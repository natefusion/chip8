(defun wrap (line)
  (if (char= #\( (char line 0))
      line
      (concatenate 'string "(" line ")")))

(defun make-sexp (line)
  (apply #'concatenate 'string
         (map 'list
              (lambda (ch)
                (case ch
                  (#\, ")(")
                  (#\; "\\;")
                  (#\: "\\:")
                  (#\| "|\\||")
                  (otherwise (string ch))))
              (wrap line))))

(defun trim (lines)
  (loop :for l :in lines
        :for trimmed = (string-trim " " l)
        :unless (uiop:emptyp trimmed)
          :collect trimmed))

(defun clean (input)
  (apply #'concatenate 'string
         (mapcar #'make-sexp (trim input))))

(defun c8-eval-v (exp)
  (if (when (listp exp) (eq (first exp) 'V))
      (second exp)
      exp))

(defun builtin-val? (exp)
  (assoc exp +BUILTIN-VALUES+))

(defun c8-type (exp)
  (cond
    ((and (listp exp) (eq (first exp) 'V)) 'V)
    ((builtin-val? exp) exp)
    ((numberp exp) 'N)
    (t nil)))

(defun to-bytes (num)
  (loop :for n :across (format nil "~x" num)
        :collect (parse-integer (string n) :radix 16)))

(defun combine-op (shell args)
  (loop :for x :in shell
        :append (to-bytes
                 (case x
                   ((x nnn) (first args))
                   (kk (first (last args)))
                   (y (second args))
                   (n (third args))
                   (otherwise x)))))

(defun emit-op (shell)
  (loop :for byte :in shell
        :for shift :in (case (length shell) (2 '(12 0)) (3 '(12 8 0)) (4 '(12 8 4 0)))
        :with op := 0
        :do (setf op (logior op (ash byte shift)))
        :finally (return (list (ash (logand op #xFF00) -8)
                               (logand op #xFF)))))

(defmacro make-instruction (&body alist)
  `(lambda (&rest args)
     (emit-op (combine-op (cdr (assoc (mapcar #'c8-type args) ',alist :test #'equal))
                          (remove-if #'builtin-val? (mapcar #'c8-eval-v args))))))

(defparameter +INSTRUCTIONS+
  `((EQ    . ,(make-instruction
                ((V V)   9 X Y 0)
                ((V N)   4 X KK)
                ((V KEY) E X A 1)))
    
    (NEQ   . ,(make-instruction
                ((V KEY) E X 9 E)
                ((V V)   5 X Y 0)
                ((V N)   3 X KK)))
    
    (SET   . ,(make-instruction
                ((V N)   6 X KK)
                ((V V)   8 X Y 0)
                ((I N)   A NNN)
                ((V DT)  F X 0 7)
                ((DT V)  F X 1 5)
                ((V ST)  F X 1 8)
                ((I V)   F X 2 9)
                ((V KEY) F X 0 A)))
    
    (ADD   . ,(make-instruction
                ((V N) 7 X KK)
                ((V V) 8 X Y 4)
                ((I V) F X 1 E)))
    
    (OR    . ,(make-instruction ((V V) 8 X Y 1)))
    (AND   . ,(make-instruction ((V V) 8 X Y 2)))
    (XOR   . ,(make-instruction ((V V) 8 X Y 3)))
    (SUB   . ,(make-instruction ((V V) 8 X Y 5)))
    (SHR   . ,(make-instruction ((V V) 8 X Y 6)))
    (SUBN  . ,(make-instruction ((V V) 8 X Y 7)))
    (SHL   . ,(make-instruction ((V V) 8 X Y E)))
    (RAND  . ,(make-instruction ((V N) C X KK)))
    (DRAW  . ,(make-instruction ((V V N) D X Y N)))
    (BCD   . ,(make-instruction ((V) F X 3 3)))
    (WRITE . ,(make-instruction ((V) F X 5 5)))
    (READ  . ,(make-instruction ((V) F X 6 5)))
    (CLEAR . ,(make-instruction (() 0 0 E 0)))
    (RET   . ,(make-instruction (() 0 0 E E)))
    (CALL  . ,(make-instruction ((N) 2 NNN)))
    (JUMP  . ,(make-instruction ((N) 1 NNN)))
    (JUMP0 . ,(make-instruction ((N) B NNN)))))

(defparameter +BUILTIN-VALUES+
  '((V0  V #x0)
    (V1  V #x1)
    (V2  V #x2)
    (V3  V #x3)
    (V4  V #x4)
    (V5  V #x5)
    (V6  V #x6)
    (V7  V #x7)
    (V8  V #x8)
    (V9  V #x9)
    (VA  V #xA)
    (VB  V #xB)
    (VC  V #xC)
    (VD  V #xD)
    (VE  V #xE)
    (VF  V #xF)
    (KEY . KEY)
    (DT  . DT)
    (ST  . ST)
    (I   . I)))

(defparameter +MATH+ '())

(defparameter +MAX-SIZE+ #x1000)
(defparameter +START+ #x200)
(defparameter +OFFSET+ 2)

(defun parse (cleaned)
  (eval (read-from-string (concatenate 'string "'(" cleaned ")"))))

(defmacro if-let (spec then &optional else)
  `(let (,spec) (if ,(car spec) ,then ,else)))

(defstruct env
  (pc (+ +START+ +OFFSET+))
  (using-main? t)
  (initial-step-only? nil)
  (jump-to-main nil)
  (values (copy-alist +BUILTIN-VALUES+))
  macros)

(defstruct (macro (:constructor mk-macro (parameters body)))
  (calls 0) parameters body)

(defvar *scope* nil)

(defun c8-check-main-0 (env name)
  (with-slots (pc using-main? jump-to-main) env
    (when (and using-main? (eq name 'main))
      (if (= (+ +START+ +OFFSET+) pc)
          (setf pc +START+)
          (setf jump-to-main pc)))))

(defun c8-eval-label-0 (env name)
  (when (null name) (error "Label not given a name"))
  (when (assoc name (env-values env)) (error "Redefinition of ~a" name))
  (c8-check-main-0 env name)
  (push (cons name (env-pc env)) (env-values env))
  nil)

(defun c8-eval-proc-0 (env name body)
  (c8-eval-label-0 env name)
  (append (c8-eval-0 env body)
          (unless (eq name 'main) (c8-eval-form-0 env '(ret)))))

(defun c8-eval-loop-0 (env body)
  (let* ((pc (env-pc env))
         (lp (c8-eval-0 env body)))
    (append lp (c8-eval-form-0 env `(JUMP ,pc)))))

(defun c8-eval-if-0 (env test then else)
  (cond ((eq (first then) 'then)
         (case (first test)
           (eq (setf (first test) 'neq))
           (neq (setf (first test) 'eq))
           (otherwise (error "Test for if statement must be either 'eq' or 'neq'")))

         ;; Evaluate the jump instructions before anything else
         ;; this will ensure the program counter is correct
         (let ((jump-else (c8-eval-form-0 env '(jump 0)))
               (jump-end  (when else (c8-eval-form-0 env '(jump 0)))))

           (setf test (c8-eval-form-0 env test)
                 then (c8-eval-0 env (rest then))
                 (cadar jump-else) (env-pc env)
                 else (c8-eval-0 env (cdar else)))
           (when jump-end (setf (cadar jump-end) (env-pc env)))
           (append test jump-else then jump-end else)))
        
        ((> (length else) 1)
         (error "If statements w/out then and else can only contain two instructions:~%(if ~a ~a ~a)"
                test then else))
        (t (c8-eval-0 env (list* test then else)))))

(defun c8-eval-include-0 (env form)
  (incf (env-pc env) (length (rest form)))
  (list form))

(defun c8-eval-macro-0 (env form)
  (let ((name (second form))
        (parameters (list* 'calls (third form)))
        (body (cdddr form)))
    (when (assoc name (env-macros env)) (error "Macro already defined ~a" form))
    (push (cons name (mk-macro parameters body)) (env-macros env))
    nil))

(defun c8-macroexpand-0 (env macro args)
  `((macro ,(pairlis (macro-parameters macro) args)
     ,@(c8-eval-0 env (macro-body macro)))))

(defun c8-apply-0 (env app args)
  (let ((ins (cdr (assoc app +INSTRUCTIONS+)))
        (mac (cdr (assoc app (env-macros env)))))
    (cond (ins (incf (env-pc env) 2)
               (list (list* (if (env-initial-step-only? env) app ins) args)))
          (mac (incf (macro-calls mac))
               (c8-macroexpand-0 env mac (list* (macro-calls mac) args)))
          (t (error "Unknown application (~a) in: ~a ~a" app app args)))))

(defun c8-insert-main-0 (env forms)
  (with-slots (using-main? jump-to-main) env
    (cond ((not using-main?) forms)
          (jump-to-main (append (c8-eval-form-0 env `(JUMP ,jump-to-main)) forms))
          ((assoc 'main (env-values env)) forms)
          (t (error "Could not find main label")))))

(defun c8-eval-form-0 (env form)
  (if (listp form)
      (case (first form)
        (\; nil)
        (def (list form))
        (proc (c8-eval-proc-0 env (second form) (cddr form)))
        (if (c8-eval-if-0 env (second form) (third form) (cdddr form)))
        (\: (c8-eval-label-0 env (cadr form)))
        (loop (c8-eval-loop-0 env (rest form)))
        (include (c8-eval-include-0 env form))
        (macro (c8-eval-macro-0 env form))
        (otherwise (c8-apply-0 env (first form) (rest form))))
      (error "'~a' is not a valid form" form)))

(defun c8-eval-0 (env forms)
  (loop for form in forms
        append (c8-eval-form-0 env form)))

(defun c8-eval-program-0 (env forms)
  (c8-insert-main-0 env (c8-eval-0 env forms)))

(defun c8-eval-args-1 (env args)
  (loop for arg in args
        collect
        (if (listp arg)
            (c8-apply-math-1 env (first arg) (rest arg))
            (c8-eval-val-1 env arg))))

(defun c8-apply-math-1 (env app args)
  (if-let (maff (cdr (assoc app +MATH+)))
    (apply maff (c8-eval-args-1 env args))
    (error "not maff: ~a ~a" app args)))

(defun c8-eval-val-1 (env arg)
  (if (numberp arg)
      arg
      (let ((val (cdr (assoc arg (env-values env))))
            (scope (cdr (assoc arg *scope*))))
        (cond (scope scope)
              (val val)
              (t (error "Unknown argument: ~a" arg))))))

(defun c8-eval-def-1 (env name value)
  (when (null value) (error "'def ~a' was not initialized" name))
  (when (assoc name (env-values env)) (error "Redefinition of ~a" name))
  (push (cons name (c8-eval-val-1 env value)) (env-values env))
  nil)

(defun c8-eval-include-1 (env numbers)
  (c8-eval-args-1 env numbers))

(defun c8-eval-macro-1 (env *scope* body)
  ;; dynamically scoped variable used for scoping in the language
  (dolist (x *scope*) (setf (cdr x) (c8-eval-val-1 env (cdr x))))
  (c8-eval-1 env body))

(defun c8-eval-1 (env forms)
  (loop for form in forms 
        append (c8-eval-form-1 env form)))

(defun c8-eval-form-1 (env form)
  (case (first form)
    (def (c8-eval-def-1 env (second form) (third form)))
    (include (c8-eval-include-1 env (rest form)))
    (macro (c8-eval-macro-1 env (second form) (cddr form)))
    (otherwise (apply (first form) (c8-eval-args-1 env (rest form))))))

(defun c8-eval-program-1 (env forms)
  (if-let (f (c8-eval-1 env forms))
    f
    (error "Compilation failed: Your program is too big")))

(defun c8-compile (filename &key (using-main? t) initial-step-only?)
  (let ((parsed (parse (clean (uiop:read-file-lines filename))))
        (env (make-env :using-main? using-main? :initial-step-only? initial-step-only?)))
    (if initial-step-only?
        (c8-eval-program-0 env parsed)
        (c8-eval-program-1 env (c8-eval-program-0 env parsed)))))

(defun chip8-write (bytes filename)
  (with-open-file (f filename
                     :direction :output
                     :if-exists :supersede
                     :if-does-not-exist :create
                     :element-type 'unsigned-byte)
    (mapcar (lambda (x) (write-byte x f)) bytes)))

