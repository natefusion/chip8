(defun wrap (line)
  (case (char line 0)
    (#\( line)
    (#\. (nsubstitute #\  #\. line :test #'char=))
    (otherwise (concatenate 'string "(" line ")"))))

(defun c8-replace (ch)
  (case ch
    (#\, ")(")
    (#\; "\\;")
    (#\: "\\:")
    (#\| "|\\||")
    (#\[ "(")
    (#\] ")")
    (otherwise (string ch))))

(defun make-sexp (line)
  (wrap (apply #'concatenate 'string
               (map 'list #'c8-replace line))))

(defun remove-comment (line)
  (subseq line 0 (position #\; line :test #'char=)))

(defun trim (lines)
  (loop :for l :in lines
        :for trimmed = (remove-comment (string-trim " " l))
        :unless (uiop:emptyp trimmed)
          :collect trimmed))

(defun clean (input)
  (apply #'concatenate 'string
         (mapcar #'make-sexp (trim input))))

(defun v-reg? (exp)
  (and (listp exp) (eq (first exp) 'V)))

(defun strip-ins-args (args)
  (mapcar (lambda (x) (if (v-reg? x) (second x) x))
          (remove-if (lambda (x) (assoc x +BUILTIN-VALUES+)) args)))

(defun c8-type (exp)
  (cond
    ((numberp exp) 'N)
    ((v-reg? exp) 'V)
    ((assoc exp +BUILTIN-VALUES+) exp)
    (t nil)))

(defun get-ins-shell (args alist)
  (cdr (assoc (mapcar #'c8-type args) alist :test #'equal)))

(defun to-bytes (num)
  (labels ((b (x) (list* (logand x #xFF)
                         (when (> x #xFF) (to-bytes (ash x -8))))))
    (reverse (b num))))

(defun combine-op (shell args)
  (loop for byte in shell
        append (to-bytes
                 (case byte
                   ((x nnn) (first args))
                   (kk (first (last args)))
                   (y (second args))
                   (n (third args))
                   (otherwise byte)))))

(defun emit-op (shell)
  (loop for byte in shell
        for shift in (case (length shell) (2 '(12 0)) (3 '(12 8 0)) (4 '(12 8 4 0)))
        with op = 0
        do (setf op (logior op (ash byte shift)))
        finally (return (list (ash (logand op #xFF00) -8)
                              (logand op #xFF)))))

(defmacro make-instruction (&body alist)
  `(lambda (&rest args)
     (emit-op (combine-op (get-ins-shell args ',alist) (strip-ins-args args)))))

(defparameter +INSTRUCTIONS+
  `((EQ    . ,(make-instruction
                ((V V)   9 X Y 0)
                ((V N)   4 X KK)
                ((V KEY) #xE X #xA 1)))
    
    (NEQ   . ,(make-instruction
                ((V KEY) #xE X 9 #xE)
                ((V V)   5 X Y 0)
                ((V N)   3 X KK)))
    
    (SET   . ,(make-instruction
                ((V N)   6 X KK)
                ((V V)   8 X Y 0)
                ((I N)   #xA NNN)
                ((V DT)  #xF X 0 7)
                ((DT V)  #xF X 1 5)
                ((V ST)  #xF X 1 8)
                ((I V)   #xF X 2 9)
                ((V KEY) #xF X 0 #xA)))
    
    (ADD   . ,(make-instruction
                ((V N) 7 X KK)
                ((V V) 8 X Y 4)
                ((I V) #xF X 1 #xE)))
    
    (OR    . ,(make-instruction ((V V) 8 X Y 1)))
    (AND   . ,(make-instruction ((V V) 8 X Y 2)))
    (XOR   . ,(make-instruction ((V V) 8 X Y 3)))
    (SUB   . ,(make-instruction ((V V) 8 X Y 5)))
    (SHR   . ,(make-instruction ((V V) 8 X Y 6)))
    (SUBN  . ,(make-instruction ((V V) 8 X Y 7)))
    (SHL   . ,(make-instruction ((V V) 8 X Y #xE)))
    (RAND  . ,(make-instruction ((V N) #xC X KK)))
    (DRAW  . ,(make-instruction ((V V N) #xD X Y N)))
    (BCD   . ,(make-instruction ((V) #xF X 3 3)))
    (WRITE . ,(make-instruction ((V) #xF X 5 5)))
    (READ  . ,(make-instruction ((V) #xF X 6 5)))
    (CLEAR . ,(make-instruction (() 0 0 #xE 0)))
    (RET   . ,(make-instruction (() 0 0 #xE #xE)))
    (CALL  . ,(make-instruction ((N) 2 NNN)))
    (JUMP  . ,(make-instruction ((N) 1 NNN)))
    (JUMP0 . ,(make-instruction ((N) #xB NNN)))))

(defstruct macro (calls 0) parameters body)

(defun mk-macro (parameters body)
  (make-macro :parameters (list* 'calls parameters) :body body))

(defparameter +BUILTIN-MACROS+
  `((GT . ,(mk-macro '(x y)
                     '((set vf x)
                       (sub vf x)
                       (eq vf 0))))
    
    (GE . ,(mk-macro '(x y)
                     '((set vf y)
                       (subn vf x)
                       (neq vf 0))))
    
    (LT . ,(mk-macro '(x y)
                     '((set vf y)
                       (subn vf x)
                       (eq vf 0))))
    
    (LE . ,(mk-macro '(x y)
                     '((set vf y)
                       (sub vf x)
                       (neq vf 0))))))

(defparameter +BUILTIN-VALUES+
  `((V0  V #x0)
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
    (I   . I)
    (KEY-1 . #x1)
    (KEY-2 . #x2)
    (KEY-3 . #x3)
    (KEY-4 . #xC)
    (KEY-Q . #x4)
    (KEY-W . #x5)
    (KEY-E . #x6)
    (KEY-R . #xD)
    (KEY-A . #x7)
    (KEY-S . #x8)
    (KEY-D . #x9)
    (KEY-F . #xE)
    (KEY-Z . #xA)
    (KEY-X . #x0)
    (KEY-C . #xB)
    (KEY-V . #xF)
    (PI . ,PI)
    (E  . ,(exp 1))))

(defparameter +MAX-SIZE+ #x1000)
(defparameter +START+ #x200)
(defparameter +OFFSET+ 2)

(defun parse (cleaned)
  (eval (read-from-string (concatenate 'string "'(" cleaned ")"))))

(defmacro if-let (spec then &optional else)
  `(let (,spec) (if ,(car spec) ,then ,else)))

(defstruct env
  (output (make-array +MAX-SIZE+ :element-type '(unsigned-byte 8) :fill-pointer 0))
  (pc (+ +START+ +OFFSET+))
  (using-main? t)
  (jump-to-main nil)
  (has-main? nil)
  (initial-step-only? nil)
  values
  labels
  (macros (copy-alist +BUILTIN-MACROS+)))

(defvar *scope* nil)

(defun c8-eval-args-0 (env args)
  (loop for arg in args collect (c8-eval-arg-0 env arg)))

(defun c8-eval-arg-0 (env arg)
  (if (listp arg)
      (list* (first arg) (c8-eval-args-0 env (cdr arg)))
      (let ((val (cdr (assoc arg (env-values env))))
            (scope (cdr (assoc arg *scope*))))
        (cond (scope scope)
              (val val)
              (t arg)))))

(defun c8-check-main-0 (env name)
  (with-slots (pc using-main? jump-to-main has-main?) env
    (when (and using-main? (eq name 'main))
      (setf has-main? t)
      (if (= (+ +START+ +OFFSET+) pc)
          (setf pc +START+)
          (setf jump-to-main pc)))))

(defun c8-eval-label-0 (env name &optional numbers)
  (when (null name) (error "Label not given a name"))
  (when (or (assoc name (env-labels env))
            (assoc name (env-values env)))
    (error "Redefinition of ~a" name))
  (c8-check-main-0 env name)
  (push (cons name (env-pc env)) (env-labels env))
  (when numbers (c8-eval-include-0 env numbers)))

(defun c8-eval-def-0 (env name value)
  (when (null value) (error "'def ~a' was not initialized" name))
  (when (or (assoc name (env-values env))
            (assoc name (env-labels env)))
    (error "Redefinition of ~a" name))
  (push (cons name (c8-eval-arg-0 env value)) (env-values env))
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
         (setf (first test)
               (case (first test)
                 (eq 'neq)
                 (neq 'eq)
                 (gt 'le)
                 (ge 'lt)
                 (lt 'ge)
                 (le 'gt)
                 (otherwise (error "Test for if statement must be eq, neq, gt, ge, lt, le"))))

         ;; Evaluate the jump instructions before anything else
         ;; this will ensure the program counter is correct
         (let ((jump-else (c8-eval-form-0 env '(jump 0)))
               (jump-end  (when else (c8-eval-form-0 env '(jump 0)))))

           (setf test (c8-eval-form-0 env test)
                 then (c8-eval-0 env (rest then))
                 (cadar jump-else) (env-pc env)
                 else (c8-eval-0 env (rest else)))
           (when jump-end (setf (cadar jump-end) (env-pc env)))
           (append test jump-else then jump-end else)))
        
        (t (let* ((test (c8-eval-form-0 env test))
                  (then (c8-eval-form-0 env then))
                  (else (when else (c8-eval-form-0 env else)))
                  (statement (append test then else)))

             (when (> (length statement) 3)
               (error "If statements w/out then/else can only have two instructions. Here is yours: ~& (if ~a ~a ~a)" test then else))
             statement))))

(defun c8-eval-include-0 (env numbers)
  (incf (env-pc env) (length numbers))
  (list (list* 'include (c8-eval-args-0 env numbers))))

(defun c8-eval-macro-0 (env form)
  (let ((name (second form))
        (parameters (third form))
        (body (cdddr form)))
    (when (assoc name (env-macros env)) (error "Macro already defined ~a" form))
    (when (assoc name +INSTRUCTIONS+) (error "Cannot redefine instruction: ~a" name))
    (push (cons name (mk-macro parameters body)) (env-macros env))
    nil))

(defun c8-macroexpand-0 (env macro args)
  (let ((*scope* (append (pairlis (macro-parameters macro) args) *scope*)))
    (c8-eval-0 env (macro-body macro))))

(defun c8-apply-0 (env app args)
  (let ((ins (cdr (assoc app +INSTRUCTIONS+)))
        (mac (cdr (assoc app (env-macros env))))
        (args (c8-eval-args-0 env args)))
    (cond (ins (incf (env-pc env) 2)
               (list (list* (if (env-initial-step-only? env) app ins) args)))
          (mac (incf (macro-calls mac))
               (c8-macroexpand-0 env mac (list* (macro-calls mac) args)))
          (t (error "Unknown application (~a) in: ~a ~a" app app args)))))

(defun c8-insert-main-0 (env forms)
  (with-slots (using-main? jump-to-main has-main?) env
    (cond ((not using-main?) forms)
          (jump-to-main (append (c8-eval-form-0 env `(JUMP ,jump-to-main)) forms))
          (has-main? forms)
          (t (error "Could not find main label")))))

(defun c8-eval-form-0 (env form)
  (if (listp form)
      (case (first form)
        (def (c8-eval-def-0 env (second form) (third form)))
        (proc (c8-eval-proc-0 env (second form) (cddr form)))
        (if (c8-eval-if-0 env (second form) (third form) (fourth form)))
        (\: (c8-eval-label-0 env (cadr form) (cddr form)))
        (loop (c8-eval-loop-0 env (rest form)))
        (include (c8-eval-include-0 env (rest form)))
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
        collect (c8-eval-arg-1 env arg)))

(defmacro bool (expression) `(if ,expression 1 0))

(defun c8-eval-arg-1 (env arg)
  (cond ((numberp arg) arg)
        ((listp arg)
         (let* ((rest (c8-eval-args-1 env (rest arg)))
                (x (first rest))
                (y (second rest)))
           (case (first arg)
             (&  (logand x y))
             (\| (logior x y))
             (^  (logxor x y))
             (<< (ash x y))
             (>> (ash x (- y)))
             (+  (+ x y))
             (-  (- x y))
             (*  (* x y))
             (/  (/ x y))
             (%  (mod x y))
             (pow (expt x y))
             (min (min x y))
             (max (max x y))
             (< (bool (< x y)))
             (<= (bool (<= x y)))
             (> (bool (> x y)))
             (>= (bool (>= x y)))
             (= (bool (= x y)))
             (/= (bool (/= x y)))
             (@  (aref (env-output env) (- x +START+)))
             (~  (lognot x))
             (!  (bool (zerop x)))
             (sin (sin x))
             (cos (cos x))
             (tan (tan x))
             (exp (exp x))
             (log (log x))
             (abs (abs x))
             (sqrt (sqrt x))
             (sign (signum x))
             (ceil (ceiling x))
             (floor (floor x))
             (otherwise (error "Invalid application: ~a" arg)))))
        (t (let ((label (cdr (assoc arg (env-labels env))))
                 (val (cdr (assoc arg +BUILTIN-VALUES+)))
                 (pc (eq arg 'pc)))
             (cond (val val)
                   (label label)
                   (pc (+ +START+ (length (env-output env))))
                   (t (error "Unknown argument: ~a" arg)))))))

(defun c8-eval-include-1 (env numbers)
  (loop for n in numbers
        collect (logand (truncate (c8-eval-arg-1 env n)) #xFF)))

(defun c8-eval-program-1 (env forms)
  (dolist (form forms (env-output env))
    (dolist (number (c8-eval-form-1 env form))
      (vector-push number (env-output env)))))

(defun c8-eval-form-1 (env form)
  (case (first form)
    (include (c8-eval-include-1 env (rest form)))
    (otherwise (apply (first form) (c8-eval-args-1 env (rest form))))))

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
