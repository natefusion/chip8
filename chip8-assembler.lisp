(defmacro if-let (spec then &optional else)
  `(let (,spec) (if ,(car spec) ,then ,else)))

(defun wrap (line)
  (case (char line 0)
    (#\( line)
    (#\. (nsubstitute #\  #\. line :end 1 :test #'char=))
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

(defun parse (filename)
  (with-open-file (f filename)
    (loop for line = (read-line f nil)
          for trimmed = (remove-comment (string-trim " " line))
          while line
          unless (uiop:emptyp trimmed)
            collect (make-sexp trimmed) into final
          finally (return (read-from-string (apply #'concatenate 'string
                                                   (append '("(") final '(")"))))))))

(defmacro match (pattern &body clauses)
  `(cond ,@(dolist (clause clauses clauses)
             (setf (car clause)
                   (flet ((ekual (x y) (or (equal x y) (equal x '_))))
                     (if (listp (car clause))
                         `(when (eql (list-length ',(car clause)) (list-length ,pattern))
                            (every ,#'ekual ',(car clause) ,pattern))
                         `(funcall ,#'ekual ',(car clause) ,pattern)))))))

(defun chop (number size &optional (pos 0))
  (ldb (byte size pos) number))

(defparameter +BUILTIN-VALUES+
  `((KEY-1 . #x1)
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

(defparameter +START+ #x200)
(defparameter +MAX-SIZE+ (- #x1000 +START+))
(defparameter +OFFSET+ 2)
(defvar *scope* nil)

(defun instruction? (exp)
  (case exp
    ((EQ NEQ SET ADD OR AND XOR SUB
         SHR SUBN SHL RAND DRAW BCD WRITE
         READ CLEAR RET CALL JUMP JUMP0)
     t)))

(defun v-reg? (exp)
  (case exp
    (v0 0) (v1 1) (v2 2) (v3 3)
    (v4 4) (v5 5) (v6 6) (v7 7)
    (v8 8) (v9 9) (va #xa) (vb #xb)
    (vc #xc) (vd #xd) (ve #xe) (vf #xf)))

(defun fake? (exp)
  (case exp ((KEY DT ST I) t)))

(defun special? (exp)
  (or (v-reg? exp) (fake? exp)))

(defstruct env
  (output (make-array +MAX-SIZE+ :element-type '(unsigned-byte 8) :fill-pointer 0))
  (pc (+ +START+ +OFFSET+))
  (using-main? t)
  (jump-to-main nil)
  (has-main? nil)
  (values (copy-alist +BUILTIN-VALUES+))
  labels
  (macros (copy-alist +BUILTIN-MACROS+)))

(declaim (ftype function c8-eval-arg-0 c8-eval-0 c8-eval-form-0))

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

(defun c8-eval-include-0 (env numbers)
  (incf (env-pc env) (length numbers))
  (list (list* 'include (c8-eval-args-0 env numbers))))

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
            (assoc name (env-values env))
            (special? name))
    (error "Redefinition of ~a" name))
  (c8-check-main-0 env name)
  (push (cons name (env-pc env)) (env-labels env))
  (when numbers (c8-eval-include-0 env numbers)))

(defun c8-eval-def-0 (env name value)
  (when (null value) (error "'def ~a' was not initialized" name))
  (when (or (assoc name (env-values env))
            (assoc name (env-labels env))
            (special? name))
    (error "Redefinition of ~a" name))
  (push (cons name (c8-eval-arg-0 env value)) (env-values env))
  nil)

(defun c8-eval-macro-0 (env form)
  (let ((name (second form))
        (parameters (third form))
        (body (cdddr form)))
    (when (assoc name (env-macros env)) (error "Macro already defined ~a" form))
    (when (instruction? name) (error "Cannot redefine instruction ~a" name))
    (when (find-if #'special? parameters) (error "Special variables cannot be shadowed"))
    (push (cons name (mk-macro parameters body)) (env-macros env))
    nil))

(defun c8-macroexpand-0 (env macro args)
  ;; TODO: Remove this dynamic variable, I don't like it
  (let ((*scope* (append (pairlis (macro-parameters macro) args) *scope*)))
    (c8-eval-0 env (macro-body macro))))

(defun c8-apply-0 (env app args)
  (let ((mac (cdr (assoc app (env-macros env))))
        (args (c8-eval-args-0 env args)))
    (cond ((instruction? app)
           (incf (env-pc env) 2)
           (list (list* app args)))
          (mac (incf (macro-calls mac))
               (c8-macroexpand-0 env mac (list* (macro-calls mac) args)))
          (t (error "Unknown application (~a) in: ~a ~a" app app args)))))

(defun c8-eval-loop-0 (env body)
  (let* ((pc (env-pc env))
         (lp (c8-eval-0 env body)))
    (append lp (c8-eval-form-0 env `(JUMP, pc)))))

(defun c8-eval-proc-0 (env name body)
  (c8-eval-label-0 env name)
  (append (c8-eval-0 env body)
          (unless (eq name 'main) (c8-eval-form-0 env '(ret)))))

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

(defun c8-insert-main-0 (env forms)
  (with-slots (using-main? jump-to-main has-main?) env
    (cond ((not using-main?) forms)
          (jump-to-main (append (c8-eval-form-0 env `(JUMP ,jump-to-main)) forms))
          (has-main? forms)
          (t (error "Could not find main label")))))

(defun c8-eval-form-0 (env form)
  (if (listp form)
      (case (first form)
        ((nil))
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

(declaim (ftype function c8-eval-arg-1))

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
                 (pc (eq arg 'pc)))
             (cond (label label)
                   (pc (+ +START+ (length (env-output env))))
                   ((special? arg) arg)
                   (t (error "Unknown argument: ~a" arg)))))))

(defun c8-eval-include-1 (env numbers)
  (loop for n in numbers
        collect (logand (truncate (c8-eval-arg-1 env n)) #xFF)))

(defun strip-ins-args (args)
  (loop for x in (remove-if #'fake? args)
        collect (if-let (v (v-reg? x)) v x)))

(defun c8-type (exp)
  (cond ((numberp exp) 'N)
        ((v-reg? exp) 'V)
        ((fake? exp) exp)
        (t nil)))

(defun emit-op (&rest shell)
  (labels ((append-bytes (nums pos)
             (if (<= (length nums) 1)
                 (car nums)
                 (dpb (car nums) (byte pos pos)
                      (append-bytes (cdr nums) (- pos 4))))))
    (let ((op (append-bytes shell 12)))
      (list (chop op 8 8) (chop op 8)))))

(defun c8-eval-ins (name args)
  (let* ((sargs (strip-ins-args args))
         (s1 (first sargs))
         (s2 (second sargs))
         (s3 (third sargs))
         (types (mapcar #'c8-type args)))
    
    (match (list* name types)
      ((EQ V V)   (emit-op 9 s1 s2 0))
      ((EQ V N)   (emit-op 4 s1 s2))
      ((EQ V KEY) (emit-op #xE s1 #xA 1))
        
      ((NEQ V KEY) (emit-op #xE s1 9 #xE))
      ((NEQ V V)   (emit-op 5 s1 s2 0))
      ((NEQ V N)   (emit-op 3 s1 s2))
        
      ((SET V N)   (emit-op 6 s1 s2))
      ((SET V V)   (emit-op 8 s1 s2 0))
      ((SET I N)   (emit-op #xA s1))
      ((SET V DT)  (emit-op #xF s1 0 7))
      ((SET DT V)  (emit-op #xF s1 1 5))
      ((SET V ST)  (emit-op #xF s1 1 8))
      ((SET I V)   (emit-op #xF s1 2 9)) 
      ((SET V KEY) (emit-op #xF s1 0 #xA))
        
      ((ADD V N) (emit-op 7 s1 s2))
      ((ADD V V) (emit-op 8 s1 s2 4))
      ((ADD I V) (emit-op #xF s1 1 #xE))
        
      ((OR V V)   (emit-op 8 s1 s2 1))
      ((AND V V)  (emit-op 8 s1 s2 2))
      ((XOR V V)  (emit-op 8 s1 s2 3))
      ((SUB V V)  (emit-op 8 s1 s2 5))
      ((SHR V V)  (emit-op 8 s1 s2 6))
      ((SUBN V V) (emit-op 8 s1 s2 7))
      ((SHL V V)  (emit-op 8 s1 s2 #xE))
        
      ((RAND V N)   (emit-op #xC s1 s2))
      ((DRAW V V N) (emit-op #xD s1 s2 s3))
      ((BCD V)      (emit-op #xF s1 3 3))
      ((WRITE V)    (emit-op #xF s1 5 5))
      ((READ V)     (emit-op #xF s1 6 5))
      ((CLEAR)      (emit-op 0 0 #xE 0))
      ((RET)        (emit-op 0 0 #xE #xE))
      ((CALL N)     (emit-op 2 s1))
      ((JUMP N)     (emit-op 1 s1))
      ((JUMP0 N)    (emit-op #xB s1))
      (_ (error "Invalid instruction: ~a ~a" name args)))))

(defun c8-eval-form-1 (env form)
  (case (first form)
    (include (c8-eval-include-1 env (rest form)))
    (otherwise (c8-eval-ins (first form) (c8-eval-args-1 env (rest form))))))

(defun c8-eval-program-1 (env forms)
  (with-slots (output) env
    (dolist (form forms output)
      (dolist (number (c8-eval-form-1 env form))
        (when (>= (fill-pointer output) (array-total-size output)) 
          (error "Your program is too large!"))
        (vector-push number output)))))

(defun c8-compile (filename &key (using-main? t) initial-step-only?)
  (let ((parsed (parse filename))
        (env (make-env :using-main? using-main?)))
    (if initial-step-only?
        (c8-eval-program-0 env parsed)
        (c8-eval-program-1 env (c8-eval-program-0 env parsed)))))

(defun c8-write (bytes filename)
  (with-open-file (f filename
                     :direction :output
                     :if-exists :supersede
                     :if-does-not-exist :create
                     :element-type 'unsigned-byte)
    (map 'nil (lambda (x) (write-byte x f)) bytes)))
