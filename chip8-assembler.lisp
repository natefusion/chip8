(defmacro if-let (spec then &optional else)
  `(let (,spec) (if ,(car spec) ,then ,else)))

(defun c8-replace (ch)
  (case ch
    (#\, ")(")
    (#\; "\\;")
    (#\: "\\:")
    (#\| "|\\||")
    (#\[ "(")
    (#\] ")")
    (t (string ch))))

(defun make-sexp (line)
  (let ((line (apply #'concatenate 'string
                     (map 'list #'c8-replace line))))
    
    (case (char line 0)
      (#\( line)
      (#\. (substitute #\  #\. line :end 1 :test #'char=))
      (t (concatenate 'string "(" line ")")))))

(defun remove-comment (line)
  (subseq line 0 (position #\; line :test #'char=)))

(defun parse (filename)
  (with-open-file (f filename)
    (loop for line = (read-line f nil)
          for trimmed = (string-trim " " (remove-comment line))
          while line
          unless (uiop:emptyp trimmed)
            collect (make-sexp trimmed) into final
          finally (return (read-from-string (apply #'concatenate 'string
                                                   (append '("(") final '(")"))))))))

(defmacro match (pattern &body clauses)
  `(cond ,@(dolist (clause clauses clauses)
             (setf (car clause)
                   (flet ((ekual (x y) (or (equal x y) (equal x '_))))
                     `(if (and (listp ,pattern) (listp ',(car clause)))
                          (when (eql (list-length ',(car clause)) (list-length ,pattern))
                            (every ,#'ekual ',(car clause) ,pattern))
                          (funcall ,#'ekual ',(car clause) ,pattern)))))))

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
                     '((set vf y)
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
(defparameter +MAX-SIZE+ (- #x10000 +START+))
(defparameter +OFFSET+ 2)

(defun instruction? (exp)
  (case exp
    ((EQ NEQ SET ADD OR AND XOR SUB
         SHR SUBN SHL DRAW BCD WRITE
         READ CLEAR RET CALL JUMP JUMP0
         EXIT LORES HIRES READ-FLAGS WRITE-FLAGS
         SCROLL-DOWN SCROLL-RIGHT SCROLL-LEFT
         SCROLL-UP PLANE AUDIO)
     t)))

(defun builtin-func? (exp)
  (case exp
    ((mut def proc if then else \: loop
          while include macro let target break)
     t)))

(defun special-func? (exp)
  (or (instruction? exp) (builtin-func? exp)))

(defun v-reg? (exp)
  (case exp
    (v0 0) (v1 1) (v2 2) (v3 3)
    (v4 4) (v5 5) (v6 6) (v7 7)
    (v8 8) (v9 9) (va #xa) (vb #xb)
    (vc #xc) (vd #xd) (ve #xe) (vf #xf)))

(defun fake? (exp)
  (case exp ((KEY DT ST I HEX BIGHEX LONG RAND) t)))

(defun special-val? (exp)
  (or (v-reg? exp) (fake? exp)
      (eq exp 'pc)))

(defstruct env
  (output (make-array +MAX-SIZE+ :element-type '(unsigned-byte 8) :fill-pointer 0))
  (pc (+ +START+ +OFFSET+))
  main-label
  (target 'chip8)
  context
  local-values
  (values (copy-alist +BUILTIN-VALUES+))
  mutables
  labels
  local-macros
  (macros (copy-alist +BUILTIN-MACROS+)))

(defun assoc-local (item alists)
  (loop for scope in alists
        for x = (assoc item scope)
        when x return x))

(declaim (ftype function c8-eval-arg-0 c8-eval-0 c8-eval-form-0))

(defun c8-eval-arg-0 (env arg)
  (if (listp arg)
      (list* (first arg) (loop for a in (rest arg) collect (c8-eval-arg-0 env a)))
      (let ((local (cdr (assoc-local arg (env-local-values env))))
            (val (cdr (assoc arg (env-values env))))
            (mut (cdr (assoc arg (env-mutables env)))))
        (cond (local local)
              (mut mut)
              (val val)
              ((eq arg 'pc) (env-pc env))
              (t arg)))))

(defun c8-eval-include-0 (env numbers)
  (loop for n in numbers
        collect (c8-eval-arg-0 env n) into f
        do (incf (env-pc env))
        finally (return (list `(include ,@f)))))

(defun c8-check-main-0 (env name)
  (with-slots (pc main-label) env
    (when (eq name 'main)
      (when (= pc (+ +START+ +OFFSET+))
        (setf pc +START+))
      (setf main-label pc))))

(defun c8-eval-label-0 (env name &optional numbers)
  (when (null name) (error "Label not given a name"))
  (when (or (assoc name (env-labels env))
            (assoc name (env-mutables env))
            (assoc name (env-values env))
            (special-val? name))
    (error "Redefinition of ~a" name))
  (c8-check-main-0 env name)
  (push (cons name (env-pc env)) (env-labels env))
  (when numbers (c8-eval-include-0 env numbers)))

(defun c8-eval-mut-0 (env name value)
  (when (null value) (error "'def ~a' was not initialized" name))
  (when (or (assoc name (env-values env))
            (assoc name (env-labels env))
            (special-val? name))
    (error "Redefinition of ~a" name))
  
  (if (assoc name (env-mutables env))
      (setf (cdr (assoc name (env-mutables env))) (c8-eval-arg-0 env value))
      (push (cons name (c8-eval-arg-0 env value)) (env-mutables env)))
  nil)

(defun c8-eval-def-0 (env name value)
  (when (null value) (error "'def ~a' was not initialized" name))
  (when (or (assoc name (env-values env))
            (assoc name (env-mutables env))
            (assoc name (env-labels env))
            (special-val? name))
    (error "Redefinition of ~a" name))
  (push (cons name (c8-eval-arg-0 env value)) (env-values env))
  nil)

(defun c8-eval-macro-0 (env form)
  (let ((name (second form))
        (parameters (third form))
        (body (cdddr form)))
    (when (assoc name (env-macros env)) (error "Macro already defined ~a" form))
    (when (special-func? name) (error "Cannot redefine special func ~a" name))
    (when (find-if #'special-val? parameters) (error "Special variables cannot be shadowed"))
    (push (cons name (mk-macro parameters body)) (env-macros env))
    nil))

(defun c8-eval-let-0 (env form)
  (when (oddp (length (second form)))
    (error "Odd number of items in let form: ~a" (second form)))
  (loop for x = (second form) then (cddr x)
        while x
        collect (car x) into keys
        collect (c8-eval-arg-0 env (cadr x)) into data
        finally (push (pairlis keys data) (env-local-values env))
                (return (prog1 (c8-eval-0 env (cddr form))
                          (pop (env-local-values env))))))

(defun c8-macroexpand-0 (env name macro args)
  (loop for key in (macro-parameters macro)
        for datum in args
        if (listp key)
          collect (cons (first key) datum) into local-macros
        else
          collect (cons key (c8-eval-arg-0 env datum)) into local-values
        finally (push name (env-context env))
                (push local-macros (env-local-macros env))
                (push local-values (env-local-values env))
                (return (prog1 (c8-eval-0 env (macro-body macro))
                          (pop (env-context env))
                          (pop (env-local-macros env))
                          (pop (env-local-values env))))))

(defun c8-apply-0 (env app args)
  (let ((local (cdr (assoc-local app (env-local-macros env))))
        (mac (cdr (assoc app (env-macros env)))))
    (cond (local (c8-eval-form-0 env (list* local args)))
          ((instruction? app)
           (incf (env-pc env) (if (find 'long (list* app args)) 4 2))
           (list (list* app (loop for arg in args collect (c8-eval-arg-0 env arg)))))
          (mac (prog2 (when (eq app (first (env-context env)))
                        (error "Tried to call ~a in context ~a. Recursion is not allowed"
                               app (first (env-context env))))
                   (c8-macroexpand-0 env app mac (list* (macro-calls mac) args))
                 (incf (macro-calls mac))))
          (t (error "Unknown application (~a) in: ~a ~a" app app args)))))

(defun flip-test (test)
  (case test
    (eq 'neq) (neq 'eq) (gt 'le) (ge 'lt) (lt 'ge) (le 'gt)
    (t (error "Test must be eq, neq, gt, ge, lt, le"))))

(defun c8-eval-loop-0 (env body)
  (let* ((pc (env-pc env))
         (lp (append (c8-with-forms-eval-0 (f body append)
                       (case (first f)
                         (while
                          (incf (env-pc env) 2)                 ;; make room for jump
                          (append (c8-eval-form-0 env (list (flip-test (second f)) (third f) (fourth f)))
                                  '((break jump-to-end-loop)))) ;; placeholder for jump
                         (t (c8-eval-form-0 env f))))
                     (c8-eval-form-0 env `(JUMP ,pc)))))

    (c8-with-forms-eval-0 (f lp collect)
      (if (equal '(break jump-to-end-loop) f)
          `(JUMP ,(env-pc env))
          f))))

(defun c8-eval-if-0 (env form)
  (let* ((test (first (c8-eval-form-0 env (list (second form) (third form) (fourth form)))))
         (test-pc (env-pc env))
         (then-pc nil)
         (else-pc nil)
         
         (body (c8-with-forms-eval-0 (f (nthcdr 4 form) append)
                 (case (first f)
                   (then
                    (when then-pc (error "Too many then statements in: ~a" form))
                    (setf then-pc (incf (env-pc env) )) ;; make room for jump
                    '((then jump-to-else-if)))          ;; placeholder for jump
                   (else
                    (when else-pc (error "Too many else statements in: ~a" form))
                    (setf else-pc (incf (env-pc env) 2)) ;; make room for jump
                    `((else jump-to-end-if)))            ;; placeholder for jump
                   (t (c8-eval-form-0 env f)))))

         (end-pc (env-pc env)))

    (if (null then-pc)
        (cond (else-pc (error "Then without else in: ~a" form))
              ((>= (length body) 3) (error "If statements without then or else cannot have more than one statement~%: ~a" form)))
        (when (> (- then-pc test-pc) 4)
          (error "There cannnot be any statements between the test and then statements in: ~a" form)))

    
    (cons (list (if then-pc (flip-test (first test)) (first test)) (second test) (third test))
            (c8-with-forms-eval-0 (f body collect)
              (match f
                ((then jump-to-else-if)
                 (if else-pc
                     `(JUMP ,else-pc)
                     `(JUMP ,end-pc)))
                ((else jump-to-end-if)
                 `(JUMP ,end-pc))
                (_ f))))))

(defun c8-eval-proc-0 (env name body)
  (c8-eval-label-0 env name)
  (append (c8-eval-0 env body)
          (unless (eq name 'main) (c8-eval-form-0 env '(ret)))))

(defun c8-insert-main-0 (env forms)
  (with-slots (main-label) env
    (cond ((= main-label +START+) forms)
          ((> main-label +START+) (append (c8-eval-form-0 env `(JUMP ,main-label)) forms))
          (t (error "Could not find main label")))))

(defun c8-eval-form-0 (env form)
  (case (first form)
    ((nil))
    (mut (c8-eval-mut-0 env (second form) (third form)))
    (def (c8-eval-def-0 env (second form) (third form)))
    (proc (c8-eval-proc-0 env (second form) (cddr form)))
    (if (c8-eval-if-0 env form))
    (\: (c8-eval-label-0 env (cadr form) (cddr form)))
    (loop (c8-eval-loop-0 env (rest form)))
    (include (c8-eval-include-0 env (rest form)))
    (macro (c8-eval-macro-0 env form))
    (let (c8-eval-let-0 env form))
    (target (setf (env-target env) (second form)) nil)
    (t (c8-apply-0 env (first form) (rest form)))))

(defmacro c8-with-forms-eval-0 ((var list action) &body body)
  `(loop for ,var in ,list
         ,action (if (listp ,var)
                 ,@body
                 (error "'~a' is not a valid form" ,var))))

(defun c8-eval-0 (env forms)
  (c8-with-forms-eval-0 (form forms append)
    (c8-eval-form-0 env form)))

(defun c8-eval-program-0 (env forms)
  (c8-insert-main-0 env (c8-eval-0 env forms)))

(declaim (ftype function c8-eval-arg-1))

(defun c8-eval-args-1 (env args)
  (loop for arg in args
        collect (c8-eval-arg-1 env arg)))

(defun c8-eval-deref-1 (array value)
  (cond ((< value +START+)
         (error (concatenate
                 'string
                 "Cannot access memory location '~A'~%"
                 "Memory references cannot be lower than '~A'")
                value +START+))
        ((>= value (+ (fill-pointer array) +START+))
         (error (concatenate
                 'string
                 "Cannot access memory location '~A'~%"
                 "Only memory addresses less than '~A', the value of the program counter~%"
                 "at the time of evaluation, can be referenced~%"
                 "~%that's too hard, cut me some slack")
                value
                (+ (fill-pointer array) +START+)))
        (t (aref array (- value +START+)))))

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
             (@  (c8-eval-deref-1 (env-output env) x))
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
             (t (error "Invalid application: ~a" arg)))))
        (t (let ((label (cdr (assoc arg (env-labels env)))))
             (cond (label label)
                   ((special-val? arg) arg)
                   (t (error "Unknown argument: ~a" arg)))))))

(defun strip-ins-args-1 (args)
  (loop for x in (remove-if #'fake? args)
        collect (if-let (v (v-reg? x)) v x)))

(defun c8-type-1 (exp)
  (cond ((numberp exp) 'N)
        ((v-reg? exp) 'V)
        ((fake? exp) exp)
        (t nil)))

(defun emit-op-1 (long &rest shell)
  (labels ((append-bytes (nums pos)
             (if (<= (length nums) 1)
                 (car nums)
                 (dpb (car nums) (byte pos pos)
                      (append-bytes (cdr nums) (- pos 4))))))
    (let ((op (append-bytes shell (if long 28 12))))
      (if long
          (list (chop op 8 24) (chop op 8 16)
                (chop op 8 8) (chop op 8))
          (list (chop op 8 8) (chop op 8))))))

(defun c8-chip8-ins-set (instruction x y n nn nnn)
  (match instruction
    ((EQ V V)   (emit-op-1 nil 9 X Y 0))
    ((EQ V N)   (emit-op-1 nil 4 X NN))
    ((EQ V KEY) (emit-op-1 nil #xE X #xA 1))
    
    ((NEQ V KEY) (emit-op-1 nil #xE X 9 #xE))
    ((NEQ V V)   (emit-op-1 nil 5 X Y 0))
    ((NEQ V N)   (emit-op-1 nil 3 X NN))
    
    ((SET V N)   (emit-op-1 nil 6 X NN))
    ((SET V V)   (emit-op-1 nil 8 X Y 0))
    ((SET I N)   (emit-op-1 nil #xA NNN))
    ((SET V DT)  (emit-op-1 nil #xF X 0 7))
    ((SET DT V)  (emit-op-1 nil #xF X 1 5))
    ((SET ST V)  (emit-op-1 nil #xF X 1 8))
    ((SET I HEX V) (emit-op-1 nil #xF X 2 9)) 
    ((SET V KEY) (emit-op-1 nil #xF X 0 #xA))
    
    ((ADD V N) (emit-op-1 nil 7 X NN))
    ((ADD V V) (emit-op-1 nil 8 X Y 4))
    ((ADD I V) (emit-op-1 nil #xF X 1 #xE))
    
    ((OR V V)   (emit-op-1 nil 8 X Y 1))
    ((AND V V)  (emit-op-1 nil 8 X Y 2))
    ((XOR V V)  (emit-op-1 nil 8 X Y 3))
    ((SUB V V)  (emit-op-1 nil 8 X Y 5))
    ((SHR V V)  (emit-op-1 nil 8 X Y 6))
    ((SUBN V V) (emit-op-1 nil 8 X Y 7))
    ((SHL V V)  (emit-op-1 nil 8 X Y #xE))
    
    ((SET V RAND N) (emit-op-1 nil #xC X NN))
    ((DRAW V V N) (emit-op-1 nil #xD X Y N))
    ((BCD V)      (emit-op-1 nil #xF X 3 3))
    ((WRITE V)    (emit-op-1 nil #xF X 5 5))
    ((READ V)     (emit-op-1 nil #xF X 6 5))
    ((CLEAR)      (emit-op-1 nil 0 0 #xE 0))
    ((RET)        (emit-op-1 nil 0 0 #xE #xE))
    ((CALL N)     (emit-op-1 nil 2 NNN))
    ((JUMP N)     (emit-op-1 nil 1 NNN))
    ((JUMP0 N)    (emit-op-1 nil #xB NNN))
    (_ (error (concatenate 'string
                           "Invalid instruction: ~a~%"
                           "Did you maybe not set a target?")
              instruction))))

(defun c8-schip-ins-set (instruction x y n nn nnn)
  (match instruction
    ;; SCHIP 1.0
    ((EXIT) (emit-op-1 nil 0 0 #xF #xD))
    ((LORES) (emit-op-1 nil 0 0 #xF #xE))
    ((HIRES) (emit-op-1 nil 0 0 #xF #xF))
    ((DRAW V V) (emit-op-1 nil #xD X Y 0))
    ((READ-FLAGS V) (emit-op-1 nil #xF X 7 5))
    ((WRITE-FLAGS V) (emit-op-1 nil #xF X 8 5))
    
    ;; SCHIP 1.1
    ((SCROLL-DOWN N) (emit-op-1 nil 0 0 #xC X))
    ((SCROLL-RIGHT) (emit-op-1 nil 0 0 #xF #xB))
    ((SCROLL-LEFT) (emit-op-1 nil 0 0 #xF #xC))
    ((SET I BIGHEX V) (emit-op-1 nil #xF X 3 0))
    (_ (c8-chip8-ins-set instruction x y n nn nnn))))

(defun c8-xo-chip-ins-set (instruction x y n nn nnn nnnn)
  (match instruction
    ((SCROLL-UP N) (emit-op-1 nil 0 0 #xD X))
    ((WRITE V V) (emit-op-1 nil 5 X Y 2))
    ((READ V V) (emit-op-1 nil 5 X Y 3))
    ((SET I LONG N) (emit-op-1 t #xF 0 0 0 NNNN))
    ((PLANE N) (emit-op-1 nil #xF X 0 1))
    ((AUDIO) (emit-op-1 nil #xF 0 0 2))
    ((SET PITCH V) (emit-op-1 nil #xF X 3 #xA))
    (_ (c8-schip-ins-set instruction x y n nn nnn))))

(defun c8-eval-ins-1 (env name args)
  (let* ((sargs (strip-ins-args-1 args))
         (nnn (first sargs))  (x   (first sargs))
         (y   (second sargs)) (nn  (second sargs))
         (n   (third sargs))
         (types (mapcar #'c8-type-1 args))
         (instruction (list* name types)))

    (case (env-target env)
      (chip8 (c8-chip8-ins-set instruction x y n nn nnn))
      (schip (c8-schip-ins-set instruction x y n nn nnn))
      (xo-chip (c8-xo-chip-ins-set instruction x y n nn nnn nnn))
      (t (error "Invalid target: ~a" (env-target env))))))

(defun c8-eval-include-1 (env numbers)
  (loop for n in numbers
        collect (chop (truncate (c8-eval-arg-1 env n)) 8)))

(defun c8-eval-form-1 (env form)
  (case (first form)
    (include (c8-eval-include-1 env (rest form)))
    (t (c8-eval-ins-1 env (first form) (c8-eval-args-1 env (rest form))))))

(defun c8-eval-program-1 (env forms)
  (let ((size (case (env-target env)
                (xo-chip (- #x10000 +START+))
                (t (- #x1000 +START+)))))
    (with-slots (output) env
      (dolist (form forms output)
        (dolist (number (c8-eval-form-1 env form))
          (when (>= (fill-pointer output) size) 
            (error "Your program is too large!"))
          (vector-push number output))))))

(defun c8-compile (filename &key initial-step-only?)
  (let ((parsed (parse filename))
        (env (make-env)))
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
