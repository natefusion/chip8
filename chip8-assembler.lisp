(defmacro if-let (spec then &optional else)
  `(let (,spec) (if ,(car spec) ,then ,else)))

;; I WILL have type checking and I WILL like it
(defmacro defun* (name lambda-list lambda-list-types return-type &body body)
  `(progn (declaim (ftype (function ,lambda-list-types ,return-type) ,name))
          (defun ,name ,lambda-list ,@body)))

(defun* make-sexp (line) (string) string
  (let* ((colon nil)
         (bang nil)
         (dollar nil)
         (chars (map 'list
                     (lambda (ch)
                       (case ch
                         (#\, ")(")
                         (#\: (prog1 " " (setf colon t)))
                         (#\| "|\\||")
                         (#\$ (prog1 " " (setf dollar t)))
                         (#\[ "(")
                         (#\] ")")
                         (#\; ")")
                         (#\! (prog1 "(" (setf bang t)))
                         (t (string ch))))
                     line))
         (line (apply #'concatenate 'string chars)))
    (when bang (setf colon nil))
    (concatenate 'string
                 (if dollar " " "(")
                 line
                 (if (or colon dollar) " " ")"))))

(defun* remove-comment (line) (string) string
  (subseq line 0 (position-if (lambda (x) (case x ((#\' #\") t))) line)))

(defun* parse (filename) (string) list
  (with-open-file (f filename)
    (loop for line = (read-line f nil) while line
          for trimmed = (string-trim " " (remove-comment line))
          unless (uiop:emptyp trimmed)
            collect (make-sexp trimmed) into final
          finally (return (read-from-string (apply #'concatenate 'string
                                                   (append '("(") final '(")"))))))))

(defmacro match (pattern &body clauses)
  `(flet ((ekual (x y) (or (equal x y) (equal x '_))))
     (cond ,@(dolist (clause clauses clauses)
               (setf (car clause)
                     `(if (and (listp ,pattern) (listp ',(car clause)))
                          (when (eql (list-length ',(car clause)) (list-length ,pattern))
                            (every #'ekual ',(car clause) ,pattern))
                          (funcall #'ekual ',(car clause) ,pattern)))))))

(defun* chop (number size &optional (pos 0)) (integer integer &optional integer) integer
  (ldb (byte size pos) number))

(defstruct value data type)

(defparameter +BUILTIN-VALUES+
  `((KEY-1 . ,(make-value :data #x1 :type 'i4)) 
    (KEY-2 . ,(make-value :data #x2 :type 'i4)) 
    (KEY-3 . ,(make-value :data #x3 :type 'i4)) 
    (KEY-4 . ,(make-value :data #xC :type 'i4)) 
    (KEY-Q . ,(make-value :data #x4 :type 'i4)) 
    (KEY-W . ,(make-value :data #x5 :type 'i4)) 
    (KEY-E . ,(make-value :data #x6 :type 'i4)) 
    (KEY-R . ,(make-value :data #xD :type 'i4)) 
    (KEY-A . ,(make-value :data #x7 :type 'i4)) 
    (KEY-S . ,(make-value :data #x8 :type 'i4)) 
    (KEY-D . ,(make-value :data #x9 :type 'i4)) 
    (KEY-F . ,(make-value :data #xE :type 'i4)) 
    (KEY-Z . ,(make-value :data #xA :type 'i4)) 
    (KEY-X . ,(make-value :data #x0 :type 'i4)) 
    (KEY-C . ,(make-value :data #xB :type 'i4)) 
    (KEY-V . ,(make-value :data #xF :type 'i4)) 
    (PI . ,(make-value :data PI      :type 'float))
    (E  . ,(make-value :data (exp 1) :type 'float))
    ;; @HACK the data should be a number but it isn't 
    (V0 . ,(make-value :data 'V0 :type 'V0)) 
    (V1 . ,(make-value :data 'V1 :type 'V1)) 
    (V2 . ,(make-value :data 'V2 :type 'V2)) 
    (V3 . ,(make-value :data 'V3 :type 'V3)) 
    (V4 . ,(make-value :data 'V4 :type 'V4)) 
    (V5 . ,(make-value :data 'V5 :type 'V5)) 
    (V6 . ,(make-value :data 'V6 :type 'V6)) 
    (V7 . ,(make-value :data 'V7 :type 'V7)) 
    (V8 . ,(make-value :data 'V8 :type 'V8)) 
    (V9 . ,(make-value :data 'V9 :type 'V9)) 
    (VA . ,(make-value :data 'VA :type 'VA)) 
    (VB . ,(make-value :data 'VB :type 'VB)) 
    (VC . ,(make-value :data 'VC :type 'VC)) 
    (VD . ,(make-value :data 'VD :type 'VD)) 
    (VE . ,(make-value :data 'VE :type 'VE)) 
    (VF . ,(make-value :data 'VF :type 'VF))))

(defstruct macro
  (calls 0 :type integer)
  (parameters nil :type list)
  (body nil :type list))

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

(defun* instruction? (exp) (t) boolean
  (case exp
    ((EQ NEQ SET ADD OR AND XOR SUB
         SHR SUBN SHL DRAW BCD WRITE
         READ CLEAR RET CALL JUMP JUMP0
         EXIT LORES HIRES READ-FLAGS WRITE-FLAGS
         SCROLL-DOWN SCROLL-RIGHT SCROLL-LEFT
         SCROLL-UP PLANE AUDIO)
     t)))

(defun* builtin-func? (exp) (t) boolean
  (case exp
    ((mut def proc end if then else label loop
          while until include macro let target
          placeholder begin end)
     t)))

(defun* special-func? (exp) (t) boolean
  (or (instruction? exp) (builtin-func? exp)))

(defun* v-reg? (exp) (t) (values (or number null) &optional)
  (case exp
    (v0 0) (v1 1) (v2 2) (v3 3)
    (v4 4) (v5 5) (v6 6) (v7 7)
    (v8 8) (v9 9) (va #xa) (vb #xb)
    (vc #xc) (vd #xd) (ve #xe) (vf #xf)))

(defun* fake? (exp) (t) boolean
  (case exp ((KEY DT ST I HEX BIGHEX LONG RAND) t)))

(defun* special-val? (exp) (t) boolean
  (not (null (or (v-reg? exp) (fake? exp)
                 (eq exp 'pc)))))

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
  local-bodies
  local-atoms
  (macros (copy-alist +BUILTIN-MACROS+)))

(defun assoc-local (item alists)
  (loop for scope in alists
        for x = (assoc item scope)
        when x return x))

(defmacro c8-with-forms-eval-0 ((var list action) &body body)
  `(loop for ,var in ,list
         ,action (if (listp ,var)
                 ,@body
                 (error "'~a' is not a valid form" ,var))))

(defun* c8-eval-arg-0 (env arg) (env t) t
  (if (listp arg)
      (list* (first arg) (loop for a in (rest arg) collect (c8-eval-arg-0 env a)))
      (let ((local (cdr (assoc-local arg (env-local-values env))))
            (atom (cdr (assoc-local arg (env-local-atoms env))))
            (val (cdr (assoc arg (env-values env))))
            (mut (cdr (assoc arg (env-mutables env)))))
        (flet ((get-data (x) (if (value-p x) (value-data x) x)))
          (cond (local (get-data local))
                (atom (get-data atom))
                (mut (get-data mut))
                (val (get-data val))
                ((eq arg 'pc) (env-pc env))
                (t arg))))))

(defun* c8-eval-include-0 (env numbers) (env list) list
  (loop for n in numbers
        collect (c8-eval-arg-0 env n) into f
        do (incf (env-pc env))
        finally (return (list `(include ,@f)))))

(defun* c8-check-main-0 (env name) (env atom) null
  (with-slots (pc main-label) env
    (when (eq name 'main)
      (when (= pc (+ +START+ +OFFSET+))
        (setf pc +START+))
      (setf main-label pc))
    nil))

(defun* c8-eval-label-0
    (env name &optional numbers)
    (env atom &optional list) list
  (when (null name) (error "Label not given a name"))
  (when (or (assoc name (env-labels env))
            (assoc name (env-mutables env))
            (assoc name (env-values env))
            (special-val? name))
    (error "Redefinition of ~a" name))
  (let ((actual-name (if-let (x (cdr (assoc-local name (env-local-atoms env))))
                       (value-data x)
                       name)))
    (c8-check-main-0 env actual-name)
    (push (cons actual-name (env-pc env)) (env-labels env)))
  (when numbers (c8-eval-include-0 env numbers)))

(defun* c8-eval-mut-0 (env name value) (env atom atom) null
  (when (null value) (error "'def ~a' was not initialized" name))
  (when (or (assoc name (env-values env))
            (assoc name (env-labels env))
            (special-val? name))
    (error "Redefinition of ~a" name))
  
  (if (assoc name (env-mutables env))
      (setf (cdr (assoc name (env-mutables env))) (c8-eval-arg-0 env value))
      (push (cons name (c8-eval-arg-0 env value)) (env-mutables env)))
  nil)

(defun infer-type-0 (value)
  (cond ((value-p value) (value-type value))
        ((listp value) 'body)
        ((numberp value)
         (cond ((<= value #xF) 'i4)
               ((<= value #xFF) 'i8)
               ((<= value #xFFF) 'i12)
               ((<= value #xFFFF) 'i16)))
        ((v-reg? value) 'v*)
        (t 'atom)))

(defun* c8-eval-def-0 (env name value) (env atom atom) null
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

(declaim (ftype (function (env list) list)
                c8-eval-0
                c8-eval-form-0)
         (ftype (function) c8-eval-macro-0))

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

;; (defun c8-macroexpand-body-0 (env forms)
;;   (c8-with-forms-eval-0 (form forms collect)
;;     (let ((func (cdr (assoc-local (first form) (env-local-macros env))))
;;           (args (loop for arg in (rest form) collect (c8-eval-arg-0 env arg))))
;;       (list* (if func func (first form)) args))))

(defun c8-check-type-0 (env name value type)
  (typecase (first value)
    (atom (if (null type)
              nil
              (let* ((e-value (c8-eval-arg-0 env (first value)))
                     (inferred (infer-type-0 e-value)))
                (if (eq inferred (if (v-reg? type) 'v* type))
                    (values inferred e-value)
                    (error "Value '~a' = '~a' has type '~a' but was given type '~a'"
                           name (first value) inferred type)))))
    (t (if (eq type 'body)
           (values 'body value)
              (error "Value '~a' = '~a' has type '~a' but was given type '~a'"
                     name value 'body type)))))

(defun c8-macroexpand-0 (env name macro args)
  (let (local-atoms local-values body)
    (loop for key in (macro-parameters macro)
          for index from 0
          for val = args then (cdr val)
          
          do (if (listp key)
                 (if (> (length key) 2)
                     (error "bad parameter in the macro named ~a~%~a" name key)
                     (let* ((pname (first key))
                            (type (second key)))
                       
                       (multiple-value-bind (checked-type e-data) (c8-check-type-0 env pname val type)
                         (case checked-type
                           (body
                            (when (< index (1- (length (macro-parameters macro))))
                              (error "parameters of type body must be last. In macro ~a" name))
                            (push (cons pname e-data) body) (return))
                           
                           (t
                            (case checked-type
                              ((nil))   ; no type means ignore   
                              (atom (push (cons pname (make-value :data e-data :type type)) local-atoms))
                              (t (push (cons pname (make-value :data e-data :type type)) local-values))))))))

                 (let ((pname key)
                       (data (c8-eval-arg-0 env (first val))))
                   (push (cons pname (make-value :data data :type (infer-type-0 data))) local-values))))
    
    (push name (env-context env))
    (push body (env-local-bodies env))
    (push local-values (env-local-values env))
    (push local-atoms (env-local-atoms env))

    (prog1 (c8-eval-0 env (macro-body macro))
      (pop (env-context env))
      (pop (env-local-values env))
      (pop (env-local-bodies env))
      (pop (env-local-atoms env)))))

(defun c8-apply-0 (env app args)
  (let ((atom (cdr (assoc-local app (env-local-atoms env))))
        (body (cdr (assoc-local app (env-local-bodies env))))
        (mac (cdr (assoc app (env-macros env)))))
    
    (cond (body (let ((lvals (pop (env-local-values env)))
                      (lbods (pop (env-local-bodies env)))
                      (latoms (pop (env-local-atoms env))))
                  ;; ignore local scope for bodies
                  (prog1 (c8-eval-0 env body)
                    (push lvals (env-local-values env))
                    (push lbods (env-local-bodies env))
                    (push latoms (env-local-atoms env)))))

          (atom (c8-eval-form-0 env (list* (value-data atom) args)))
          
          ((instruction? app)
           (incf (env-pc env) (if (find 'long (list* app args)) 4 2))
           (list (list* app (loop for arg in args collect (c8-eval-arg-0 env arg)))))
          
          (mac (prog2 (when (eq app (first (env-context env)))
                        (error "Tried to call ~a in context ~a. Recursion is not allowed"
                               app (first (env-context env))))
                   (c8-macroexpand-0 env app mac (list* (macro-calls mac) args))
                 (incf (macro-calls mac))))
          ;; hopefully the definition will be found during the second pass of the initial step
          (t (list (list* app args))))))

(defun flip-test (test)
  (case test
    (eq 'neq) (neq 'eq) (gt 'le) (ge 'lt) (lt 'ge) (le 'gt)
    (t (error "Test must be eq, neq, gt, ge, lt, le"))))

(defun c8-eval-loop-0 (env body)
  (let* ((pc (env-pc env))
         (lp (append (c8-with-forms-eval-0 (f body append)
                       (case (first f)
                         ((while until)
                          (incf (env-pc env) 2) ;; make room for jump
                          (list `(,(first f) ,@(first (c8-eval-form-0 env (rest f))))
                                '(placeholder jump-to-end-loop)))
                         (t (c8-eval-form-0 env f))))
                     (c8-eval-form-0 env `(JUMP ,pc)))))

    (c8-with-forms-eval-0 (f lp collect)
      (match f
        ((while _ _ _) (list* (flip-test (second f)) (nthcdr 2 f)))
        ((until _ _ _) (list*            (second f)  (nthcdr 2 f)))
        ((placeholder jump-to-end-loop) `(JUMP ,(env-pc env)))
        (_ f)))))

(defun c8-eval-if-0 (env form)
  (let* ((test (first (c8-eval-form-0 env (list (second form) (third form) (fourth form)))))
         (test-pc (env-pc env))
         (then-pc nil)
         (else-pc nil)
         
         (body (c8-with-forms-eval-0 (f (nthcdr 4 form) append)
                 (case (first f)
                   (then
                    (when then-pc (error "Too many then statements in: ~a" form))
                    (setf then-pc (incf (env-pc env) 2)) ;; make room for jump
                    '((placeholder jump-to-else-if)))
                   (else
                    (when else-pc (error "Too many else statements in: ~a" form))
                    (setf else-pc (incf (env-pc env) 2)) ;; make room for jump
                    '((placeholder jump-to-end-if)))
                   (t (c8-eval-form-0 env f)))))

         (end-pc (env-pc env)))
    (if (null then-pc)
        (cond (else-pc (error "Else without then in: ~a" form))
              ((> (length body) 1) (error "If statements without then or else cannot have more than one statement~%: ~a" form)))
        (when (> (- then-pc test-pc) 2)
          (error "There cannnot be any statements between the test and then statements in: ~a" form)))
    
    (when then-pc
      (setf test (list* (flip-test (first test)) (rest test))))
    
    (cons test (c8-with-forms-eval-0 (f body collect)
                 (match f
                   ((placeholder jump-to-else-if)
                    (if else-pc
                        `(JUMP ,else-pc)
                        `(JUMP ,end-pc)))
                   ((placeholder jump-to-end-if)
                    `(JUMP ,end-pc))
                   (_ f))))))

(defun c8-eval-proc-0 (env name body)
  (c8-eval-label-0 env name)
  (append (c8-eval-0 env body)
          (unless (eq name 'main) (c8-eval-form-0 env '(ret)))))

(defun* c8-insert-main-0 (env forms) (env list) list
  (with-slots (main-label) env
    (cond ((null main-label) (error "Could not find main label"))
          ((= main-label +START+) forms)
          ((> main-label +START+) (append (c8-eval-form-0 env `(JUMP ,main-label)) forms)))))

(defun* c8-eval-form-0 (env form) (env list) list
  (case (first form)
    ((nil end))
    (mut (c8-eval-mut-0 env (second form) (third form)))
    (def (c8-eval-def-0 env (second form) (third form)))
    (proc (c8-eval-proc-0 env (second form) (cddr form)))
    (if (c8-eval-if-0 env form))
    ((label) (c8-eval-label-0 env (cadr form) (cddr form)))
    (loop (c8-eval-loop-0 env (rest form)))
    (include (c8-eval-include-0 env (rest form)))
    (macro (c8-eval-macro-0 env form))
    (let (c8-eval-let-0 env form))
    (target (setf (env-target env) (second form)) nil)
    (t (c8-apply-0 env (first form) (rest form)))))

(defun* c8-eval-0 (env forms) (env list) list
  (c8-with-forms-eval-0 (form forms append)
    (c8-eval-form-0 env form)))

(defun c8-eval-program-0 (env forms)
  ;; @HACK eval two times to allow macros to be defined anywhere
  (c8-insert-main-0 env (c8-eval-0 env (c8-eval-0 env forms))))

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
    (_ (error "Invalid instruction: ~a~%~\
               Did you maybe not set a target?" instruction))))

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
