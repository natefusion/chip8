(declaim (ftype function chip8-eval))

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

(defun parse (cleaned)
  (eval (read-from-string (concatenate 'string "'(" cleaned ")"))))

;; (defstruct scope macro-calls namespace)
(defstruct env macro-calls namespace)

(defun env-pc (env)
  (cdr (assoc 'pc (env-namespace env))))

(defmethod (setf env-pc) (new-val (obj env))
  (setf (cdr (assoc 'pc (env-namespace obj))) new-val))

(defun builtin-var? (exp)
  (case exp ((KEY ST DT I) t)))

(defun chip8-type (exp)
  (cond
    ((and (listp exp) (eq (first exp) 'V)) 'V)
    ((builtin-var? exp) exp)
    ((numberp exp) 'N)
    (t nil)))

(defun in-scope? (value namespace)
  (let ((scope-separator (position 'scope-separator (reverse namespace) :key #'car)))
    (if scope-separator
        (when (assoc value (butlast namespace scope-separator)) t)
        (when (assoc value namespace) t))))

(defun chip8-eval-label (exp env)
  (let ((name (second exp)))
    (if (in-scope? name (env-namespace env))
        (error "label redefinition of '~a'" name)
        (push (cons name (env-pc env)) (env-namespace env)))
    nil))

(defun chip8-eval-var (exp env)
  (let ((x (assoc exp (env-namespace env))))
    (if x (cdr x) `(undefined ,exp))))

(defun chip8-eval-v (exp)
  (if (and (listp exp) (eq (first exp) 'V))
      (second exp)
      exp))

(defun chip8-eval-calls (exp env)
  (cdr (assoc exp (env-macro-calls env))))

(defun chip8-eval-args (exps env)
  (mapcar (lambda (x) (chip8-eval x env)) exps))

(defun undefined? (args)
  (when (listp args) (find t (mapcar (lambda (x) (eq (if (listp x) (first x) x) 'undefined)) args))))

(defun chip8-eval-def (exp env)
  (let ((name (second exp))
        (value (third exp)))
    (cond ((null value) (error "'def ~a' was not initialized" name))
          ((in-scope? name (env-namespace env)) (error "def redefinition of '~a'" name))
          (t (push (cons name (chip8-eval value env)) (env-namespace env))))
    nil))

(defun chip8-eval-forms (exps env)
  (loop :for x :in exps
        :for evald = (chip8-eval x env)
        :if (listp evald)
          :append evald
        :else
          :collect evald))

(defun make-scope (env &optional keys data)
  (make-env :macro-calls (env-macro-calls env)
            :namespace (pairlis (append '(scope-separator) keys)
                                (append '(nil) data)
                                (env-namespace env))))

(defun add-to-calls (name env)
  (push (cons name 0) (env-macro-calls env)))

(defun make-macro (name body args env)
  (lambda (passed-env &rest vars)
    (let ((evald (chip8-eval-forms
                  body (make-scope env
                                   (append '(calls) args)
                                   (append (list (chip8-eval-calls name passed-env)) vars)))))
      (incf (cdr (assoc name (env-macro-calls env))))
      evald)))

(defun chip8-eval-macro (exp env)
  (let ((name (second exp))
        (args (third exp))
        (body (cdddr exp)))
    (cond ((assoc name (env-namespace env)) (error "macro redefinition of '~a'" name))
          ((listp name) (error "macro not given a name: '~a'" exp))
          (t (add-to-calls name env)
             (push (cons name (make-macro name body args env)) (env-namespace env))))
    nil))

(defun chip8-eval-proc (exp env)
  (let ((name (second exp))
        (body (cddr exp)))
    ;; PC should start at #x202 to make room for the jump to main unless the program starts with main
    (when (and (= #x202 (env-pc env)) (eq name 'main))
      (setf (env-pc env) #x200))

    (chip8-eval `(|:| ,name) env)
    (append (chip8-eval-forms body (make-scope env))
            (unless (eq name 'main) (chip8-eval '(ret) env)))))

(defun chip8-eval-at (exps)
  (loop :for x :in exps
        :if (and (listp x) (eq (first x) '@))
          :collect (nth (- (second x) #x200) result) :into result
        :else :if (listp x)
                :append x :into result
        :else
          :collect x :into result
        :finally (return result)))

(defun chip8-eval-program (exps env)
  (chip8-eval '(def pc #x202) env)
  ;; Eval two times to resolve anything left uncompiled
  (let* ((binary (chip8-eval-forms (chip8-eval-forms exps env) env))
         (main-label (cdr (assoc 'main (env-namespace env))))
         (jump-to-main? (unless (eql main-label #x200)
                          (chip8-eval `(JUMP ,main-label) env))))
    (chip8-eval-at (append jump-to-main? binary))))

(defun chip8-eval-loop (exp env)
  (let* ((label (env-pc env))
         (new-env (make-scope env)))
    (append (chip8-eval-forms (rest exp) new-env)
            (chip8-eval `(JUMP ,label) env))))

(defun chip8-eval-include (exp env)
  (let ((name (second exp))
        (bytes (mapcar (lambda (x)
                         (cond ((not (numberp x)) x)
                               ((> x #xFF) (logand x #xFF))
                               (t x)))
                       (chip8-eval-args (cddr exp) env))))
    (chip8-eval `(\: ,name) env)
    (incf (env-pc env) (length bytes))
    bytes))

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

(defmacro make-instruction (lname c8name &rest alist)
  `(defun ,lname (env &rest args)
     (incf (env-pc env) 2)
     (let ((e-args (chip8-eval-args args env)))
       (if (undefined? e-args)
           (list (cons ',c8name args))
           (emit-op (combine-op (cdr (assoc (mapcar #'chip8-type e-args) ',alist :test #'equal))
                                (mapcar #'chip8-eval-v (remove-if #'builtin-var? e-args))))))))

(make-instruction chip8-eq eq
                  ((V V)   9 X Y 0)
                  ((V N)   4 X KK)
                  ((V KEY) E X A 1))

(make-instruction chip8-neq neq
                  ((V KEY) E X 9 E)
                  ((V V)   5 X Y 0)
                  ((V N)   3 X KK))

(make-instruction chip8-set set
                  ((V N)   6 X KK)
                  ((V V)   8 X Y 0)
                  ((I N)   A NNN)
                  ((V DT)  F X 0 7)
                  ((DT V)  F X 1 5)
                  ((V ST)  F X 1 8)
                  ((I V)   F X 2 9)
                  ((V KEY) F X 0 A))

(make-instruction chip8-add add
                  ((V N) 7 X KK)
                  ((V V) 8 X Y 4)
                  ((I V) F X 1 E))

(make-instruction chip8-or   or   ((V V) 8 X Y 1))
(make-instruction chip8-and  and  ((V V) 8 X Y 2))
(make-instruction chip8-xor  xor  ((V V) 8 X Y 3))
(make-instruction chip8-sub  sub  ((V V) 8 X Y 5))
(make-instruction chip8-shr  shr  ((V V) 8 X Y 6))
(make-instruction chip8-subn subn ((V V) 8 X Y 7))
(make-instruction chip8-shl  shl  ((V V) 8 X Y E))

(make-instruction chip8-rand rand ((V N)   C X KK))
(make-instruction chip8-draw draw ((V V N) D X Y N))

(make-instruction chip8-bcd   bcd   ((V) F X 3 3))
(make-instruction chip8-write write ((V) F X 5 5))
(make-instruction chip8-read  read  ((V) F X 6 5))

(make-instruction chip8-clear clear (()  0 0 E 0))
(make-instruction chip8-ret   ret   (()  0 0 E E))
(make-instruction chip8-call  call  ((N) 2 NNN))
(make-instruction chip8-jump  jump  ((N) 1 NNN))
(make-instruction chip8-jump0 jump0 ((N) B NNN))

(defmacro lm (f)
  `(lambda (env &rest args) (apply #',f (chip8-eval-args args env))))

(defun chip8-eval (exp env)
  (cond ((null exp) nil)
        ((numberp exp) exp)
        ((listp exp)
         (case (first exp) 
           (\;        nil)
           (def       (chip8-eval-def exp env))
           (\:        (chip8-eval-label exp env))
           (proc      (chip8-eval-proc exp env))
           (loop      (chip8-eval-loop exp env))
           (include   (chip8-eval-include exp env))
           (macro     (chip8-eval-macro exp env))
           (undefined (chip8-eval (second exp) env))
           (V exp)
           (@ `(@ (chip8-eval (second exp))))
           (otherwise (apply (chip8-eval (first exp) env) env (rest exp)))))
        (t (case exp
             (EQ    #'chip8-eq)
             (NEQ   #'chip8-neq)
             (SET   #'chip8-set)
             (ADD   #'chip8-add)
             (OR    #'chip8-or)
             (AND   #'chip8-and)
             (XOR   #'chip8-xor)
             (SUB   #'chip8-sub)
             (SHR   #'chip8-shr)
             (SUBN  #'chip8-subn)
             (SHL   #'chip8-shl)
             (RAND  #'chip8-rand)
             (DRAW  #'chip8-draw)
             (BCD   #'chip8-bcd)
             (WRITE #'chip8-write)
             (READ  #'chip8-read)
             (CLEAR #'chip8-clear)
             (RET   #'chip8-ret)
             (CALL  #'chip8-call)
             (JUMP  #'chip8-jump)
             (JUMP0 #'chip8-jump0)
             
             (&  (lm logand))
             (\| (lm logior))
             (<< (lm ash))
             (>> (lm (lambda (x y) (ash x (- y)))))
             (+  (lm +))
             (- (lm -))
             (* (lm *))
             (/ (lm /))
             (% (lm mod))
             (floor (lm floor))
             
             (V0 '(V #x0))
             (V1 '(V #x1))
             (V2 '(V #x2))
             (V3 '(V #x3))
             (V4 '(V #x4))
             (V5 '(V #x5))
             (V6 '(V #x6))
             (V7 '(V #x7))
             (V8 '(V #x8))
             (V9 '(V #x9))
             (VA '(V #xA))
             (VB '(V #xB))
             (VC '(V #xC))
             (VD '(V #xD))
             (VE '(V #xE))
             (VF '(V #xF))
             (KEY 'KEY)
             (DT 'DT)
             (ST 'ST)
             (I  'I)
             (otherwise (chip8-eval-var exp env))))))

(defun chip8-compile (filename)
  (chip8-eval-program
   (parse (clean (uiop:read-file-lines filename)))
   (make-env)))

(defun chip8-write (bytes filename)
  (with-open-file (f filename
                     :direction :output
                     :if-exists :supersede
                     :if-does-not-exist :create
                     :element-type 'unsigned-byte)
    (mapcar (lambda (x) (write-byte x f)) bytes)))
