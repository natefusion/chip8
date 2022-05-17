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

(defstruct env namespace)

(defun builtin-var? (exp)
  (case exp ((KEY ST DT I) t)))

(defun chip8-type (exp)
  (cond
    ((and (listp exp) (eq (first exp) 'V)) 'V)
    ((builtin-var? exp) exp)
    ((numberp exp) 'N)
    (t nil)))

(defun env-pc (env)
  (cdr (assoc 'pc (env-namespace env))))

(defmethod (setf env-pc) (new-val (obj env))
  (setf (cdr (assoc 'pc (env-namespace obj))) new-val))

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
  (cdr (assoc exp (cdr (assoc 'macro-calls (env-namespace env))))))

(declaim (ftype function
                chip8-eval-application
                chip8-eval-include
                chip8-eval-loop
                chip8-eval-macro
                chip8-eval-proc
                chip8-eval-def))

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
           (@         `(@ ,(chip8-eval (second exp) env)))
           (V         exp)
           (otherwise (chip8-eval-application exp env))))
        (t (chip8-eval-var exp env))))

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

 (defun chip8-eval-args (exps env)
   (mapcar (lambda (x) (chip8-eval x env)) exps))

(defun make-scope (namespace &optional keys data)
  (make-env :namespace (pairlis (append '(scope-separator) keys)
                                (append '(nil) data)
                                namespace)))

(defun add-to-calls (name env)
  (push (cons name 0) (cdr (assoc 'macro-calls (env-namespace env)))))

(defun chip8-eval-macro (exp env)
  (let ((name (second exp))
        (args (third exp))
        (body (cdddr exp)))
    (cond ((assoc name (env-namespace env)) (error "macro redefinition of '~a'" name))
          ((listp name) (error "macro not given a name: '~a'" exp))
          (t (add-to-calls name env)
             (push (cons name
                         (lambda (env &rest vars)
                           (chip8-eval-forms body (make-scope (env-namespace env)
                                                              (append args '(calls))
                                                              (append vars (list (chip8-eval-calls name env)))))))
                   (env-namespace env))))
    nil))

(defun chip8-eval-proc (exp env)
  (let ((name (second exp))
        (body (cddr exp)))
    ;; PC should start at #x202 to make room for the jump to main unless the program starts with main
    (when (and (= #x202 (env-pc env)) (eq name 'main))
      (setf (env-pc env) #x200))

    (chip8-eval `(|:| ,name) env)
    (append (chip8-eval-forms body (make-scope (env-namespace env)))
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
  ;; Eval two times to resolve anything left uncompiled
  (let* ((binary (chip8-eval-forms (chip8-eval-forms exps env) env))
         (main-label (cdr (assoc 'main (env-namespace env))))
         (jump-to-main? (unless (= main-label #x200)
                          (chip8-eval `(JUMP ,main-label) env))))
    (chip8-eval-at (append jump-to-main? binary))))

(defun chip8-eval-loop (exp env)
  (let* ((label (env-pc env))
         (new-env (make-scope (env-namespace env))))
    (append (chip8-eval-forms (rest exp) new-env)
            (chip8-eval `(JUMP ,label) new-env))))

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

(defun inc-calls (name env)
  (let ((calls (cdr (assoc name (cdr (assoc 'macro-calls (env-namespace env)))))))
    (when calls (incf (cdr (assoc name (cdr (assoc 'macro-calls (env-namespace env)))))))))

(defun chip8-eval-application (exp env)
  ;; Do I want to eval v registers here???
  (let* ((function (chip8-eval (first exp) env))
         (arguments (chip8-eval-args (rest exp) env)))
    (if (eq (and (listp function) (first function)) 'undefined)
        `(undefined ,exp)
        (let ((application (apply function env arguments)))
          (inc-calls (first exp) env)
          application))))

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

(defun clean-args (args env)
  (let ((cleaned (remove-if #'builtin-var? (chip8-eval-args args env))))
    (if (find t (mapcar (lambda (x)
                          (and (listp x) (eq (first x) 'undefined)))
                        cleaned))
        'undefined (mapcar #'chip8-eval-v cleaned))))

(defmacro make-instruction (name &rest alist)
  `(defun ,name (env &rest args)
     (let ((cleaned (clean-args args env)))
       (incf (env-pc env) 2)
       (if (eq cleaned 'undefined)
           (list (cons (car (rassoc #',name (env-namespace env))) args))
           (emit-op (combine-op (cdr (assoc (mapcar #'chip8-type (chip8-eval-args args env)) ',alist :test #'equal)) cleaned))))))

(make-instruction chip8-eq
                  ((V V)   9 X Y 0)
                  ((V N)   4 X KK)
                  ((V KEY) E X A 1))

(make-instruction chip8-neq
                  ((V KEY) E X 9 E)
                  ((V V)   5 X Y 0)
                  ((V N)   3 X KK))

(make-instruction chip8-set
                  ((V N)   6 X KK)
                  ((V V)   8 X Y 0)
                  ((I N)   A NNN)
                  ((V DT)  F X 0 7)
                  ((DT V)  F X 1 5)
                  ((V ST)  F X 1 8)
                  ((I V)   F X 2 9)
                  ((V KEY) F X 0 A))

(make-instruction chip8-add
                  ((V N) 7 X KK)
                  ((V V) 8 X Y 4)
                  ((I V) F X 1 E))

(make-instruction chip8-or   ((V V) 8 X Y 1))
(make-instruction chip8-and  ((V V) 8 X Y 2))
(make-instruction chip8-xor  ((V V) 8 X Y 3))
(make-instruction chip8-sub  ((V V) 8 X Y 5))
(make-instruction chip8-shr  ((V V) 8 X Y 6))
(make-instruction chip8-subn ((V V) 8 X Y 7))
(make-instruction chip8-shl  ((V V) 8 X Y E))

(make-instruction chip8-rand ((V N)   C X KK))
(make-instruction chip8-draw ((V V N) D X Y N))

(make-instruction chip8-bcd   ((V) F X 3 3))
(make-instruction chip8-write ((V) F X 5 5))
(make-instruction chip8-read  ((V) F X 6 5))

(make-instruction chip8-clear (()  0 0 E 0))
(make-instruction chip8-ret   (()  0 0 E E))
(make-instruction chip8-call  ((N) 2 NNN))
(make-instruction chip8-jump  ((N) 1 NNN))
(make-instruction chip8-jump0 ((N) B NNN))

;; chip8-eval-application passes the environment to the application.
;; I want to ignore this for the mathematical operations.
(defmacro lm (func)
  `(lambda (&rest args) (apply (function ,func) (rest args))))

(defun default-namespace ()
  (copy-alist
   `((PC    .  #x202)
     (EQ    . ,#'chip8-eq)
     (NEQ   . ,#'chip8-neq)
     (SET   . ,#'chip8-set)
     (ADD   . ,#'chip8-add)
     (OR    . ,#'chip8-or)
     (AND   . ,#'chip8-and)
     (XOR   . ,#'chip8-xor)
     (SUB   . ,#'chip8-sub)
     (SHR   . ,#'chip8-shr)
     (SUBN  . ,#'chip8-subn)
     (SHL   . ,#'chip8-shl)
     (RAND  . ,#'chip8-rand)
     (DRAW  . ,#'chip8-draw)
     (BCD   . ,#'chip8-bcd)
     (WRITE . ,#'chip8-write)
     (READ  . ,#'chip8-read)
     (CLEAR . ,#'chip8-clear)
     (RET   . ,#'chip8-ret)
     (CALL  . ,#'chip8-call)
     (JUMP  . ,#'chip8-jump)
     (JUMP0 . ,#'chip8-jump0)

     (MACRO-CALLS . nil)
     
     (KEY   . KEY)
     (ST    . ST)
     (DT    . DT)
     (I     . I)
     
     (V0 V #x0)
     (V1 V #x1)
     (V2 V #x2)
     (V3 V #x3)
     (V4 V #x4)
     (V5 V #x5)
     (V6 V #x6)
     (V7 V #x7)
     (V8 V #x8)
     (V9 V #x9)
     (VA V #xA)
     (VB V #xB)
     (VC V #xC)
     (VD V #xD)
     (VE V #xE)
     (VF V #xF)

     (&  . ,(lm logand))
     (\| . ,(lm logior))
     (<< . ,(lm (lambda (x y) (ash x y))))
     (>> . ,(lm (lambda (x y) (ash x (- y)))))
     (+ . ,(lm +))
     (- . ,(lm -))
     (* . ,(lm *))
     (/ . ,(lm /))
     (% . ,(lm mod))
     (floor . ,(lm floor)))))

(defun chip8-compile (filename)
  (chip8-eval-program
   (parse (clean (uiop:read-file-lines filename)))
   (make-env :namespace (default-namespace))))

(defun chip8-write (bytes filename)
  (with-open-file (f filename
                     :direction :output
                     :if-exists :supersede
                     :if-does-not-exist :create
                     :element-type 'unsigned-byte)
    (mapcar (lambda (x) (write-byte x f)) bytes)))
