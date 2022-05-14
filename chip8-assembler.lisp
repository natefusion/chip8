(eval-when (:compile-toplevel :execute)
  (ql:quickload :trivia)
  (use-package :trivia))

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
                  (#\; "|;|")
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

(defun chip8-eval-v? (exp)
  (case exp
    (V0 0) (V1 1) (V2 2) (V3 3)
    (V4 4) (V5 5) (V6 6) (V7 7)
    (V8 8) (V9 9) (VA #xA) (VB #xB)
    (VC #xC) (VD #xD) (VE #xE) (VF #xF)))

(defun v? (exp)
  (not (null (chip8-eval-v? exp))))

(defun builtin-var? (exp)
  (case exp ((KEY ST DT I) t)))

(defun self-evaluating? (exp)
  (and (not (listp exp))
       (or (numberp exp)
           (builtin-var? exp)
           (v? exp))))

(defun chip8-type (exp)
  (cond
    ((v? exp) 'V)
    ((builtin-var? exp) exp)
    (t 'N)))

(defun def? (exp)
  (and (listp exp)
       (eq (first exp) 'DEF)))

(defun label? (exp)
  (and (listp exp)
       (eq (first exp) 'LAB)))

(defun loop? (exp)
  (and (listp exp)
       (eq (first exp) 'LOOP)))

(defun application? (exp)
  (and (not (null exp))
       (listp exp)
       (not (def? exp))
       (not (label? exp))))

(defun var? (exp)
  (and (not (application? exp))
       (not (self-evaluating? exp))))

(defun include? (exp)
  (and (listp exp)
       (eq (first exp) 'INCLUDE)))

(defun unpack? (exp)
  (and (listp exp)
       (eq (first exp) 'UNPACK)))

(defun macro? (exp)
  (and (listp exp)
       (eq (first exp) 'MACRO)))

(defun proc? (exp)
  (and (listp exp)
       (eq (first exp) 'PROC)))

(defun comment? (exp)
  (and (listp exp)
       (eq (first exp) '|;|)))

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
    (if x (cdr x) exp)))

(declaim (ftype function
                chip8-eval-application
                chip8-eval-include
                chip8-eval-loop
                chip8-eval-macro
                chip8-eval-unpack
                chip8-eval-proc
                chip8-eval-def))

(defun chip8-eval (exp env)
  (cond ((self-evaluating? exp) exp)
        ((comment? exp) nil)
        ((def? exp) (chip8-eval-def exp env))
        ((label? exp) (chip8-eval-label exp env))
        ((proc? exp) (chip8-eval-proc exp env))
        ((var? exp) (chip8-eval-var exp env))
        ((loop? exp) (chip8-eval-loop exp env))
        ((include? exp) (chip8-eval-include exp env))
        ((unpack? exp) (chip8-eval-unpack exp env))
        ((macro? exp) (chip8-eval-macro exp env))
        ((application? exp) (chip8-eval-application exp env))
        (t (error "wow you did something bad"))))

(defun chip8-eval-def (exp env)
  (let ((name (second exp))
        (value (third exp)))
    (cond ((null value) (error "'def ~a' was not initialized" name))
          ((in-scope? name (env-namespace env)) (error "def redefinition of '~a'" name))
          (t (push (cons name (chip8-eval value env)) (env-namespace env))))
    nil))

(defun chip8-eval-file (exps env)
  (if (null exps)
      nil
      (let* ((x (chip8-eval (first exps) env))
             (y (if (and x (atom x))
                    (list x) x)))
        (append y (chip8-eval-file (rest exps) env)))))

(defun make-scope (namespace &optional keys data)
  (make-env :namespace (pairlis (append '(scope-separator) keys)
                                (append '(nil) data)
                                namespace)))

(defun chip8-eval-macro (exp env)
  (let ((name (second exp))
        (args (third exp))
        (body (cdddr exp)))
    (if (assoc name (env-namespace env))
        (error "macro redefinition of '~a'" name)
        (push (cons name
                    (lambda (env &rest vars)
                      (chip8-eval-file body (make-scope (env-namespace env) args vars))))
              (env-namespace env)))
    nil))

(defun chip8-eval-proc (exp env)
  (let ((name (second exp))
        (body (cddr exp)))
    ;; PC should start at #x202 to make room for the jump to main unless the program starts with main
    (when (and (= #x202 (env-pc env)) (eq name 'main))
      (setf (env-pc env) #x200))

    (chip8-eval `(lab ,name) env)
    (append (chip8-eval-file body (make-scope (env-namespace env)))
            (unless (eq name 'main) (chip8-eval '(ret) env)))))

(defun chip8-eval-top (exps env)
  ;; Eval two times to resolve anything left uncompiled
  (let* ((binary (chip8-eval-file (chip8-eval-file exps env) env))
         (main-label (cdr (assoc 'main (env-namespace env))))
         (jump-to-main? (unless (= main-label #x200)
                          (chip8-eval `(JUMP ,main-label) env))))
    (append jump-to-main? binary)))

(defun chip8-eval-unpack (exp env)
  ;; TODO: doesn't handle 16-bit addresses
  (let ((nibble (chip8-eval (second exp) env))
        (label (chip8-eval (third exp) env)))
    (chip8-eval-file
     `((set v0 ,(logior (ash nibble 4) (ash label -8)))
       (set v1 ,(logand label #xFF)))
     env)))

(defun chip8-eval-args-partial (args env &key eval-v)
  (mapcar (lambda (x)
            (if (and (v? x) eval-v)
                (chip8-eval-v? x)
                (chip8-eval x env)))
          args))

(defun chip8-eval-loop (exp env)
  (let ((label (env-pc env))
        (loop-body (chip8-eval-file (rest exp) env)))
    (loop :for x :in loop-body
           :if (eq x 'BREAK)
             :append (chip8-eval `(JUMP ,(+ 4 (env-pc env))) env) :into final
           :else
             :collect x :into final
          :finally (return (append final (chip8-eval `(JUMP ,label) env))))))

(defun chip8-eval-include (exp env)
  (let ((name (second exp))
        ;; silently does nothing if no numbers are given to include (bad!)
        (bytes (let ((x (chip8-eval-args-partial (cddr exp) env)))
                 (append x (when (oddp (length x)) '(0))))))
    (dolist (x bytes)
      (cond ((not (numberp x)) (error "Only numbers can be included"))
            ((> x 255) (error "cannot include numbers larger than 255 (#xFF)"))))
    (chip8-eval `(lab ,name) env)
    (incf (env-pc env) (length bytes))
    bytes))

(defun chip8-eval-application (exp env)
  ;; Do I want to eval v registers here???
  (apply (chip8-eval (first exp) env)
         env
         (chip8-eval-args-partial (rest exp) env)))

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

(defmacro make-instruction (name &rest alist)
  `(defun ,name (env &rest args)
     (let* ((cleaned (remove-if #'builtin-var? (chip8-eval-args-partial args env :eval-v t)))
            (shell (combine-op (cdr (assoc (mapcar #'chip8-type args) ',alist :test #'equal)) cleaned)))
       (incf (env-pc env) 2)
       (cond ((null shell) (error "wat: ~a" args))
             ((remove-if #'numberp cleaned) (list (cons ',name args)))
             (t (emit-op shell))))))

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

(make-instruction chip8-or   ((V V) 8 X X 1))
(make-instruction chip8-and  ((V V) 8 X X 2))
(make-instruction chip8-xor  ((V V) 8 X X 3))
(make-instruction chip8-sub  ((V V) 8 X X 5))
(make-instruction chip8-shr  ((V V) 8 X X 6))
(make-instruction chip8-subn ((V V) 8 X X 7))
(make-instruction chip8-shl  ((V V) 8 X X E))

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
     (BREAK . ,#'(lambda () '(BREAK)))
     (+ . ,#'+)
     (- . ,#'-)
     (* . ,#'*)
     (/ . ,#'/))))

(defun chip8-compile (filename)
  (chip8-eval-top
   (parse (clean (uiop:read-file-lines filename)))
   (make-env :namespace (default-namespace))))

(defun chip8-write (bytes filename)
  (with-open-file (f filename
                     :direction :output
                     :if-exists :supersede
                     :if-does-not-exist :create
                     :element-type 'unsigned-byte)
    (mapcar (lambda (x) (write-byte x f)) bytes)))
