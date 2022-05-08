(eval-when (:compile-toplevel :execute)
  (ql:quickload :trivia)
  (use-package :trivia))

(defun flatten (l)
  (apply #'concatenate 'string l))

;; This works but could be better
(defun make-sexp (line)
  (loop :for ch :across line
        :for count :from 0
        :with result = (make-array 0 :element-type 'character :fill-pointer 0 :adjustable t)
        :with parens-to-add = 0
        :if (and (zerop count) (char/= #\( ch))
          :do (progn (incf parens-to-add)
                     (vector-push-extend #\( result))
        :if (char= #\, ch)
          :do (progn (vector-push-extend #\) result)
                     (vector-push-extend #\( result))
        :if (char= #\. ch)
          :do (progn (incf parens-to-add)
                     (vector-push-extend #\( result))
          :else
            :do (vector-push-extend ch result)
        :finally
           (return (dotimes (x parens-to-add result)
                     (vector-push-extend #\) result)))))

(defun remove-comments (line)
  (subseq line 0 (position #\; line :test #'char=)))

(defun scrub-input (input)
  (loop :for line :in input
        :for trimmed = (remove-comments (string-trim " " line))

        :unless (string= "" trimmed)
          :collect trimmed))

(defun parse (x)
  (eval (read-from-string
         (concatenate 'string
               "'("
               (flatten
                (mapcar #'make-sexp (scrub-input (uiop:read-file-lines x))))
               ")"))))

(defstruct env inner outer)

(defun env-pc (env)
  (cdr (assoc 'pc (env-inner env))))

(defmethod (setf env-pc) (new-val (obj env))
  (setf (cdr (assoc 'pc (env-inner obj))) new-val))

(defun chip8-eval-v? (exp)
  (match exp
    ('V0 0) ('V1 1) ('V2 2) ('V3 3)
    ('V4 4) ('V5 5) ('V6 6) ('V7 7)
    ('V8 8) ('V9 9) ('VA #xA) ('VB #xB)
    ('VC #xC) ('VD #xD) ('VE #xE) ('VF #xF)
    (t nil)))

(defun v? (exp)
  (not (null (chip8-eval-v? exp))))

(defun builtin-var? (exp)
  (or (eq exp 'KEY)
      (eq exp 'ST)
      (eq exp 'DT)
      (eq exp 'I)))

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

(defun ins? (exp)
  (and (listp exp)
       (match (first exp)
         ('EQ 't) ('NEQ 't) ('SET 't) ('ADD 't)
         ('OR 't) ('AND 't) ('XOR 't) ('SUB 't)
         ('SHR 't) ('SUBR 't) ('SHL 't) ('RAND 't)
         ('DRAW 't) ('BCD 't) ('WRITE 't) ('READ 't)
         ('CLEAR 't) ('RET 't) ('CALL 't) ('JUMP 't)
         ('JUMP0 't)
         (_ nil))))

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

(defun chip8-eval-def (exp env)
  (let ((name (second exp))
        (value (third exp)))
    (cond ((assoc name (env-inner env)) (error "def Redefinition of '~a'" name))
          ((null value) (error "'def ~a' was not initialized" name)) 
          (t (push (cons name value) (env-inner env))))
    nil))

(defun chip8-eval-label (exp env)
  (let ((name (second exp)))
    (if (assoc name (env-inner env))
        (error "label Redefinition of '~a'" name)
        (push (cons name (env-pc env)) (env-inner env)))
    nil))

(defun chip8-eval-var (exp env)
  (let ((inner (assoc exp (env-inner env)))
        (outer (env-outer env)))
    (cond (inner (cdr inner))
          (outer (chip8-eval-var exp outer))
          (t exp))))

;; These functions have circular depedencies to chip8-eval
(declaim (ftype function
                chip8-eval-application
                chip8-eval-include
                chip8-eval-ins
                chip8-eval-loop
                chip8-eval-macro
                chip8-eval-unpack
                chip8-eval-proc))

(defun chip8-eval (exp env)
  (cond ((self-evaluating? exp) exp)
        ((def? exp) (chip8-eval-def exp env))
        ((label? exp) (chip8-eval-label exp env))
        ((proc? exp) (chip8-eval-proc exp env))
        ((var? exp) (chip8-eval-var exp env))
        ((loop? exp) (chip8-eval-loop exp env))
        ((include? exp) (chip8-eval-include exp env))
        ((unpack? exp) (chip8-eval-unpack exp env))
        ((macro? exp) (chip8-eval-macro exp env))
        ((ins? exp) (chip8-eval-ins exp env))
        ((application? exp) (chip8-eval-application exp env))
        (t (error "wow you did something bad"))))

(defun chip8-eval-file (exps env)
  (if (null exps)
      nil
      (let* ((x (chip8-eval (first exps) env))
             (y (if (and (not (null x)) (atom x))
                    (list x) x)))
        (append y (chip8-eval-file (rest exps) env)))))

(defun chip8-eval-macro (exp env)
  (let ((name (second exp))
        (args (third exp))
        (body (cdddr exp)))
    (if (assoc name (env-inner env))
        (error "macro redefinition of '~a'" name)
        (push (cons name (lambda (&rest vars)
                           (let ((new-env (make-env :outer env)))
                             (mapcar (lambda (arg var) (push (cons arg var) (env-inner new-env))) args vars)
                             (chip8-eval-file body new-env))))
              (env-inner env)))
    nil))

(defun chip8-eval-proc (exp env)
  (let ((name (second exp))
        (body (cddr exp)))
    ;; PC should start at #x202 to make room for the jump to main unless the program starts with main
    (when (and (= #x202 (env-pc env)) (eq name 'main))
      (setf (env-pc env) #x200))

    (chip8-eval `(lab ,name) env)
    (append (chip8-eval-file body env) (unless (eq name 'main) (chip8-eval '(ret) env)))))

(defun chip8-eval-top (exps env)
  ;; Eval two times to resolve anything left uncompiled
  (let* ((binary (chip8-eval-file (chip8-eval-file exps env) env))
         (main-label (cdr (assoc 'main (env-inner env))))
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

(defun chip8-eval-ins (exp env)
  (funcall (chip8-eval (first exp) env)
           (first exp)
           (chip8-eval-args-partial (rest exp) env)
           env))

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
         (chip8-eval-args-partial (rest exp) env :eval-v t)))

(defun combine-op (args shell&info)
  (let ((shell (car shell&info))
        (info (cadr shell&info)))
    (loop :for x :in args
          :for i :from 0
          :do (let ((shift (logand (ash info (* i -4)) #xF)))
                (setf shell (logior shell (ash x shift))))
          :finally (return (list (ash (logand shell #xFF00) -8)
                                 (logand shell #xFF))))))

(defun emit-op (proc args env)
  (incf (env-pc env) 2)
  
  (let ((stripped-args
          (remove-if #'builtin-var? (chip8-eval-args-partial args env :eval-v t))))
    
    (if (remove-if #'numberp stripped-args)
        (list (cons proc args))
        
        (combine-op
         stripped-args
         
         (match (append (list proc) (mapcar #'chip8-type args))
           ('(EQ V V) '(#x9000 #x48))
           ('(EQ V N) '(#x4000 #x8))
           ('(EQ V KEY) '(#xE0A1 #x8))
           
           ('(NEQ V KEY) '(#xE09E #x81))
           ('(NEQ V V) '(#x5000 #x48))
           ('(NEQ V N) '(#x3000 #x8))
           
           ('(SET V N) '(#x6000 #x8))
           ('(SET V V) '(#x8000 #x48))
           ('(SET I N) '(#xA000 #x0))
           ('(SET V DT) '(#xF007 #x8))
           ('(SET DT V) '(#xF015 #x8))
           ('(SET V ST) '(#xF018 #x8))
           ('(SET I V) '(#xF029 #x8))
           ('(SET V KEY) '(#xF00A #x8))
           
           ('(ADD V N) '(#x7000 #x8))
           ('(ADD V V) '(#x8004 #x48))
           ('(ADD I V) '(#xF01E #x8))
           
           ('(OR V V) '(#x8001 #x48))
           ('(AND V V) '(#x8002 #x48))
           ('(XOR V V) '(#x8003 #x48))
           ('(SUB V V) '(#x8005 #x48))
           ('(SHR V V) '(#x8006 #x48))
           ('(SUBR V V) '(#x8007 #x48))
           ('(SHL V V) '(#x800E #x48))
           
           ('(RAND V N) '(#xC000 #x8))
           ('(DRAW V V N) '(#xD000 #x48))
           
           ('(BCD V) '(#xF033 #x8))
           ('(WRITE V) '(#xF055 #x8))
           ('(READ V) '(#xF065 #x8))
           
           ('(CLEAR) '(#x00E0 #x0))
           ('(RET) '(#x00EE #x0))
           ('(CALL N) '(#x2000 #x0))
           ('(JUMP N) '(#x1000 #x0))
           ('(JUMP0 N) '(#xB000 #x0))
           (_ (error "Invalid instruction '~a'" proc)))))))

(defun default-namespace ()
  `((PC    .  #x202)
    (EQ    . ,#'emit-op)
    (NEQ   . ,#'emit-op)
    (SET   . ,#'emit-op)
    (ADD   . ,#'emit-op)
    (OR    . ,#'emit-op)
    (AND   . ,#'emit-op)
    (XOR   . ,#'emit-op)
    (SUB   . ,#'emit-op)
    (SHR   . ,#'emit-op)
    (SUBR  . ,#'emit-op)
    (SHL   . ,#'emit-op)
    (RAND  . ,#'emit-op)
    (DRAW  . ,#'emit-op)
    (BCD   . ,#'emit-op)
    (WRITE . ,#'emit-op)
    (READ  . ,#'emit-op)
    (CLEAR . ,#'emit-op)
    (RET   . ,#'emit-op)
    (CALL  . ,#'emit-op)
    (JUMP  . ,#'emit-op)
    (JUMP0 . ,#'emit-op)
    (BREAK . ,#'(lambda () '(BREAK)))
    (+ . ,#'+)
    (- . ,#'-)
    (* . ,#'*)
    (/ . ,#'/)))

(defun chip8-compile (file)
  (chip8-eval-top
   (parse file)
   (make-env :inner (default-namespace))))

(defun chip8-write (bytes filename)
  (with-open-file (f filename
                     :direction :output
                     :if-exists :supersede
                     :if-does-not-exist :create
                     :element-type 'unsigned-byte)
    (mapcar (lambda (x) (write-byte x f)) bytes)))
