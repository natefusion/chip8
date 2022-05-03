(eval-when (:compile-toplevel :execute)
  (ql:quickload :trivia)
  (use-package :trivia))

(defun parse (l)
  (eval (read-from-string (concatenate 'string "'(" l ")"))))

(defun flatten (l)
  (apply #'concatenate 'string l))

(defun make-sexp (s)
  (let ((trim (string-trim " " s)))
    (if (and (string/= (subseq trim 0 1) "(")
             (string/= (subseq trim 0 1) ")"))
        (concatenate 'string "(" trim ") ")
        (concatenate 'string trim " "))))

;; comment dont actually work, pls fix
(defun remove-blank (l)
  (remove-if
   (lambda (x) (or (string= (string-trim " " x) "")
                   (string= (subseq (string-trim " " x) 0 1) ";")))
     l))

(defun tokenize (x)
  (flatten
    (mapcar #'make-sexp
            (remove-blank (uiop/stream:read-file-lines x)))))

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
  (setf (gethash (cadr exp) (cadr env)) (caddr exp))
  nil)

(defun chip8-eval-label (exp env)
  (setf (gethash (cadr exp) (cadr env)) (car env))
  nil)

(defun chip8-eval-var (exp env)
  (let ((inner (gethash exp (cadr env)))
        (outer (caddr env)))
    (cond (inner inner)
          (outer (chip8-eval-var exp outer))
          (t exp))))

(defun rotate-main (exps)
  "Ensures that the code above 'lab main' is always at the end"
  (let ((main-label (loop :for x :in exps
                          :for pos :from 0
                          :if (equal '(proc main) (list (first x) (second x)))
                            :return pos)))
    (if main-label
        ;; defs should be kept at the beginning
        ;; everything else should be put at the end
        (let ((before-main
                (reduce (lambda (a b)
                          (if (or (def? a) (macro? a))
                              (push a (first b))
                              (push a (second b)))
                          b)
                        (reverse (nthcdr (- (length exps) main-label) (reverse exps)))
                        :initial-value (list nil nil)
                        :from-end t)))
          (append (car before-main)
                  (nthcdr main-label exps)
                  (cadr before-main)))
        (error "put main pls"))))

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

(defun process-labels (exps env)
  "Flattens list and processes unresolved labels"
  (cond
    ((null exps) nil)
    ((atom exps) (list exps))
    (t (mapcan (lambda (x) (process-labels (chip8-eval x env) env)) exps))))

(defun chip8-eval-file (exps env)
  (cond
    ((null exps) nil)
    (t (append (chip8-eval (first exps) env)
               (chip8-eval-file (rest exps) env)))))

(defun chip8-eval-macro (exp env)
  (let ((name (cadr exp))
        (args (caddr exp))
        (body (cdddr exp)))
    (setf (gethash name (cadr env))
          (eval `(lambda (&rest vars)
                   (let ((inner-env (make-env ',(copy-list env))))
                     (mapcar (lambda (arg var)
                               (setf (gethash arg (cadr inner-env)) var))
                             ',args vars)
                     (chip8-eval-file ',body inner-env))))))
  nil)

(defun chip8-eval-proc (exp env)
  (let ((name (cadr exp))
        (body (chip8-eval-file (cddr exp) env)))
    (chip8-eval `(lab ,name) env)
    (append body
            (unless (eq name 'main) (chip8-eval '(ret) env)))))

(defun chip8-eval-top (exps env)
  (process-labels (chip8-eval-file (rotate-main exps) env) env))

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
  (let ((label (first env))
        (loop-body (chip8-eval-file (rest exp) env)))
    (append
     (loop :for x :in loop-body
           :if (eq x 'BREAK)
             :append (chip8-eval `(JUMP ,(+ 4 (first env))) env)
           :else
             :collect x)
     (chip8-eval `(JUMP ,label) env))))

(defun chip8-eval-include (exp env)
  (let ((name (second exp))
        ;; silently does nothing if no numbers are given to include (bad!)
        (bytes (let ((x (chip8-eval-args-partial (cddr exp) env)))
                 (append x (when (oddp (length x)) '(0))))))
    (dolist (x bytes)
      (cond ((not (numberp x)) (error "Only numbers can be included"))
            ((> x 255) (error "cannot include numbers larger than 255 (#xFF)"))))
    (chip8-eval `(lab ,name) env)
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
  (incf (first env) 2)
  
  (let ((stripped-args
          (remove-if #'builtin-var? (chip8-eval-args-partial args env :eval-v t))))
    (if (not (null (remove-if #'numberp stripped-args)))
        (list (cons proc args))
        (combine-op
         stripped-args
         
         (match (append (list proc) (mapcar #'chip8-type args))
           ('(EQ V V) '(#x9000 #x48))
           ('(EQ V N) '(#x4000 #x8))
           ('(EQ V KEY) '(#xE0A1 #x8))
           
           ('(NEQ V KEY) '(#xE09E Ex81))
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
           (_ '(0 0)))))))



(defun make-env (&optional outer)
  (let ((inner (make-hash-table)))
    (setf (gethash 'EQ inner) #'emit-op)
    (setf (gethash 'NEQ inner) #'emit-op)
    (setf (gethash 'SET inner) #'emit-op)
    (setf (gethash 'ADD inner) #'emit-op)
    (setf (gethash 'OR inner) #'emit-op)
    (setf (gethash 'AND inner) #'emit-op)
    (setf (gethash 'XOR inner) #'emit-op)
    (setf (gethash 'SUB inner) #'emit-op)
    (setf (gethash 'SHR inner) #'emit-op)
    (setf (gethash 'SUBR inner) #'emit-op)
    (setf (gethash 'SHL inner) #'emit-op)
    (setf (gethash 'RAND inner) #'emit-op)
    (setf (gethash 'DRAW inner) #'emit-op)
    (setf (gethash 'BCD inner) #'emit-op)
    (setf (gethash 'WRITE inner) #'emit-op)
    (setf (gethash 'READ inner) #'emit-op)
    (setf (gethash 'CLEAR inner) #'emit-op)
    (setf (gethash 'RET inner) #'emit-op)
    (setf (gethash 'CALL inner) #'emit-op)
    (setf (gethash 'JUMP inner) #'emit-op)
    (setf (gethash 'JUMP0 inner) #'emit-op)
    (setf (gethash '+ inner) #'+)
    (setf (gethash '- inner) #'-)
    (setf (gethash '* inner) #'*)
    (setf (gethash '/ inner) #'/)
    (setf (gethash '% inner) #'mod)
    (setf (gethash '&& inner) #'logand)
    (setf (gethash '|| inner) #'logior)
    (setf (gethash '^ inner) #'logxor)
    (setf (gethash '<< inner) #'ash)
    (setf (gethash '>> inner) #'(lambda (x y) (ash x (- y))))
    (setf (gethash 'pow inner) #'expt)
    (setf (gethash 'min inner) #'min)
    (setf (gethash 'max inner) #'max)
    (setf (gethash '< inner) #'(lambda (x y) (if (< x y) 1 0)))
    (setf (gethash '<= inner) #'(lambda (x y) (if (<= x y) 1 0)))
    (setf (gethash '== inner) #'(lambda (x y) (if (= x y) 1 0)))
    (setf (gethash '!= inner) #'(lambda (x y) (if (/= x y) 1 0)))
    (setf (gethash '>= inner) #'(lambda (x y) (if (>= x y) 1 0)))
    (setf (gethash '> inner) #'(lambda (x y) (if (> x y) 1 0)))
    (setf (gethash '~ inner) #'lognot)
    (setf (gethash '! inner) #'(lambda (x) (if (zerop x) 1 0)))
    (setf (gethash 'sin inner) #'sin)
    (setf (gethash 'cos inner) #'cos)
    (setf (gethash 'tan inner) #'tan)
    (setf (gethash 'exp inner) #'exp)
    (setf (gethash 'log inner) #'log)
    (setf (gethash 'abs inner) #'abs)
    (setf (gethash 'sqrt inner) #'sqrt)
    (setf (gethash 'sign inner) #'(lambda (x) (if (plusp x) 1 -1)))
    (setf (gethash 'ceil inner) #'ceiling)
    (setf (gethash 'floor inner) #'floor)
    

    (setf (gethash 'BREAK inner) (lambda () '(BREAK)))

    (list #x200 inner outer)))
    
(defun chip8-compile (file)
  (chip8-eval-top
   (parse (tokenize file))
   (make-env)))

(defun chip8-write (bytes filename)
  (with-open-file (f filename
                     :direction :output
                     :if-exists :supersede
                     :if-does-not-exist :create
                     :element-type 'unsigned-byte)
    (mapcar (lambda (x) (write-byte x f)) bytes)))
