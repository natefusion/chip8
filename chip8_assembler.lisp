;;#!/usr/bin/sbcl --script
;;(load "/home/nathan/quicklisp/setup.lisp")
;;(ql:quickload :trivia)
;;(proclaim '(optimize (speed 3) (safety 0) (debug 0)))
;;(use-package :trivia)

;(defun chip8-setup ()
;;  (ql:quickload :trivia)
;; (use-package :trivia))

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

    (setf (gethash 'BREAK inner) (lambda () '(BREAK)))

    (list #x200 inner outer)))

(defun chip8-type (exp)
  (cond
    ((v? exp) 'V)
    ((builtin-var? exp) exp)
    (t 'N)))

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

(defun chip8-eval-ins (exp env)
  (funcall (chip8-eval (first exp) env)
           (first exp)
           (chip8-eval-args-partial (rest exp) env) env))

(defun chip8-eval-args-partial (args env &key eval-v)
  (mapcar (lambda (x)
            (if (and (v? x) eval-v)
                (chip8-eval-v? x)
                (chip8-eval x env)))
          args))

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

(defun def? (exp)
  (and (listp exp)
       (eq (first exp) 'DEF)))
  
(defun chip8-eval-def (exp env)
  (setf (gethash (cadr exp) (cadr env)) (caddr exp))
  nil)

(defun label? (exp)
  (and (listp exp)
       (eq (first exp) 'LAB)))

(defun chip8-eval-label (exp env)
  (setf (gethash (cadr exp) (cadr env)) (car env))
  nil)

(defun loop? (exp)
  (and (listp exp)
       (eq (first exp) 'LOOP)))

(defun chip8-eval-loop (exp env)
  (let ((label (list (first env)))
        (loop-body (chip8-eval-file (rest exp) env)))
   (append
     (loop :for x :in loop-body
           :if (eq x 'BREAK)
             :append (emit-op 'JUMP (list (+ 4 (car env))) env)
           :else
             :collect x)
     (emit-op 'JUMP label env))))
  
(defun var? (exp)
  (and (not (application? exp))
       (not (self-evaluating? exp))))

(defun chip8-eval-var (exp env)
  (let ((inner (gethash exp (cadr env)))
        (outer (caddr env)))
    (cond (inner inner)
          (outer (chip8-eval-var exp outer))
          (t exp))))

(defun application? (exp)
  (and (not (null exp))
       (listp exp)
       (not (def? exp))
       (not (label? exp))))

(defun chip8-eval-application (exp env)
  (apply (chip8-eval (first exp) env)
         (chip8-eval-args-partial (rest exp) env)))

(defun include? (exp)
  (and (listp exp)
       (eq (first exp) 'INCLUDE)))

(defun chip8-eval-include (exp env)
  (incf (car env) (length (remove-if-not #'numberp exp)))
  (chip8-eval-args-partial
   (if (= (mod (length (rest exp)) 2) 0)
       (rest exp)
       (append (rest exp) '(0)))
   env))

(defun macro? (exp)
  (and (listp exp)
       (eq (first exp) 'MACRO)))

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

(defun process-labels (exps env)
  "Flattens list and processes unresolved labels"
  (cond
    ((null exps) nil)
    ((atom exps) (list exps))
    (t (mapcan (lambda (x) (process-labels (chip8-eval x env) env)) exps))))

(defun rotate-main (exps)
  "Ensures that the code above 'lab main' is always at the end"
  (let ((main-label (position '(lab main) exps :test #'equal)))
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
                (cdr before-main))))))

(defun chip8-eval-top (exps env)
  (process-labels (chip8-eval-file (rotate-main exps) env) env))

(defun chip8-eval-file (exps env)
  (cond
    ((null exps) nil)
    (t (append (chip8-eval (car exps) env)
               (chip8-eval-file (rest exps) env)))))

(defun chip8-err (exp)
  (format t "You typed: ~a~%That was bad~%" exp))

(defun chip8-eval (exp env)
  (cond ((self-evaluating? exp) exp)
        ((def? exp) (chip8-eval-def exp env))
        ((label? exp) (chip8-eval-label exp env))
        ((var? exp) (chip8-eval-var exp env))
        ((loop? exp) (chip8-eval-loop exp env))
        ((include? exp) (chip8-eval-include exp env))
        ((macro? exp) (chip8-eval-macro exp env))
        ((ins? exp) (chip8-eval-ins exp env))
        ((application? exp) (chip8-eval-application exp env))
        (t (chip8-err exp))))

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

;;(defun main ()
;;  (cond
;;    ((>= (length *posix-argv*) 2)
;;     (format t "~a~%"
;;     (chip8-eval-top
;;       (parse (tokenize (cadr *posix-argv*)))
;;       (make-env))))
;;    (t nil)))

;;(main)
