(defstruct state
  labels
  subroutines
  instructions
  data)

(defun make-name (name num)
  (read-from-string (format nil "~A~X" name num)))

(defun dump (state opcode pc)
  (with-slots (labels subroutines data) state
    (let* ((nnn (chop opcode 12))
           (nn  (chop opcode 8))
           (n   (chop opcode 4))
           (x   (chop opcode 4 8))
           (xn (make-name 'v x))
           (y   (chop opcode 4 4))
           (yn (make-name 'v y))
           (w   (chop opcode 4 12))
           (lsize (/ (length labels) 2))
           (ssize (/ (length subroutines) 2))
           (dsize (/ (length data) 2)))
      (match (list w x y n)
        ((0 0 #xC _) `(SCROLL-DOWN ,n))
        ((0 0 #xE #x0) '(CLEAR))
        ((0 0 #xE #xE) '(RET))
        ((0 0 #xD _) `(SCROLL-UP ,n))
        ((0 0 #xF #xB) '(SCROLL-RIGHT))
        ((0 0 #xF #xC) '(SCROLL-LEFT))
        ((0 0 #xF #xD) '(EXIT))
        ((0 0 #xF #xF) '(HIRES))
        ((1 _ _ _)
         (if-let (x (getf labels nnn))
           `(JUMP ,x)
           (let ((name (cond ((= pc 512) 'main)
                             ((> pc nnn) (make-name 'loop- lsize))
                             (t (make-name 'label- lsize)))))
             (push `(\: ,name) labels)
             (push nnn labels)
             `(JUMP ,name))))
        ((2 _ _ _)
         (if-let (x (getf subroutines nnn)) 
           `(CALL ,x)
           (let ((name (make-name 'sub- ssize)))
             (push `(\: ,name) subroutines)
             (push nnn subroutines)
             `(CALL ,name))))
        ((3 _ _ _) `(NEQ ,xn ,nn))
        ((4 _ _ _) `(EQ ,xn ,nn))
        ((5 _ _ 0) `(NEQ ,xn ,yn))
        ((5 _ _ 2) `(WRITE ,xn ,yn))
        ((5 _ _ 3) `(READ ,xn ,yn))
        ((6 _ _ _) `(SET ,xn ,nn))
        ((7 _ _ _) `(ADD ,xn ,nn))
        ((8 _ _ 0) `(SET ,xn ,yn))
        ((8 _ _ 1) `(OR ,xn ,yn))
        ((8 _ _ 2) `(AND ,xn ,yn))
        ((8 _ _ 3) `(XOR ,xn ,yn))
        ((8 _ _ 4) `(ADD ,xn ,yn))
        ((8 _ _ 5) `(SUB ,xn ,yn))
        ((8 _ _ 6) `(SHR ,xn ,yn))
        ((8 _ _ 7) `(SUBN ,xn ,yn))
        ((8 _ _ #xE) `(SHL ,xn ,yn))
        ((9 _ _ 0) `(EQ ,xn ,yn))
        ((#xA _ _ _)
         (if-let (x (getf data nnn)) 
           `(SET I ,x)
           (let ((name (make-name 'data- dsize)))
             (push `(\: ,name) data)
             (push nnn data)
             `(SET I ,name))))
        ((#xB _ _ _) `(JUMP0 ,nnn))
        ((#xC _ _ _) `(SET ,xn RAND ,nn))
        ((#xD _ _ 0) `(DRAW ,xn ,yn))
        ((#xD _ _ _) `(DRAW ,xn ,yn ,n))
        ((#xE _ #x9 #xE) `(NEQ ,xn KEY))
        ((#xE _ #xA #x1) `(EQ ,xn KEY))
        ((#xF 0 0 0) '(SET I LONG))     ; 4 bytes, wat do
        ((#xF _ 0 1) `(PLANE ,xn))
        ((#xF 0 0 2) '(AUDIO))
        ((#xF _ 0 7) `(SET ,xn DT))
        ((#xF _ 0 #xA) `(SET ,xn KEY))
        ((#xF _ 1 #x5) `(SET DT ,xn))
        ((#xF _ 1 #x8) `(SET ST ,xn))
        ((#xF _ 1 #xE) `(ADD I ,xn))
        ((#xF _ 2 9) `(SET I HEX ,xn))
        ((#xF _ 3 0) `(SET I BIGHEX ,xn))
        ((#xF _ 3 3) `(BCD ,xn))
        ((#xF _ 3 #xA) `(SET PITCH ,xn))
        ((#xF _ 5 5) `(WRITE ,xn))
        ((#xF _ 6 5) `(READ ,xn))
        ((#xF _ 7 5) `(READ-FLAGS ,xn))
        ((#xF _ 8 5) `(WRITE-FLAGS ,xn))
        (_ opcode)))))

(defun c8-dasm (state f)
  (loop for one = (read-byte f nil)
        for two = (read-byte f nil)
        for pc from 512 by 2
        while one
        for opcode = (dpb one (byte 8 8) (if two two 0))
        collect (if (and one two)
                    (list (list one two) (dump state opcode pc))
                    (list (list one) one))))

(defun c8-read (filename)
  (let* ((state (make-state))
         (ins (with-open-file (f filename :element-type 'unsigned-byte)
                (c8-dasm state f))))
    (with-slots (labels subroutines data) state
      (loop for x in ins
            for pc from 512 by 2
            with data? = nil
            
            for lab = (let ((d (getf data pc))
                            (l (getf labels pc))
                            (s (getf subroutines pc)))
                        (cond (d (setf data? t) d)
                              (l (setf data? nil) l)
                              (s (setf data? nil) s)
                              (t nil)))
            
            do (when lab (print lab))
               (print (if data? `(include ,@(first x)) (second x)))))))


