(deftype u8  () '(unsigned-byte 8))
(deftype u16 () '(unsigned-byte 16))

(defparameter +W+     64)
(defparameter +H+     32)
(defparameter +SCALE+ 20)
(defparameter +MEM+   #x1000)
;; (defconstant +START+ #x200)
(defparameter +FONT+ #(#xF0 #x90 #x90 #x90 #xF0   ; 0
                       #x20 #x60 #x20 #x20 #x70   ; 1
                       #xF0 #x10 #xF0 #x80 #xF0   ; 2
                       #xF0 #x10 #xF0 #x10 #xF0   ; 3
                       #x90 #x90 #xF0 #x10 #x10   ; 4
                       #xF0 #x80 #xF0 #x10 #xF0   ; 5
                       #xF0 #x80 #xF0 #x90 #xF0   ; 6
                       #xF0 #x10 #x20 #x40 #x40   ; 7
                       #xF0 #x90 #xF0 #x90 #xF0   ; 8
                       #xF0 #x90 #xF0 #x10 #xF0   ; 9
                       #xF0 #x90 #xF0 #x90 #x90   ; A
                       #xE0 #x90 #xE0 #x90 #xE0   ; B
                       #xF0 #x80 #x80 #x80 #xF0   ; C
                       #xE0 #x90 #x90 #x90 #xE0   ; D
                       #xF0 #x80 #xF0 #x80 #xF0   ; E
                       #xF0 #x80 #xF0 #x80 #x80)) ; F

(defun chip8-array (dimensions &key type)
  (make-array dimensions :element-type type))

(defun set-mem (chip &key game font)
  (with-slots (mem) chip
    (when font
      (loop for i below (length mem)
            for j below (length font)
            do (setf (aref mem i) (aref font j))))
    
    (when game
      (loop for i from +START+ below (length mem)
            for j below (length game)
            do (setf (aref mem i) (aref game j))))))

(defstruct chip8
  (mem (chip8-array +MEM+ :type 'u8))
  (v (chip8-array 16 :type 'u8))
  (i 0 :type u16)
  (pc +START+ :type u16)
  (dt 0 :type u8)
  (st 0 :type u8)
  (stack (chip8-array 16 :type 'u16))
  (sp 0 :type u8)
  (gfx (chip8-array (list +W+ +H+) :type 'u8))
  (waiting nil :type boolean)
  (keys (chip8-array 16 :type 'bit)))

(defun get-opcode (mem pc)
  (dpb (aref mem pc) (byte 8 8) (aref mem (1+ pc))))

(defun init-chip (filename)
  (let ((chip (make-chip8)))
    (set-mem chip :game (c8-compile filename) :font +FONT+)
    chip))

(defun emulate-cycle (chip8)
  (set-key chip8)
  (with-slots (opcode mem v i pc dt st stack sp gfx waiting keys) chip8
    (let* ((opcode (get-opcode mem pc))
           (nnn    (chop opcode 12))
           (nn     (chop opcode 8))
           (n      (chop opcode 4))
           (x      (chop opcode 4 8))
           (y      (chop opcode 4 4))
           (w      (chop opcode 4 12)))
      (incf pc 2)
      
      (match (list w x y n)
        ((0 0 #xE #x0) (setf gfx (chip8-array (list +W+ +H+) :type 'u8)))
        ((0 0 #xE #xE) (setf pc (aref stack sp)
                             sp (1- sp)))
        
        ((1 _ _ _) (setf pc nnn))
        ((2 _ _ _) (setf sp (1+ sp)
                         (aref stack sp) pc
                         pc nnn))
        
        ((3 _ _ _) (when   (= (aref v x) nn)         (incf pc 2)))
        ((4 _ _ _) (when  (/= (aref v x) nn)         (incf pc 2)))
        ((5 _ _ _) (when   (= (aref v x) (aref v y)) (incf pc 2)))
        
        ((6 _ _ _) (setf (aref v x) nn))
        ((7 _ _ _) (setf (aref v x) (chop (+ nn (aref v x)) 8)))
        
        ((8 _ _ 0) (setf (aref v x) (aref v y)))
        ((8 _ _ 1) (setf (aref v x) (logior (aref v x) (aref v y))))
        ((8 _ _ 2) (setf (aref v x) (logand (aref v x) (aref v y))))
        ((8 _ _ 3) (setf (aref v x) (logxor (aref v x) (aref v y))))
        
        ((8 _ _ 4) (let ((sum (+ (aref v x) (aref v y))))
                     (setf (aref v #xF) (if (> sum #xFF) 1 0)
                           (aref v x)   (chop sum 8))))

        ((8 _ _ 5) (let ((diff (- (aref v x) (aref v y))))
                     (setf (aref v #xF) (if (> diff 0) 1 0)
                           (aref v x)   (chop diff 8))))
        
        ((8 _ _ 6) (setf (aref v #xF) (logand (aref v x) 1)
                         (aref v x)   (ash (aref v y) -1)))

        ((8 _ _ 7) (let ((diff (- (aref v y) (aref v x))))
                     (setf (aref v #xF) (if (> diff #xFF) 1 0)
                           (aref v x)   (chop diff 8))))
        
        ((8 _ _ #xE) (setf (aref v #xF) (ash (aref v x) -7)
                           (aref v x)   (chop (ash (aref v y) 1) 8)))

        ((9 _ _ 0) (when (/= (aref v x) (aref v y)) (incf pc 2)))
        
        ((#xA _ _ _) (setf i nnn))
        ((#xB _ _ _) (setf pc (+ nnn (aref v 0))))
        ((#xC _ _ _) (setf (aref v x) (logand (random 255) nn)))
        
        ((#xD _ _ _) (dotimes (py n)
                       (dotimes (px 8)
                         (when (logbitp (- 7 px) (aref mem (+ i py)))
                           (let* ((x-coor (mod (+ px (aref v x)) +W+))
                                  (y-coor (mod (+ py (aref v y)) +H+))
                                  (pixel (aref gfx x-coor y-coor)))
                             (setf (aref gfx x-coor y-coor) (if (zerop pixel) 1 0)
                                   (aref v #xF) pixel))))))
        
        ((#xE _ #x9 #xE) (when (= 1 (bit keys (aref v x))) (incf pc 2)))
        ((#xE _ #xA #x1) (when (= 0 (bit keys (aref v x))) (incf pc 2)))
        
        ((#xF _ 0 7) (setf (aref v x) dt))
        
        ((#xF _ 0 #xA) (if-let (pos (position 1 keys))
                         (setf (aref v x) pos)
                         (setf waiting t)))
        
        ((#xF _ 1 #x5) (setf dt (aref v x)))
        ((#xF _ 1 #x8) (setf st (aref v x)))
        ((#xF _ 1 #xE) (setf i (chop (+ i (aref v x)) 16)))
        ((#xF _ 2 #x9) (setf i (* 5 (aref v x))))
        
        ((#xF _ 3 3) (setf (aref mem (+ i 0)) (truncate (mod (/ (aref v x) 100) 10))
                           (aref mem (+ i 1)) (truncate (mod (/ (aref v x) 10) 10))
                           (aref mem (+ i 2)) (truncate (mod (/ (aref v x) 1) 10))))

        ((#xF _ 5 5) (dotimes (a (1+ x)) (setf (aref mem (chop (+ a i) 16)) (aref v a))))
        ((#xF _ 6 5) (dotimes (a (1+ x)) (setf (aref v a) (aref mem (chop (+ a i) 16)))))
        
        (otherwise (error "Unknown opcode: #x~X~%W: ~X, X: ~X, Y: ~X, N: ~X"
                          opcode w x y n))))))

(defun draw-frame (chip)
  (raylib:with-drawing
    (raylib:clear-background raylib:+yellow+)
    
    (with-slots (v gfx i pc dt st opcode mem) chip
      ;; background
      (raylib:draw-rectangle (+ 0 (* +SCALE+ +W+)) 10 
                             (- *extra* 10) (- (* +SCALE+ +H+) 25)
                             raylib:+blue+)
      ;; shadow long
      (raylib:draw-rectangle (- (* +SCALE+ +W+) 10) 20
                             10 (- (* +SCALE+ +H+) 25)
                             raylib:+black+)
      ;; shadow wide
      (raylib:draw-rectangle (+ 0 (* +SCALE+ +W+)) (- (* +SCALE+ +H+) 15)
                             (- *extra* 20) 10
                             raylib:+black+)
      
      (raylib:draw-text
       (format nil (concatenate
                    'string
                    "V0: ~3D, V4: ~3D, V8: ~3D, VC: ~3D~%"
                    "V1: ~3D, V5: ~3D, V9: ~3D, VD: ~3D~%"
                    "V2: ~3D, V6: ~3D, VA: ~3D, VE: ~3D~%"
                    "V3: ~3D, V7: ~3D, VB: ~3D, VF: ~3D~%"
                    "~%I: ~3D~%PC: ~3D~%DT: ~3D~%ST: ~3D~%"
                    "~%Instruction:~%"
                    "Prev: ~A~%"
                    "Current: ~A~%"
                    "Next: ~A")
               (aref v 0) (aref v 4) (aref v 8) (aref v 12)
               (aref v 1) (aref v 5) (aref v 9) (aref v 13)
               (aref v 2) (aref v 6) (aref v 10) (aref v 14)
               (aref v 3) (aref v 7) (aref v 11) (aref v 15)
               i pc dt st
               (dump (get-opcode mem (- pc 2))) ; prev
               (dump (get-opcode mem pc)) ; current
               (dump (get-opcode mem (+ pc 2))))      ; next
       
       (+ 5 (* +SCALE+ +W+)) 11
       30
       raylib:+yellow+)

      (dotimes (x (array-dimension gfx 0))
        (dotimes (y (array-dimension gfx 1))
          (unless (zerop (aref gfx x y))
            (raylib:draw-rectangle (* x +SCALE+) (* y +SCALE+)
                                   +SCALE+ +SCALE+
                                   raylib:+blue+)))))))

(defun set-key (chip)
  (loop for key in (list raylib:+key-X+ raylib:+key-one+ raylib:+key-two+ raylib:+key-three+
                         raylib:+key-Q+ raylib:+key-W+ raylib:+key-E+ raylib:+key-A+
                         raylib:+key-S+ raylib:+key-D+ raylib:+key-Z+ raylib:+key-C+
                         raylib:+key-four+ raylib:+key-R+ raylib:+key-F+ raylib:+key-V+)
        for index from 0
        do (setf (bit (chip8-keys chip) index)
                 (if (raylib:is-key-down key)
                     (progn (setf (chip8-waiting chip) nil) 1)
                     0))))

(defstruct timing frame-time tickrate last origin)

(defun init-timing ()
  (let* ((frame-time (/ 1000 60))
         (last (get-internal-real-time))
         (origin (+ last (/ frame-time 2))))
    (make-timing :frame-time frame-time
                 :last last
                 :origin origin
                 :tickrate 10)))

(defun idle-loop (timing chip)
  (with-slots (frame-time tickrate last origin) timing
    (set-key chip)
    
    (incf last (- (get-internal-real-time) last))

    (with-slots (st dt gfx waiting) chip
      (loop repeat 2
            while (< origin (- last frame-time))
            do (loop repeat tickrate
                     while (not waiting)
                     do (emulate-cycle chip))

               (when (> dt 0) (decf dt))
               (when (> st 0) (decf st))
               (incf origin frame-time)))

    (draw-frame chip)))

(defparameter *extra* 520)

(defun c8-load (filename)
  (with-open-file (f filename :element-type 'unsigned-byte)
    (loop for byte = (read-byte f nil)
          while byte
          with vec = (make-array +MAX-SIZE+
                                 :element-type 'unsigned-byte
                                 :fill-pointer 0)
          do (if (< (fill-pointer vec) (array-total-size vec))
                 (vector-push byte vec)
                 (error "Your program is too big!"))
          finally (return vec))))

(defun chip8 (&key code binary)
  (let* ((chip (make-chip8))
         (timing (init-timing)))
    (set-mem chip :game (cond (code (c8-compile code))
                              (binary (c8-load binary))
                              (t (error "wowee enter code or binary pls")))
                  :font +FONT+)
    (raylib:with-window ((+ *extra* (* +SCALE+ +W+)) (* +SCALE+ +H+) (format nil "chip8 emulator | ~A" (if code code binary)))
      (raylib:set-target-fps 60)
      (loop until (raylib:window-should-close)
            ;; GOTCHA: raylib craps itself if with-drawing is not called
            do (if (raylib:is-key-down raylib:+key-p+)
                   (draw-frame chip)
                   (idle-loop timing chip))))))

(defun main ()
  (let ((command (second *posix-argv*))
        (filename (third *posix-argv*)))
    (cond ((string-equal command "--binary")
           (chip8 :binary filename))
          ((string-equal command "--code")
           (chip8 :code filename))
          (t (print "Malformed input: should be: '--binary filename' or '--code filename'")))))

