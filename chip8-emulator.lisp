(deftype u8  () '(unsigned-byte 8))
(deftype u16 () '(unsigned-byte 16))

(defconstant +CYCLES-PER-SECOND+ 500)
(defconstant +CYCLES-BEFORE-SLEEP+ 10)

(defconstant +W+     64)
(defconstant +H+     32)
(defconstant +SCALE+ 10)
(defconstant +MEM+   #x1000)
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
  (draw-flag nil :type boolean)
  (waiting nil :type boolean)
  (keys (chip8-array 16 :type 'bit)))

(defun init-chip (filename)
  (let ((chip (make-chip8)))
    (set-mem chip :game (c8-compile filename) :font +FONT+)
    chip))

(defmacro match (pattern &body clauses)
  `(cond
     ,@(mapcar
        (lambda (clause)
          (cons (flet ((ekual (x y) (or (equal x y) (equal x '_))))
                  (if (listp (car clause))
                      `(every ,#'ekual ',(car clause) ,pattern)
                      `(funcall ,#'ekual ',(car clause) ,pattern)))
           (cdr clause)))
        clauses)))

(defun chop (number size &optional (pos 0))
  (ldb (byte size pos) number))

(defun emulate-cycle (chip8)
  (with-slots (mem v i pc dt st stack sp gfx draw-flag waiting  keys) chip8
    (let* ((opcode (dpb (aref mem pc) (byte 8 8) (aref mem (1+ pc))))
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
                           (aref v x)   (ash (aref v y) 1)))

        ((9 _ _ 0) (when (/= (aref v x) (aref v y)) (incf pc 2)))
        
        ((#xA _ _ _) (setf i nnn))
        ((#xB _ _ _) (setf pc (+ nnn (aref v 0))))
        ((#xC _ _ _) (setf (aref v x) (logand (random 255) nn)))
        
        ((#xD _ _ _)
         (setf draw-flag t)
         (dotimes (py n)
           (dotimes (px 8)
             (when (logbitp px (aref mem (+ i py)))
               (let* ((x-coor (mod (+ px (aref v x)) +W+))
                      (y-coor (mod (+ py (aref v y)) +H+))
                      (pixel (aref gfx x-coor y-coor)))
                 (setf (aref gfx x-coor y-coor) (if (zerop pixel) 1 0)
                       (aref v #xF) pixel))))))
        
        ((#xE _ #x9 #xE) (when (= 1 (bit keys (aref v x))) (incf pc 2)))
        ((#xE _ #xA #x1) (when (= 0 (bit keys (aref v x))) (incf pc 2)))
        
        ((#xF _ 0 7) (setf (aref v x) dt))
        
        ((#xF _ 0 #xA) (if-let (pos (position-if (lambda (v) (= v 1)) keys))
                         (setf (aref v x) pos
                               waiting nil)
                         (setf waiting t)))
        
        ((#xF _ 1 #x5) (setf dt (aref v x)))
        ((#xF _ 1 #x8) (setf st (aref v x)))
        ((#xF _ 1 #xE) (setf i (chop (+ i (aref v x)) 16)))
        ((#xF _ 2 #x9) (setf i (chop (* 5 (aref v x)) 16)))
        
        ((#xF _ 3 3) (setf (aref mem (+ i 0)) (mod (/ (aref v x) 100) 10)
                           (aref mem (+ i 1)) (mod (/ (aref v x) 10) 10)
                           (aref mem (+ i 2)) (mod (/ (aref v x) 1) 10)))

        ((#xF _ 5 5) (dotimes (a (1+ x)) (setf (aref mem (+ a i)) (aref v a))))
        ((#xF _ 5 5) (dotimes (a (1+ x)) (setf (aref v a) (aref mem (+ a i)))))
        
        (otherwise (error "Unknown opcode: #x~X~%W: ~X, X: ~X, Y: ~X, N: ~X"
                          opcode w x y n))))))

(defun draw-frame (gfx renderer)
  (destructuring-bind (n m) (array-dimensions gfx)
    (dotimes (x n)
      (dotimes (y m)
        (let ((sx (* x +SCALE+))
              (sy (* y +SCALE+)))
          (if (zerop (aref gfx x y))
              (sdl2:set-render-draw-color renderer 255 255 255 255)
              (sdl2:set-render-draw-color renderer 0   0   0   255))
          (sdl2:with-rects ((x sx sy +SCALE+ +SCALE+))
            (sdl2:render-fill-rect renderer x)))))
    (sdl2:render-present renderer)))

(defun set-key (chip keycode key-state)
  (setf (bit (chip8-keys chip)
             (case keycode
               (:SCANCODE-1 #x1) (:SCANCODE-2 #x2)
               (:SCANCODE-3 #x3) (:SCANCODE-4 #xC)
               (:SCANCODE-Q #x4) (:SCANCODE-W #x5)
               (:SCANCODE-E #x6) (:SCANCODE-R #xD)
               (:SCANCODE-A #x7) (:SCANCODE-S #x8)
               (:SCANCODE-D #x9) (:SCANCODE-F #xE)
               (:SCANCODE-Z #xA) (:SCANCODE-X #x0)
               (:SCANCODE-C #xB) (:SCANCODE-V #xF)
               (otherwise (return-from set-key))))
        key-state))

(defmacro with-sdl2 ((window renderer) filename &body body)
  `(sdl2:with-init (:video)
     (sdl2:with-window (,window
                        :title (format nil "Chip8 Emulator | ~A" ,filename)
                        :w (* ,+SCALE+ ,+W+)
                        :h (* ,+SCALE+ ,+H+)
                        :flags '(:shown))
       (sdl2:with-renderer (,renderer ,window :index -1 :flags '(:accelerated))
         (sdl2:with-event-loop (:method :poll) ,@body)))))

(defun chip8 (game)
  (let* ((chip (make-chip8))
         (frame-time (/ 1000 60))
         (last (get-internal-real-time))
         diff
         (origin (+ last (/ frame-time 2)))
         (tickrate 20))
    (set-mem chip :game (c8-compile game) :font +FONT+)
    (with-sdl2 (window renderer) game
      (:quit () t)
      (:keydown (:keysym keysym) (set-key chip (sdl2:scancode keysym) 1))
      (:keyup   (:keysym keysym) (set-key chip (sdl2:scancode keysym) 0))
      (:idle ()
             (setf diff (- (get-internal-real-time) last)
                   last (+ last diff))
             
             (with-slots (st dt draw-flag gfx waiting) chip
               (loop for k from 0
                     while (and (< origin (- last frame-time)) (< k 2))
                     do (loop for z from 0
                              while (and (< z tickrate) (not waiting))
                              do (emulate-cycle chip))
                     do (incf origin frame-time))

               (when draw-flag
                 (draw-frame gfx renderer)
                 (setf draw-flag nil))

               (when (> st 0) (decf st))
               (when (> dt 0) (decf dt)))
             (sleep (/ frame-time 1000))))))

(defun main ()
  (if (= (length *posix-argv*) 2)
      (chip8 (second *posix-argv*))
      (print "Please enter a filename")))

