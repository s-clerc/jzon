(defpackage #:com.inuoe.jzon
  (:use #:cl)
  (:export
   ;; Deserialize
   #:parse
   ;; Serialize
   #:stringify

   ;; Extensible serialization
   #:coerced-fields
   #:coerce-key
   #:coerce-element

   ;; Types
   #:json-atom
   #:json-element

   ;; conditions
   #:json-error
   #:json-parse-error
   #:json-eof-error)
  (:import-from #:closer-mop)
  (:import-from #:introspect-environment)
  (:local-nicknames
   (#:ie #:introspect-environment)))

(in-package #:com.inuoe.jzon)

#++
(declaim (optimize (speed 3) (safety 0) (debug 0)))

(define-condition json-error (simple-error) ())
(define-condition json-parse-error (json-error)
  ((%line
    :initarg :line
    :reader %json-parse-error-line)
   (%column
    :initarg :column
    :reader %json-parse-error-column))
  (:report
   (lambda (c stream)
     (apply #'format stream (simple-condition-format-control c) (simple-condition-format-arguments c))
     (let ((line (%json-parse-error-line c))
           (column (%json-parse-error-column c)))
       (if (and line column)
           (format stream ", at line ~A, column ~A." (%json-parse-error-line c) (%json-parse-error-column c))
           (format stream ", position unavailable."))))))
(define-condition json-eof-error (json-parse-error) ())

(deftype json-atom ()
  `(or (eql t)
       (eql nil)
       (eql null)
       real
       string))

(deftype json-element ()
  `(or json-atom
       vector
       hash-table))

(declaim (type function *%pos-fn*))
(defvar *%pos-fn*)

(declaim (inline %raise))
(defun %raise (type format &rest args)
  (if (subtypep type 'json-parse-error)
      (multiple-value-bind (line column) (funcall *%pos-fn*)
        (error type :format-control format :format-arguments args :line line :column column))
      (error type :format-control format :format-arguments args)))

(declaim (type boolean *%allow-comments*))
(defvar *%allow-comments*)

(declaim (ftype (function (function) (values (or null character) &optional)) %peek %step)
         (inline %peek %step))
(defun %peek (peek)
  (declare (function peek))
  (values (the (or null character) (funcall peek))))

(defun %step (step)
  (declare (function step))
  (values (the (or null character) (funcall step))))

(defun %whitespace-p (char)
  (and (member char '(#\Space #\Linefeed #\Return #\Tab))
       t))

(defun %skip-whitespace (step)
  "Skip whitespace, and optionally comments, depending on `%*allow-comments*'
 Returns the next character."
  (flet ((skip-cpp-comment ()
           ;; Skip the second slash.
           (let ((c (%step step)))
             (case c
               ((nil)(%raise 'json-eof-error "End of input reading comment exepecting second slash"))
               (#\/ nil)
               (t (%raise 'json-parse-error "Unexpected input '/~A'" c))))

           ;; Skip rest of line or until EOF
           (loop :until (member (%step step) '(nil #\Linefeed #\Return)))))
    (loop :for char := (%step step)
          :do
             (cond
               ((null char)
                (return nil))
               ((%whitespace-p char))
               ((and (char= #\/ char) *%allow-comments*)
                (skip-cpp-comment))
               (t
                (return char))))))

(defun %control-char-p (c)
  "Returns true if `c' is a control character per RFC 8259."
  (declare (type character c))
  (<= #x00 (char-code c) #x1F))

(declaim (type (and string (not simple-string)) *%string-accum*))
(defvar *%string-accum*)

(defun %read-json-string (step)
  "Reads a JSON string step-wise using `step' until an unescaped double-quote.
 Returns a `simple-string' representing the string."
  (labels ((interpret (char)
             (cond
               ((char= #\\ char)
                (let ((escaped (%step step)))
                  (case escaped
                    ((nil) (%raise 'json-eof-error "Unexpected end of input after '\\' in string"))
                    ((#.(char "\"" 0) #\\ #\/) escaped)
                    (#\b #\Backspace)
                    (#\f #\Formfeed)
                    (#\n #\Linefeed)
                    (#\r #\Return)
                    (#\t #\Tab)
                    (#\u (read-unicode))
                    (t (%raise 'json-parse-error "Invalid escape sequence in string '\\~A'" escaped)))))
               ((%control-char-p char)
                (%raise 'json-parse-error "Unexpected control character in string '~A' (~A)" char (char-name char)))
               (t char)))
           (read-unicode ()
             ;; refer to ECMA-404, strings.
             (flet ((read-code-point ()
                      (the (unsigned-byte 32)
                           (loop :for pos :of-type (integer 0 4) :from 0 :below 4
                                 :for weight :of-type (integer 1 4096) := #.(expt 16 3) :then (ash weight -4)
                                 :for digit := (digit-char-p (%step step) 16)
                                 :do (unless digit (%raise 'json-parse-error "Invalid unicode constant in string"))
                                 :sum (the (unsigned-byte 32) (* digit weight)) :of-type (unsigned-byte 32))))
                    (expect-char (char)
                      (let ((c (%step step)))
                        (unless (char= char c)
                          (%raise 'json-parse-error "Expecting ~C, found ~C instead" char c)))))
               (let ((code-point (read-code-point)))
                 (declare (type (unsigned-byte 32) code-point))
                 (code-char
                  (if (<= #xD800 code-point #xDBFF)
                      (let ((utf-16-high-surrogate-pair code-point))
                        (expect-char #\\)
                        (expect-char #\u)
                        (let ((utf-16-low-surrogate-pair (read-code-point)))
                          (declare (type (unsigned-byte 32) utf-16-low-surrogate-pair))
                          (unless (<= #xDC00 utf-16-low-surrogate-pair #xDFFF)
                            (%raise 'json-parse-error "Unexpected UTF-16 surrogate pair: ~A and ~A"
                                    utf-16-high-surrogate-pair
                                    utf-16-low-surrogate-pair))
                          (+ #x010000
                             (ash (- utf-16-high-surrogate-pair #xD800) 10)
                             (- utf-16-low-surrogate-pair #xDC00))))
                      code-point))))))
    (let ((accum *%string-accum*))
      (setf (fill-pointer accum) 0)
      (loop :for next character := (or (%step step) (%raise 'json-eof-error "Encountered end of input inside string constant"))
            :until (char= #.(char "\"" 0) next)
            :do (vector-push-extend (interpret next) accum))
      (subseq accum 0))))

(defun %read-json-array (peek step read-string)
  "Reads a JSON array of elements until finding a closing brace.
 Returns a `simple-vector' of JSON values."
  (let ((c (%skip-whitespace step)))
    (case c
      ((nil) (%raise 'json-eof-error "End of input reading first array element"))
      (#\] (vector))
      (t
       (coerce
        (cons (%read-json-element peek step read-string c)
              (loop
                :do (let ((c (%skip-whitespace step)))
                      (case c
                        (#\, nil)
                        (#\] (loop-finish))
                        ((nil) (%raise 'json-parse-error "End of input in array"))
                        (t (%raise 'json-parse-error "Expected comma or ] in array, got '~A'" c))))
                :collect (%read-json-element peek step read-string (%skip-whitespace step))))
        'simple-vector)))))

(declaim (type function *%key-fn*))
(defvar *%key-fn*)

(defun %read-json-object (peek step read-string)
  (declare (type function read-string))
  (let ((accum (make-hash-table :test 'equal))
        (key-fn *%key-fn*))
    (flet ((read-key-value ()
             ;; Read quote
             (case (%skip-whitespace step)
               ((nil) (%raise 'json-eof-error "End of input in object. Expected key"))
               (#.(char "\"" 0) nil)
               (#\}
                (return-from read-key-value nil))
               (t (%raise 'json-parse-error "Expected key in object")))

             (let ((key (funcall key-fn (funcall read-string))))
               (case (%skip-whitespace step)
                 ((nil) (%raise 'json-eof-error "End of input in object. Expected colon after key '~A'" key))
                 (#\: nil)
                 (t (%raise 'json-parse-error "Expected colon after object key '~A'" key)))

               (setf (gethash key accum) (%read-json-element peek step read-string (%skip-whitespace step))))
             t))
      (when (read-key-value)
        (loop
          (case (%skip-whitespace step)
            ((nil) (%raise 'json-eof-error "End of input in object. Expecting comma"))
            (#\, nil)
            (#\} (return))
            (t (%raise 'json-parse-error "Expected comma in object")))
          (unless (read-key-value)
            (%raise 'json-parse-error "Expected \"key\": value after comma"))))
      accum)))

(defun %read-json-number (peek step c)
  "Reads an RFC 8259 number, starting with `c'."
  (flet ((digit09-p (c)
           (let ((val (- (char-code c) (char-code #\0))))
             (and (<= 0 val 9) val)))
         (digit19-p (c)
           (let ((val (- (char-code c) (char-code #\0))))
             (and (<= 1 val 9) val)))
         (ends-number-p (c)
           (or (%whitespace-p c)
               (member c '(#\) #\] #\} #\,)))))
    (macrolet ((takec (on-eof)
                 "Take the next character, `go'ing to `label' on EOF or end of token"
                 `(let ((c (%peek peek)))
                    (when (or (null c) (ends-number-p c))
                      (go ,on-eof))
                    (%step step)
                    c)))
      (prog ((int-sign 1)
             (int-val 0)
             (frac-val 0)
             (frac-len 0)
             (exp-sign 1)
             (exp-val 0))
         (declare (type (integer 0) int-val frac-val exp-val frac-len)
                  (type (member -1 1) int-sign exp-sign))
         (let ((c c))
           (when (char= c #\-)
             (setf int-sign -1)
             (setf c (takec :fail)))

           (when (char= c #\0)
             (case (takec :done-0)
               (#\.       (go :parse-frac))
               ((#\e #\E) (go :parse-exp))
               (t         (go :fail))))

           (let ((digit (digit19-p c)))
             (unless digit (go :fail))
             (setf int-val digit)
             (go :parse-int)))

       :done-0
         (return (if (plusp int-sign) 0 -0.0d0))

       :parse-int
         (let ((c (takec :done-int)))
           (when (char= c #\.)
             (go :parse-frac))
           (when (or (char= c #\e)
                     (char= c #\E))
             (go :parse-exp))
           (let ((digit (digit09-p c)))
             (unless digit (go :fail))
             (setf int-val (+ (* int-val 10) digit))))
         (go :parse-int)

       :done-int
         (return (* int-sign int-val))

       :parse-frac
         (let ((c (takec :fail)))
           (let ((digit (digit09-p c)))
             (unless digit (go :fail))
             (setf frac-val digit)
             (setf frac-len 1)))

       :parse-frac-loop
         (let ((c (takec :done-frac)))
           (when (or (char= c #\e)
                     (char= c #\E))
             (go :parse-exp))
           (let ((digit (digit09-p c)))
             (unless digit (go :fail))
             (setf frac-val (+ (* frac-val 10) digit))
             (incf frac-len)))
         (go :parse-frac-loop)

       :done-frac
         (return (* int-sign (+ int-val (/ frac-val (expt 10.d0 frac-len)))))

       :parse-exp
         (let ((c (takec :fail)))
           (case c
             (#\-
              (setf exp-sign -1)
              (setf c (takec :fail)))
             (#\+
              (setf c (takec :fail))))

           (let ((digit (digit09-p c)))
             (unless digit (go :fail))
             (setf exp-val digit)))

       :parse-exp-loop
         (let ((c (takec :done)))
           (let ((digit (digit09-p c)))
             (unless digit (go :fail))
             (setf exp-val (+ (* exp-val 10) digit))))
         (go :parse-exp-loop)

       :done
         (return
           (let ((exp-mult (expt 10d0 (* exp-sign exp-val))))
             (* int-sign
                (+ (* int-val exp-mult)
                   (/ (* frac-val exp-mult) (expt 10.d0 frac-len))))))
       :fail
         (return nil)))))

(defun %read-until-space (step)
  (coerce (loop :for c := (%step step)
                :while c
                :collect c)
          'string))

(defun %read-json-atom (peek step c)
  "Parse a non-string JSON atom and return its value.
 `c' is the lookahead character already read."
  (macrolet ((expect (string value)
               `(loop :for i :from 1 :below (length ,string)
                      :for expect-c := (aref ,string i)
                      :for c := (or (%step step)
                                    (%raise 'json-eof-error (format nil "End of input reading token '~A'. Expected '~A'" ,string expect-c)))
                      :unless (char= c expect-c)
                        :do (let ((token (concatenate 'string
                                                      (subseq ,string 0 i)
                                                      (string c)
                                                      (%read-until-space step))))
                              (%raise 'json-parse-error (format nil "Unexpected token '~A'" token)))
                      :finally
                      (return ,value))))
    (case c
      (#\f (expect "false" nil))
      (#\t (expect "true" t))
      (#\n (expect "null" 'null))
      (t
       ;; Try to read a number
       (or (%read-json-number peek step c)
           (%raise 'json-parse-error "Unrecognized character in JSON data"))))))

(declaim (type (integer 0) *%current-depth*))
(defvar *%current-depth*)

(declaim (type (or null (integer 1)) *%maximum-depth*))
(defvar *%maximum-depth*)

(defun %read-json-element (peek step read-string c)
  (declare (type function peek step read-string)
           (type (or null character) c))
  (case c
    ((nil) (%raise 'json-eof-error "Unexpected end of input"))
    (#.(char "\"" 0)   (funcall read-string))
    (#\[
     (let ((*%current-depth* (1+ *%current-depth*)))
       (when (and *%maximum-depth* (> *%current-depth* *%maximum-depth*))
         (%raise 'json-parse-error "Maximum depth exceeded"))
       (%read-json-array peek step read-string)))
    (#\{
     (let ((*%current-depth* (1+ *%current-depth*)))
       (when (and *%maximum-depth* (> *%current-depth* *%maximum-depth*))
         (%raise 'json-parse-error "Maximum depth exceeded"))
       (%read-json-object peek step read-string)))
    (t     (%read-json-atom peek step c))))

(macrolet ((def-make-string-fns (name type)
             `(defun ,name (in)
                "Create peek, step, and read-string functions for the string `in'."
                (declare (type ,type in))
                (let ((i 0))
                  (declare (type (integer 0 #.array-dimension-limit) i))
                  (let* ((peek (lambda () (when (< i (length in)) (aref in i))))
                         (step (lambda () (when (< i (length in)) (prog1 (aref in i) (incf i)))))
                         (read-string (lambda ()
                                        (let ((q-pos (position #.(char "\"" 0) in :start i)))
                                          (unless q-pos (%raise 'json-eof-error "Unexpected end of input reading string"))
                                          (cond
                                            ((null (find #\\ in :start i :end q-pos))
                                             ;; Fast path, just need to check for control chars
                                             (let ((control-char (find-if #'%control-char-p in :start i :end q-pos)))
                                               (when control-char
                                                 (%raise 'json-parse-error "Unexpected control character in string '~A' (~A)" control-char (char-name control-char))))
                                             (prog1 (subseq in i q-pos)
                                               (setf i (1+ q-pos))))
                                            (t
                                             ;; Otherwise we need to worry about escape sequences, unicode, etc.
                                             (%read-json-string step))))))
                         (pos (lambda ()
                                (loop :with line := 1
                                      :with col := 1
                                      :with cr := nil
                                      :for p :from 0 :below (1- i)
                                      :for c := (aref in p)
                                      :do
                                         (case c
                                           (#\Linefeed (incf line) (setf col 1))
                                           (t (incf col)))
                                      :finally
                                         (return (values line col))))))
                    (values peek
                            step
                            read-string
                            pos))))))
  (def-make-string-fns %make-fns-simple-string simple-string)
  (def-make-string-fns %make-fns-string (and string (not simple-string))))

(defun %make-fns-stream (in)
  "Create peek, step, and read-string functions for the stream `in'."
  (declare (type stream in))
  (let* ((peek (lambda () (peek-char nil in nil)))
         (step (lambda () (read-char in nil)))
         (read-string (lambda () (%read-json-string step)))
         (pos (lambda ()
                (block nil
                  (let ((pos (ignore-errors (file-position in))))
                    (unless (and pos (ignore-errors (file-position in 0)))
                      (return (values nil nil)))

                    (loop :with line := 1
                          :with col := 1
                          :with cr := nil
                          :for p :from 0 :below (1- pos)
                          :for c := (read-char in)
                          :do (case c
                                (#\Linefeed (incf line) (setf col 1))
                                (t (incf col)))
                          :finally
                             (file-position in pos)
                             (return (values line col))))))))
    (values peek
            step
            read-string
            pos)))

(defun %coerce-into (value type)
  (let ((exp-type (ie:typexpand type)))
    (cond
      ((eq exp-type  'nil)
       (error "Cannot coerce to empty type ~A" type))
      ((eq exp-type 't)
       value)
      ((eq exp-type 'null)
       (unless (eq value 'null)
         (error "Cannot coerce '~A' to ~A" value type))
       nil)
      ((subtypep exp-type 'number)
       (coerce
        (cond
          ((simple-string-p value)
           (multiple-value-bind (peek step) (%make-fns-simple-string value)
             (%read-json-number peek step (%step step))))
          ((stringp value)
           (multiple-value-bind (peek step) (%make-fns-string value)
             (%read-json-number peek step (%step step))))
          (t value))
        type))
      ((or (eq exp-type 'cons)
           (and (listp exp-type)
                (eq (car exp-type) 'cons)))
       (unless (and (vectorp value) (not (stringp value)))
         (error "Cannot coerce '~A' to '~A'" value type))
       (labels ((recurse (i type acc)
                  (cond
                    ((eq type 'null)
                     (unless (= (length value) i)
                       (error "bad len"))
                     (nreverse acc))
                    ((not (or (eq type 'cons)
                              (and (listp type)
                                   (eq (first type) 'cons))))
                     (unless (= (length value) (1+ i))
                       (error "bad len"))
                     (let ((ret (nreverse acc)))
                       (setf (cdr (last ret)) (%coerce-into (aref value i) type))
                       ret))
                    (t
                     (multiple-value-bind (car cdr)
                         (cond
                           ((eq type 'cons)
                            (values '* '*))
                           ((and (listp type) (eq (car type) 'cons))
                            (values (second type) (third type)))
                           (t (error "impossible")))
                       (let ((car (if (eq car '*) t (ie:typexpand car)))
                             (cdr (if (eq cdr '*) t (ie:typexpand cdr))))
                         (recurse (1+ i) cdr (cons (%coerce-into (aref value i) car) acc))))))))
         (recurse 0 exp-type nil)))
      ((let ((designator (if (atom exp-type) exp-type (car exp-type))))
         (or (eq designator 'array)
             (eq designator 'simple-array)
             (eq designator 'bit-vector)
             (eq designator 'simple-bit-vector)
             (eq designator 'string)
             (eq designator 'simple-string)
             (eq designator 'base-string)
             (eq designator 'simple-base-string)
             (eq designator 'vector)
             (eq designator 'simple-vector)))
       (unless (vectorp value)
         (error "Cannot coerce '~A' to '~A'" value type))
       (let* ((normalized (if (atom exp-type) (list exp-type) exp-type))
              (designator (first normalized))
              (elt-type
                (ecase designator
                  ((array simple-array vector)
                   ;; Note - handle nil typed array (eg array that can hold nothing)
                   (if (cdr normalized) (second normalized) '*))
                  ((bit-vector simple-bit-vector)
                   'bit)
                  ((base-string simple-base-string)
                   'base-char)
                  ((string simple-string)
                   'character)
                  ((simple-vector)
                   '*)))
              (elt-type (if (eq elt-type '*) t elt-type))
              (coerced-elements (map 'vector (if (stringp value)
                                                 (lambda (elt) (%coerce-into (string elt) elt-type))
                                                 (lambda (elt) (%coerce-into elt elt-type)))
                                     value))
              (dimensions (third normalized)))
         (coerce
          (cond
            ((null dimensions)
             (unless (zerop (length value))
               (error "Cannot coerce '~A' to '~A'." value type))
             (make-array nil :element-type elt-type))
            ((and (or (eq designator 'array)
                       (eq designator 'simple-array))
                   (and (listp dimensions)
                        (not (null (cdr dimensions)))
                        (every #'integerp dimensions)))
              ;; Multidimensional with fixed size
             (make-array dimensions :displaced-to coerced-elements))
            (t
             coerced-elements))
          type)))
      ((or (eq type 'base-char)
           (eq type 'character)
           (eq type 'extended-char)
           (eq type 'standard-char))
       (coerce
        (etypecase value
          (string    value)
          (json-atom (stringify value))
          (t         value))
        type))
      ((subtypep type 'logical-pathname)
       (logical-pathname (etypecase value
                           (string    value)
                           (json-atom (stringify value))
                           (t         value))))
      ((subtypep type 'pathname)
       (values (parse-namestring (etypecase value
                                   (string    value)
                                   (json-atom (stringify value))
                                   (t         value)))))
      ((eq type 'keyword)
       (let ((name (etypecase value
                     (string    value)
                     (json-atom (stringify value)))))
         (intern name 'keyword)))
      ((or (subtypep type 'null)
           (subtypep type 'boolean)
           (subtypep type 'sequence)
           (subtypep type 'hash-table))
       (coerce value type))
      ((symbolp type)
       (let ((class (find-class type)))
         (etypecase value
           (hash-table
            (let (;; plist of :initarg form slot/values for `make-instance'
                  (initarg-slots-plist ())
                  ;; alist of (slotd . value) for `(setf cmop:slot-value-using-class)'
                  (set-value-slots-alist ()))
              (declare (dynamic-extent initarg-slots-plist set-value-slots-alist))
              (c2mop:ensure-finalized class)
              (dolist (slot (c2mop:class-slots class))
                (let* ((name (symbol-name (c2mop:slot-definition-name slot)))
                       (name (if (some #'lower-case-p name) name (string-downcase name))))
                  (multiple-value-bind (value value-p) (gethash name value)
                    (when value-p
                      (let ((coerce-value (%coerce-into value (c2cl:slot-definition-type slot)))
                            (slot-initargs (c2mop:slot-definition-initargs slot)))
                        (cond
                          (slot-initargs
                           (push coerce-value initarg-slots-plist)
                           (push (first slot-initargs) initarg-slots-plist))
                          (t
                           (push (cons slot coerce-value) set-value-slots-alist))))))))
              (let ((instance (apply #'make-instance class initarg-slots-plist)))
                (loop :for (slot . value) :in set-value-slots-alist
                      :do (setf (c2mop:slot-value-using-class class instance slot) value))
                instance))))))
      ((listp type)
       (ecase (first type)
         (or
          (let ((types (rest type)))
            (dolist (type types (error "Coercing 'or' - '~A' is not any of ~{~A~^, ~}" value types))
              (multiple-value-bind (value errorp) (ignore-errors (%coerce-into value type))
                (unless errorp
                  (return value))))))
         (and
          ;; TODO handle subtypes (inherited class/struct) by ordering to most specialized:
          ;; eg to handle this case:
          ;; (defclass x ()
          ;;   (a))

          ;; (defclass y (x)
          ;;   (b))

          ;; (defclass z (y)
          ;;   (c))

          ;; (jzon:parse "{a : 0; b : 1; c : 2}" :type '(and x y z))
          (let* ((types (rest type))
                 (main-type (first types))
                 (coerced (%coerce-into value main-type))
                 (no-fits (remove coerced (rest types) :test #'typep)))
            (when no-fits
              (error "Coercing 'and' - Value '~A' coerced to '~A' via '~A' fails constraint for ~A" value coerced main-type no-fits))
            (values coerced no-fits)))))
      (t
       (error "Don't know how to coerce into '~A'" type)))))

(defun parse (in &key
                   (maximum-depth 128)
                   (allow-comments nil)
                   (type t)
                   key-fn)
  "Read a JSON value from `in', which may be a string, a stream, or a pathname.
 `:maximum-depth' controls the maximum depth of the object/array nesting
 `:allow-comments' controls whether or not single-line // comments are allowed.
 `:type' is the expected type of object to parse
 `:key-fn' is a function of one value which 'pools' object keys, or null for the default pool"
  (check-type maximum-depth (or (integer 1) null))
  (check-type key-fn (or null symbol function))
  (if (pathnamep in)
      (with-open-file (in in :direction :input :external-format :utf-8)
        (parse in :maximum-depth maximum-depth :allow-comments allow-comments :key-fn key-fn :type type))
      (multiple-value-bind (peek step read-string pos)
          (etypecase in
            (simple-string (%make-fns-simple-string in))
            (string (%make-fns-string in))
            (stream (%make-fns-stream in)))
        (declare (dynamic-extent peek step read-string pos))
        (let ((*%maximum-depth* maximum-depth)
              (*%allow-comments* (and allow-comments t))
              (*%string-accum* (make-array 32 :element-type 'character :adjustable t :fill-pointer 0))
              (*%key-fn* (or (and key-fn (if (functionp key-fn) key-fn (fdefinition key-fn)))
                             (let ((pool nil))
                               (declare (type list pool))
                               (lambda (key)
                                 (declare (type simple-string key))
                                 (or (find key pool :test (lambda (s1 s2)
                                                            (declare (type simple-string s1 s2))
                                                            (string= s1 s2)))
                                     (progn (push key pool)
                                            key))))))
              (*%current-depth* 0)
              (*%pos-fn* pos))
          (declare (dynamic-extent *%string-accum* *%key-fn* *%current-depth* *%pos-fn*))
          (%coerce-into
           (prog1 (%read-json-element peek step read-string (%skip-whitespace step))
             (or (null (%skip-whitespace step))
                 (%raise 'json-parse-error "Content after reading element")))
           type)))))

(macrolet ((%coerced-fields-slots (element)
             `(let ((class (class-of ,element)))
                (c2mop:ensure-finalized class)
                (mapcar (lambda (s)
                          (list (c2mop:slot-definition-name s)
                                (c2mop:slot-value-using-class class ,element s)
                                (c2mop:slot-definition-type s)))
                        (remove-if-not (lambda (s) (c2mop:slot-boundp-using-class class ,element s))
                                       (c2mop:class-slots class))))))
  (defgeneric coerced-fields (element)
    (:documentation "Return a list of key definitions for `element'.
 A key definition is a three-element list of the form
  (name value type)
 name is the key name and will be coerced if not already a string
 value is the value, and will be coerced if not a `json-element'
 type is a type for the key, in order to handle ambiguous `nil' interpretations")
    #+(or ccl clisp sbcl)
    (:method ((element structure-object))
      (%coerced-fields-slots element))
    (:method ((element standard-object))
      (%coerced-fields-slots element))))

(defgeneric coerce-key (key)
  (:documentation "Coerce `key' into a string designator, or `nil' if `key' is an unsuitable key.")
  (:method (key)
    (format nil "~A" key))
  (:method ((key symbol))
    (let ((name (symbol-name key)))
      (if (some #'lower-case-p name)
          name
          (string-downcase name))))
  (:method ((key string))
    key)
  (:method ((key character))
    (string key))
  (:method ((key integer))
    (format nil "~D" key)))

(defgeneric coerce-element (element coerce-key)
  (:documentation "Coerce `element' into a `json-element', using `coerce-key' in cases the result is a hash-table.")
  (:method (element coerce-key)
    (loop :with ret := (make-hash-table :test 'equal)
          :for (name value . type-cell) :in (coerced-fields element)
          :for type := (if type-cell (car type-cell) t)
          :for key := (funcall coerce-key name)
          :do
             (when key ; TODO - Should we error instead?
               (setf (gethash key ret)
                     (typecase value
                       (null
                        (cond
                          ((and (subtypep 'boolean type) (subtypep type 'boolean))
                           nil)
                          ((and (subtypep 'list type) (subtypep type 'list))
                           #())
                          (t
                           'null)))
                       (t value))))
          :finally (return ret)))
  (:method ((element (eql t)) coerce-key)
    t)
  (:method ((element null) coerce-key)
    nil)
  (:method ((element (eql 'null)) coerce-key)
    'null)
  (:method ((element number) coerce-key)
    element)
  (:method ((element symbol) coerce-key)
    (string element))
  (:method ((element real) coerce-key)
    element)
  ;; TODO replace with coercing multi-dimensional arrays
  ;;      as arrays of arrays rather than linearizing them
  (:method ((element array) coerce-key)
    (coerce (make-array (array-total-size element) :displaced-to element) 'simple-vector))
  (:method ((element vector) coerce-key)
    element)
  (:method ((element sequence) coerce-key)
    (declare (type (and (not list) (not vector)) element))
    (coerce element 'simple-vector))
  (:method ((element cons) coerce-key)
    ;; Try and guess alist/plist
    ;; TODO - this might be too hacky/brittle to have on by default
    (let* ((alist-keys (and (every #'consp element)
                            (loop :for (k . v) :in element
                                  :for key := (funcall coerce-key k)
                                  :unless key
                                    :return nil
                                  :collect key)))
           (plist-keys (and (null alist-keys)
                            (loop :for cell :on element :by #'cddr
                                  :for k := (car cell)
                                  :for key := (funcall coerce-key k)
                                  :unless (and (cdr cell)
                                               (or (symbolp k) (stringp k))
                                               key)
                                    :return nil
                                  :collect key))))
      (cond
        (alist-keys
         (loop :with ret := (make-hash-table :test 'equal)
               :for (k . v) :in element
               :for key :in alist-keys
               :do (setf (gethash key ret) v)
               :finally (return ret)))
        (plist-keys
         (loop :with ret := (make-hash-table :test 'equal)
               :for (k v . rest) :on element :by #'cddr
               :for key :in plist-keys
               :do (setf (gethash key ret) v)
               :finally (return ret)))
        ((listp (cdr element))
         ;; If it looks like a proper list, then consider it a list
         (coerce element 'simple-vector))
        (t
         ;; Otherwise consider it a 2-element tuple
         (vector (car element) (cdr element))))))
  (:method ((element sequence) coerce-key)
    (declare (type (and (not list) (not vector)) element))
    (coerce element 'simple-vector)))

(defun %stringify-atom (atom stream)
  (declare (type stream stream))
  (etypecase atom
    ((eql t)      (write-string "true" stream))
    ((eql nil)    (write-string "false" stream))
    ((eql null)   (write-string "null" stream))
    (integer      (format stream "~D" atom))
    ;; TODO - Double-check any edge-cases with ~F and if ~E might be more appropriate
    (real         (format stream "~F" atom))
    (string
     (write-char #.(char "\"" 0) stream)
     (loop :for c :across atom
           :do
              (case c
                ((#.(char "\"" 0) #\\)
                 (write-char #\\ stream)
                 (write-char c stream))
                (#\Backspace
                 (write-char #\\ stream)
                 (write-char #\b stream))
                (#\Formfeed
                 (write-char #\\ stream)
                 (write-char #\f stream))
                (#\Linefeed
                 (write-char #\\ stream)
                 (write-char #\n stream))
                (#\Return
                 (write-char #\\ stream)
                 (write-char #\r stream))
                (#\Tab
                 (write-char #\\ stream)
                 (write-char #\t stream))
                (t
                 (cond
                   ((%control-char-p c)
                    (format stream "\\u~4,'0X" (char-code c)))
                   (t
                    (write-char c stream))))))
     (write-char #.(char "\"" 0) stream))))

(declaim (inline %ensure-linear-stringify))
(defun %ensure-linear-stringify (element path stack)
  (if (rassoc element stack)
      (format nil "@recursive-ref__ROOT~{->~A~}" (cdr (nreverse (delete nil (cons path (mapcar #'car stack))))))
      element))

(defun %stringify (element stream coerce-element coerce-key path stack)
  "Stringify non-pretty."
  (declare (type stream stream)
           (type function coerce-element coerce-key)
           (type list stack)
           (dynamic-extent stack))
  (typecase element
    (json-atom (%stringify-atom element stream))
    (pathname  (write-string (namestring element) stream))
    (t
     (let ((element (%ensure-linear-stringify element path stack)))
       (typecase element
         (json-atom (%stringify-atom element stream))
         ((and vector (not string))
          (write-char #\[ stream)
          (unless (zerop (length element))
            (let ((stack (acons path element stack)))
              (declare (dynamic-extent stack))
              (%stringify (aref element 0) stream coerce-element coerce-key 0 stack)
              (loop :for i :from 1 :below (length element)
                    :do (write-char #\, stream)
                        (%stringify (aref element i) stream coerce-element coerce-key i stack))))
          (write-char #\] stream))
         (hash-table
          (write-char #\{ stream)
          (with-hash-table-iterator (iter element)
            (multiple-value-bind (more? key val) (iter)
              (when more?
                (let ((stack (acons path element stack)))
                  (declare (dynamic-extent stack))
                  (flet ((stringify-key-value (key value)
                           (let ((key-str (funcall coerce-key key)))
                             (unless (typep key-str '(or string character (and (not null) symbol)))
                               (error "Invalid key after coercion: '~A' -> '~A'" key key-str))
                             (%stringify-atom (string key-str) stream)
                             (write-char #\: stream)
                             (%stringify value stream coerce-element coerce-key key-str stack))))
                    (stringify-key-value key val)
                    (loop
                      (multiple-value-bind (more? key val) (iter)
                        (unless more? (return))
                        (write-char #\, stream)
                        (stringify-key-value key val))))))))
          (write-char #\} stream))
         (t
          (let ((coerced-element (funcall coerce-element element coerce-key)))
            (unless (typep coerced-element 'json-element)
              (error "Unknown value to stringify: '~A'" coerced-element))
            (%stringify coerced-element stream coerce-element coerce-key path (acons nil element stack)))))))))

(defun %needs-lf-separator (element stack)
  "For pretty-printing. Returns true if `element' should have a lf separator."
  (unless (position element stack)
    (let ((stack (cons element stack)))
      (declare (dynamic-extent stack))
      (typecase element
        ((and vector (not string))
         (some (lambda (elt) (%needs-lf-separator elt stack))
               element))
        (hash-table
         (or (> (hash-table-count element) 1)
             (block nil
               (maphash (lambda (k v)
                          (declare (ignore k))
                          (when (%needs-lf-separator v stack)
                            (return t)))
                        element))))))))

(defun %indent (stream separator depth)
  "Indent `stream' by outputting `separator' and then spaces for `depth'."
  (write-char separator stream)
  (dotimes (_ (* depth 2))
    (write-char #\Space stream)))

(defun %stringifyp (element stream depth coerce-element coerce-key path stack)
  "Stringify Pretty."
  (declare (type stream stream)
           (type function coerce-element coerce-key)
           (type list stack)
           (dynamic-extent stack))
  (typecase element
    (json-atom (%stringify-atom element stream))
    (pathname  (write-string (namestring element) stream))
    (t
     (let ((element (%ensure-linear-stringify element path stack)))
       (typecase element
         (json-atom (%stringify-atom element stream))
         ((and vector (not string))
          (write-char #\[ stream)
          (unless (zerop (length element))
            (let* ((needs-lf  (%needs-lf-separator element nil))
                   (separator (if needs-lf #\Linefeed #\Space))
                   (depth     (if needs-lf (1+ depth) 0))
                   (stack     (acons path element stack)))
              (declare (dynamic-extent stack))
              (%indent stream separator depth)
              (%stringifyp (aref element 0) stream depth coerce-element coerce-key 0 stack)
              (loop :for i :from 1 :below (length element)
                    :do (write-char #\, stream)
                        (%indent stream separator depth)
                        (%stringifyp (aref element i) stream depth coerce-element coerce-key i stack))
              (%indent stream separator (1- depth))))
          (write-char #\] stream))
         (hash-table
          (write-char #\{ stream)
          (with-hash-table-iterator (iter element)
            (multiple-value-bind (more? key val) (iter)
              (when more?
                (let* ((needs-lf  (%needs-lf-separator element nil))
                       (separator (if needs-lf #\Linefeed #\Space))
                       (depth     (if needs-lf (1+ depth) 0))
                       (stack     (acons path element stack)))
                  (declare (dynamic-extent stack))
                  (flet ((stringify-key-value (key value)
                           (%indent stream separator depth)
                           (let ((key-str (funcall coerce-key key)))
                             (unless (typep key-str '(or string character (and (not null) symbol)))
                               (error "Invalid key after coercion: '~A' -> '~A'" key key-str))
                             (%stringify-atom (string key-str) stream)
                             (write-char #\: stream)
                             (write-char #\Space stream)
                             (%stringifyp value stream depth coerce-element coerce-key key-str stack))))
                    (stringify-key-value key val)
                    (loop
                      (multiple-value-bind (more? key val) (iter)
                        (unless more? (return))
                        (write-char #\, stream)
                        (stringify-key-value key val))))
                  (%indent stream separator (1- depth))))))
          (write-char #\} stream))
         (t
          (let ((coerced-element (funcall coerce-element element coerce-key)))
            (unless (typep coerced-element 'json-element)
              (error "Unknown value to stringify: '~A'" coerced-element))
            (%stringifyp coerced-element stream depth coerce-element coerce-key path (acons nil element stack)))))))))

(defun stringify (element &key stream pretty (coerce-element #'coerce-element) (coerce-key #'coerce-key))
  "Serialize `element' into JSON.
 Returns a fresh string if `stream' is nil, nil otherwise.
  `:stream' like the `destination' in `format'
  `:pretty' if true, pretty-format the output
  `:coerce-element' is a function of two arguments, and is used to coerce an unknown value to a `json-element'
  `:coerce-key' is a function of one argument, and is used to coerce object keys into non-nil string designators

 see `coerce-element'
 see `coerce-key'"
  (flet ((stringify-to (stream)
           (if pretty
               (%stringifyp element stream 0 coerce-element coerce-key element nil)
               (%stringify element stream coerce-element coerce-key element nil))))
    (cond
      ((null stream)
       (with-output-to-string (stream)
         (stringify-to stream)))
      ((stringp stream)
       (unless (array-has-fill-pointer-p stream)
         (error 'type-error :datum stream :expected-type '(and vector (satisfies array-has-fill-pointer-p))))
       (with-output-to-string (stream stream)
         (stringify-to stream))
       nil)
      (t
       (let ((stream (etypecase stream
                       ((eql t) *standard-output*)
                       (stream stream))))
         (stringify-to stream))
       nil))))
