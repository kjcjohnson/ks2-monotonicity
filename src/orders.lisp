;;;;
;;;; Definitions and protocols for orders
;;;;
(in-package #:com.kjcjohnson.ks2.monotonicity)

(defclass order ()
  ((name :reader name
         :initarg :name
         :type string
         :documentation "Name of this order"))
  (:documentation "An order."))

(defgeneric order-<= (order left right)
  (:documentation "Checks if LEFT is <= RIGHT, according to ORDER"))
;; TODO: how to handle incomparable? Deal with later.

(defgeneric order-top (order sort)
  (:documentation "Returns top of ORDER (for SORT) as (VALUES TOP-LB TOP-UB)"))

(defgeneric order-join (order arg1-lb arg1-ub arg2-lb arg2-ub)
  (:documentation "Takes the join of ARG1 and ARG2, according to ORDER")
  (:method (order arg1-lb arg1-ub arg2-lb arg2-ub)
    "Generic join, using the defined <= for the order"
    (values (if (order-<= order arg1-lb arg2-lb)
                arg1-lb
                arg2-lb)
            (if (order-<= order arg1-ub arg2-ub)
                arg2-ub
                arg1-ub))))

(defgeneric order-contains (order lower upper value)
  (:documentation "Checks if VALUE is between LOWER and UPPER, according to ORDER")
  (:method (order lower upper value)
    "Generic contains, using the defined <= for the order"
    (and (order-<= order lower value)
         (order-<= order value upper))))

(defgeneric order-extended? (order)
  (:documentation "Returns if ORDER is extended, that is, has extrema that are not
elements of the underlying type, e.g., +/- infinity for integers."))

(defgeneric order-extension (order value)
  (:documentation "Returns T if VALUE is an extended value in ORDER, NIL otherwise"))

(defgeneric order-upper-extension-predicate (order)
  (:documentation "Returns a predicate for checking for the upper extension of ORDER"))

(defgeneric order-lower-extension-predicate (order)
  (:documentation "Returns a predicate for checking for the lower extension of ORDER"))

(defgeneric order-singleton-interval-predicate (order sort)
  (:documentation "Returns a predicate for checking singleton intervals"))

(defgeneric order-singleton-interval (order lower upper)
  (:documentation "Checks if [LOWER, UPPER] is a singleton (non-extended) interval")
  (:method (order lower upper)
    "Generic singleton check, using the defined <= for the order"
    (and (not (order-extension order lower))
         (not (order-extension order upper))
         (order-<= order lower upper)
         (order-<= order upper lower))))

(defgeneric order-parse-bound (order val-string)
  (:documentation "Parses a bound value from VAL-STRING"))

;;;
;;; Boolean Implication
;;;
(defclass boolean-implication (order)
  ()
  (:default-initargs :name "Boolean Implication"))

(defmethod order-<= ((order boolean-implication) left right)
  "Boolean implication order."
  (declare (type boolean left right))
  (smt:call-smt "=>" left right))

(defmethod order-top ((order boolean-implication) sort)
  "Boolean implication interval top."
  (declare (ignore sort))
  (values (smt:call-smt "false")
          (smt:call-smt "true")))

(defmethod order-extended? ((order boolean-implication)) nil)

(defmethod order-extension ((order boolean-implication) value) nil)

(defparameter *boolean-implication-order* (make-instance 'boolean-implication)
  "The Boolean implication order")

(defmethod order-singleton-interval-predicate ((order boolean-implication) sort)
  "Core equality is good enough for Boolean implication intervals"
  (declare (ignore sort))
  (smt:$function
      "="
      (smt:*bool-sort* smt:*bool-sort*)
      smt:*bool-sort*))

(defmethod order-parse-bound ((order boolean-implication) val-string)
  (str:string-case (str:downcase val-string)
    ("true" (smt:call-smt "true"))
    ("false" (smt:call-smt "false"))
    (otherwise (error "Invalid bool bound value: ~a" val-string))))

;;;
;;; Integer Leq
;;;
(defclass integer-leq (order)
  ()
  (:documentation "Integers, extended to :+infinity and :-infinity")
  (:default-initargs :name "Integer Leq"))

(defparameter *integer-leq-order* (make-instance 'integer-leq)
  "The integer leq order")

(deftype extended-integer ()
  "Integers extended to positive and negative infinity"
  '(or integer (member :+infinity :-infinity)))

(defun +infinity? (x)
  "Checks if X is positive infinity"
  (eql x :+infinity))

(defun -infinity? (x)
  "Checks if X is negative infinity"
  (eql x :-infinity))

(defmethod order-<= ((order integer-leq) left right)
  "Integer leq order."
  (declare (type extended-integer left right))
  (cond ((+infinity? right) t)
        ((+infinity? left) nil)
        ((-infinity? left) t)
        ((-infinity? right) nil)
        (t (<= left right))))

(defmethod order-top ((order integer-leq) sort)
  "Integer leq interval top."
  (declare (ignore sort))
  (values :-infinity :+infinity))

(defmethod order-extended? ((order integer-leq)) t)

(defmethod order-extension ((order integer-leq) value)
  (or (+infinity? value) (-infinity? value)))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter +smt-+infinityp+ "__integer_leq_+_infinity_p")
  (defparameter +smt--infinityp+ "__integer_leq_-_infinity_p")
  (defparameter +smt-int-leq-singleton+ "__order_singleton_interval"))

(smt:defsmtfun #.+smt-+infinityp+ :native (value)
  "Checks if VALUE is +infinity"
  (+infinity? value))

(smt:defsmtfun #.+smt--infinityp+ :native (value)
  "Checks if VALUE is -infinity"
  (-infinity? value))

(smt:defsmtfun #.+smt-int-leq-singleton+ :native (lower upper)
  "Checks if LOWER and UPPER form a concrete singleton interval"
  (order-singleton-interval *integer-leq-order* lower upper))

(defmethod order-upper-extension-predicate ((order integer-leq))
  (smt:$function
      #.+smt-+infinityp+
      (smt:*int-sort*)
      smt:*bool-sort*))

(defmethod order-lower-extension-predicate ((order integer-leq))
  (smt:$function
      #.+smt--infinityp+
      (smt:*int-sort*)
      smt:*bool-sort*))

(defmethod order-singleton-interval-predicate ((order integer-leq) sort)
  (declare (ignore sort))
  (smt:$function
      #.+smt-int-leq-singleton+
      (smt:*int-sort* smt:*int-sort*)
      smt:*bool-sort*))

(defmethod order-parse-bound ((order integer-leq) val-string)
  (str:string-case (str:downcase val-string)
    ("infty" :+infinity)
    ("ninfty" :-infinity)
    (otherwise (parse-integer val-string))))

;;;
;;; Regular language subset
;;;
(defclass reglan-subset (order)
  ()
  (:default-initargs :name "Regular Language Subset"))

(defmethod order-<= ((order reglan-subset) left right)
  "Uncomputable. We'd have to do a subset construction on LEFT and RIGHT."
  (declare (ignore order left right))
  (error "Cannot compute <= for regular language subset order."))

(defmethod order-contains ((order reglan-subset) lower upper value)
  "Checks if VALUE, a string, is in the interval bounded by LOWER and UPPER. This is a
little tricky and hand-wavy. Technically, we should treat VALUE as a reglan expression.
But...is it actually called? HUHH"
  (declare (ignore order lower upper value))
  (error "Cannot compute contains for regular language subset order."))

(defmethod order-top ((order reglan-subset) sort)
  "Top values for regular languages"
  (declare (ignore sort))
  (values (smt:call-smt "re.none")
          (smt:call-smt "re.all")))

(defmethod order-extended? ((order reglan-subset)) nil)
(defmethod order-extension ((order reglan-subset) value) nil)

(defparameter *reglan-subset-order* (make-instance 'reglan-subset))

(defmethod order-singleton-interval-predicate ((order reglan-subset) sort)
  "Core equality works fine"
  (declare (ignore sort))
  (smt:$function "=" (smt:*reglan-sort* smt:*reglan-sort*) smt:*bool-sort*))

(defmethod order-parse-bound ((order reglan-subset) val-string)
  (let ((re (let ((*package* (find-package "COM.KJCJOHNSON.KS2.MONOTONICITY")))
              (read-from-string val-string))))
    (labels ((parse-regex (re)
               (?:match re
                 ('re.none
                  (smt:call-smt "re.none"))
                 ('re.allchar
                  (smt:call-smt "re.allchar"))
                 ('re.all
                  (smt:call-smt "re.all"))
                 ((list 're.* next)
                  (smt:call-smt "re.*" (parse-regex next)))
                 ((list 're.union left right)
                  (smt:call-smt "re.union" (parse-regex left) (parse-regex right)))
                 ((list 're.range left right)
                  (smt:call-smt "re.range" left right))
                 ((list 're.++ left right)
                  (smt:call-smt "re.++" (parse-regex left) (parse-regex right)))
                 ((list 'str.to_re str)
                  (smt:call-smt "str.to_re" str))
                 ((list 're.+ next)
                  (smt:call-smt "re.+" (parse-regex next)))
                 (_ (error "Cannot parse regex bound: ~a" re)))))
      (parse-regex re))))

;;;
;;; Bitvector implication
;;;
(defclass bit-vector-implication (order)
  ()
  (:default-initargs :name "Bit Vector Implication"))

(defparameter *bit-vector-implication-order* (make-instance 'bit-vector-implication))

(defmethod order-<= ((order bit-vector-implication) left right)
  "Checks if each element of LEFT implies RIGHT"
  (every #'(lambda (l r)
             (or (not (= 1 l)) (= 1 r)))
         left right))

(defmethod order-top ((order bit-vector-implication) sort)
  "Gets top for bit vector implication"
  (?:match sort
    ((smt:bv-sort width)
     (values (make-array width :element-type 'bit :initial-element 0)
             (make-array width :element-type 'bit :initial-element 1)))
    (_ (error "Apparently not a bit vector sort: ~a" sort))))

(defmethod order-extended? ((order bit-vector-implication)) nil)

(defmethod order-singleton-interval-predicate ((order bit-vector-implication) sort)
  "Core equality is good enough for Boolean implication intervals"
  (smt:$function
      "="
      (sort sort)
      smt:*bool-sort*))


;;;
;;; Bitvector less than or equal (saturating)
;;;
(defclass bit-vector-ule (order)
  ()
  (:default-initargs :name "Bit Vector ULE"))

(defparameter *bit-vector-ule-order* (make-instance 'bit-vector-ule))

(defmethod order-<= ((order bit-vector-ule) left right)
  "Checks if the bit vectors compare with ULE"
  (smt:call-smt "bvule" left right))

(defmethod order-top ((order bit-vector-ule) sort)
  "Gets top for bit vector implication"
  (?:match sort
    ((smt:bv-sort width)
     (values (make-array width :element-type 'bit :initial-element 0)
             (make-array width :element-type 'bit :initial-element 1)))
    (_ (error "Apparently not a bit vector sort: ~a" sort))))

(defmethod order-extended? ((order bit-vector-ule)) nil)

(defmethod order-singleton-interval-predicate ((order bit-vector-ule) sort)
  "Core equality is good enough for Boolean implication intervals"
  (smt:$function
      "="
      (sort sort)
      smt:*bool-sort*))

;;;
;;; Helpers
;;;
(defun orders-for-head (head)
  "Gets a vector of orders for variables in HEAD's signature"
  (declare (type chc:head head))
  (let ((head-data (gethash (chc:name head) (%head-data *monotonicity-data*)))
        (orders-array (make-array (length (chc:formals head)) :initial-element nil)))
    (assert head-data)
    (loop for formal across (chc:formals head)
          for sort across (chc:signature head)
          for ix from 0
          do (setf (aref orders-array ix)
                   (let ((order (gethash formal head-data)))
                     (if (null order) ; We apparently need orders for input vars o_O
                         (cond ((eql sort smt:*bool-sort*)
                                *boolean-implication-order*)
                               ((eql sort smt:*int-sort*)
                                *integer-leq-order*)
                               ((eql sort smt:*reglan-sort*)
                                *reglan-subset-order*)
                               (t nil))
                         order))))
    orders-array))

(defun order-for-var (var chc)
  "Gets an order for a particular VAR in CHC."
  ;; First, search child relations
  (loop for body-rel in (chc:body chc)
        for ix = (position var (chc:actuals body-rel) :test #'eql)
        when ix
          do (return-from order-for-var
               (aref (orders-for-head (chc:head body-rel)) ix)))
  ;; Then try the CHC head itself
  (*:when-let (ix (position var (chc:formals (chc:head chc)) :test #'eql))
    (return-from order-for-var
      (aref (orders-for-head (chc:head chc)) ix)))

  (error "Cannot find order for: ~a" var))

(defun order-for-id (id)
  "Gets an order object for ID, either a string or SMT identifier"
  (setf id (smt:ensure-identifier id))
  (cond
    ((eql id (smt:ensure-identifier "IntegerLeq"))
     *integer-leq-order*)
    ((eql id (smt:ensure-identifier "IntLeq"))
     *integer-leq-order*)
    ((eql id (smt:ensure-identifier "BoolImplies"))
     *boolean-implication-order*)
    ((eql id (smt:ensure-identifier "BoolImpl"))
     *boolean-implication-order*)
    ((eql id (smt:ensure-identifier "RegLanSubset"))
     *reglan-subset-order*)
    ((eql id (smt:ensure-identifier "BVImpl"))
     *bit-vector-implication-order*)
    ((eql id (smt:ensure-identifier "BVule"))
     *bit-vector-ule-order*)
    (t
     (error "Unknown order: ~a" (smt:identifier-string id)))))
