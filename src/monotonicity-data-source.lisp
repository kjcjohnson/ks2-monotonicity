;;;;
;;;; A source for monotonicity data about a problem
;;;;
(in-package #:com.kjcjohnson.ks2.monotonicity)

;;;
;;; Protocol
;;;
(defgeneric monotonicity-type (data-source chc identifier)
  (:documentation "Returns :INCREASING, :DECREASING, :CONSTANT, or NIL"))

(defgeneric monotonicity-gfa-intervals (data-source descriptor nt)
  (:documentation "Gets all GFA intervals for INPUT-STATE and DESCRIPTOR"))

;;;
;;; Datatypes
;;;
(defclass monotonicity-data-source ()
  ((head-data :accessor %head-data
              :type hash-table
              :documentation "A hash of head name to order information")
   (chc-data :accessor %chc-data
             :type hash-table
             :documentation "A hash of CHC ID to monotonicity information")
   (gfa-data :accessor %gfa-data
             :documentation "GFA results"))
  (:documentation "A source for information about monotonicity"))

(defclass always-increasing-data-source ()
  ()
  (:documentation "A mock data source that is always monotonically increasing"))

;;;
;;; Implementations
;;;
(defmethod monotonicity-type ((ds always-increasing-data-source) chc identifier)
  (declare (ignore ds))
  (check-type chc chc:chc)
  (if (and (eql (chc:name (chc:constructor chc)) (smt:ensure-identifier "$ite"))
           (eql identifier (smt:ensure-identifier "b")))
      nil
      :increasing))

(defmethod monotonicity-type ((ds monotonicity-data-source) chc identifier)
  (check-type chc chc:chc)
  (let ((chc-entry (gethash (chc:id chc) (%chc-data ds))))
    (unless (= 1 (hash-table-count chc-entry))
      ;; TODO: fully support multiple output variables
      ;;   For now, ensure that they all have the same monotonicity
      (loop with type = nil
            for mapping in (*:hash-table-values chc-entry)
            if (null type)
              do (unless (eql :constant (gethash identifier mapping))
                   (setf type (gethash identifier mapping)))
            else do (unless (or (eql type (gethash identifier mapping))
                                (eql :constant (gethash identifier mapping)))
                      (error "Multiple outputs with different directions!"))))
    (let ((mapping (first (*:hash-table-values chc-entry))))
      (and mapping (gethash identifier mapping)))))

(defun %parse-head-order (head-name var-hash context)
  "Parses orders from VAR-HASH for a CHC with head HEAD-NAME. In the case that VAR-HASH
is a string, not a hash, applies the compound tuple order named by VAR-HASH to all
output variables for the given head."
  (let ((order-hash (make-hash-table)))
    (flet ((order-setter (var order)
             "Sets order for VAR in ORDER-HASH to ORDER"
             (setf (gethash (smt:ensure-identifier var) order-hash)
                   (order-for-id order))))
      (etypecase var-hash
        (hash-table
         (maphash #'order-setter var-hash))
        (string
         (if (string= var-hash "RegexImplies")
             (loop for of in (chc:output-formals (semgus:lookup-head head-name context))
                   do (order-setter of "BoolImplies"))
             (error "Unknown compound order: ~a" var-hash)))))
    (values (smt:ensure-identifier head-name)
            order-hash)))

(defun %parse-all-head-orders (obj-hash context)
  "Parses the orders block from the JSON object hash"
  (let ((orders-hash (make-hash-table)))
    (maphash #'(lambda (head-name var-hash)
                 (multiple-value-bind (head orders)
                     (%parse-head-order head-name var-hash context)
                   (setf (gethash head orders-hash) orders)))
             (gethash "orders" obj-hash))
    orders-hash))

(defun %parse-chc-monotonicity (chc-hash context)
  "Parses a single CHC's monotonicity direction data"
  (let ((dirs (make-hash-table))
        (id (smt:ensure-identifier (gethash "chcId" chc-hash))))
    (maphash #'(lambda (output-var child-vars)
                 (if (hash-table-p child-vars)
                     (setf (gethash (smt:ensure-identifier output-var) dirs)
                           (let ((cdirs (make-hash-table)))
                             (maphash
                              #'(lambda (var value)
                                  (setf (gethash (smt:ensure-identifier var) cdirs)
                                        (str:string-case value
                                          ("Increasing" :increasing)
                                          ("Decreasing" :decreasing)
                                          ("Constant" :constant)
                                          ("None" nil)
                                          (otherwise (error "Invalid: ~a" value)))))
                              child-vars)
                             cdirs))
                     ;; Compound tuple orders
                     (let ((chc (semgus:lookup-chc id context)))
                       ;; Ugh. Loop over each output variable
                       (loop for output-se across (chc:output-symbols chc)
                             for output = (chc:symbol-name output-se)
                             for cdirs = (make-hash-table)
                             unless (gethash output dirs)
                             do ;; Loop over each child relation
                                (loop for rel in (chc:body chc)
                                      do (loop for actual in (chc:output-actuals rel)
                                               do (setf (gethash actual cdirs)
                                                        (str:string-case child-vars
                                                          ("Increasing" :increasing)
                                                          ("Decreasing" :decreasing)
                                                          ("Constant" :constant)
                                                          ("None" nil)
                                                          (otherwise
                                                           (error "Invalid: ~a"
                                                                  child-vars))))))
                                (setf (gethash output dirs) cdirs)))))

             (gethash "monotonicityDirection" chc-hash))
    (values id dirs)))

(defun %parse-all-chc-monotonicity (obj-hash context)
  "Parses the monotonicity data from the JSON object hash"
  (let ((mono-hash (make-hash-table)))
    (loop for chc across (gethash "monotonicity" obj-hash)
          do (multiple-value-bind (id directions)
                 (%parse-chc-monotonicity chc context)
               (setf (gethash id mono-hash) directions)))
    mono-hash))

(defclass gfa-result-state ()
    ((descriptor :accessor descriptor
                 :initarg :descriptor
                 :type symbol
                 :documentation "The descriptor for the input state for this result")
     (input :accessor input
            :initarg :input
            :type smt:state
            :documentation "The input state for this result")
     (intervals :accessor intervals
                :initarg :intervals
                :type list
                :documentation "The intervals from this GFA")))

(defclass gfa-result-interval ()
  ((descriptor :accessor descriptor
               :initarg :descriptor
               :type symbol
               :documentation "The descriptor for the CHC head for this result")
   (non-terminal :accessor non-terminal
                 :initarg :non-terminal
                 :type g:non-terminal
                 :documentation "The non-terminal for the GFA result")
   (lower-bound :accessor lower-bound
                :initarg :lower-bound
                :type smt:state
                :documentation "The lower bound for this interval")
   (upper-bound :accessor upper-bound
                :initarg :upper-bound
                :type smt:state
                :documentation "The upper bound for this interval"))
  (:documentation "An interval result from GFA"))

(defmethod monotonicity-gfa-intervals ((ds monotonicity-data-source) descriptor nt)
  ;; We have to do some inversion of the data...
  (let ((result-hash (make-hash-table)))
    (dolist (result-state (%gfa-data ds))
      (let ((desc-hash (gethash (descriptor result-state) result-hash)))
        (unless desc-hash
          (setf desc-hash (make-hash-table))
          (setf (gethash (descriptor result-state) result-hash) desc-hash))

        (let ((state-list (gethash (input result-state) desc-hash)))

          (loop for interval in (intervals result-state)
                when (and (eql (non-terminal interval) nt)
                          (eql (descriptor interval) descriptor))
                  do (push interval state-list))
          (setf (gethash (input result-state) desc-hash) state-list))))
    result-hash))

(defun %parse-input-value (var val-string descriptor context)
  "Parses an input value string VAL-STRING for variable VAR"
  (let ((head (semgus:lookup-head descriptor context))
        sort)
    (loop for ix in (chc:input-indices head)
          when (eql var (elt (chc:formals head) ix))
            do (setf sort (elt (chc:signature head) ix))
               (return))
    (unless sort
      (error "Unknown input variable name: ~a for descriptor: ~a" var descriptor))
    (?:match sort
      ((smt:bool-sort)
        (str:string-case (str:downcase val-string)
         ("true" (smt:call-smt "true"))
         ("false" (smt:call-smt "false"))
         (otherwise (error "Unknown Boolean value: ~a" val-string))))
      ((smt:int-sort)
       (parse-integer val-string))
      ((smt:string-sort)
       val-string)
      (_ (error "Unsupported input state sort: ~a" sort)))))

(defun %parse-gfa-input-state (input-hash descriptor context)
  "Parses an input state entry from GFA results"
  (smt:make-state
    (loop for var-str being the hash-keys of input-hash using (hash-value val-str)
          for var = (smt:ensure-identifier var-str)
          for val = (%parse-input-value var val-str descriptor context)
          collecting (cons var val))))

(defun %parse-gfa-bound (bound-hash head-orders descriptor)
  "Parses BOUND-HASH into an SMT state"
  (smt:make-state
   (loop for var-str being the hash-keys of bound-hash using (hash-value val-str)
         for var = (smt:ensure-identifier var-str)
         for order = (gethash var (gethash descriptor head-orders))
         for val = (order-parse-bound order val-str)
         collecting (cons var val))))

(defun %parse-gfa-result (result-hash head-orders context)
  "Parses a result entry from the GFA results hash"
  (let* ((descriptor (smt:ensure-identifier (gethash "descriptor" result-hash)))
         (non-terminal (g:lookup-non-terminal context
                                              (gethash "nonterminal" result-hash)))
         (lower (%parse-gfa-bound (gethash "lower" result-hash)
                                  head-orders descriptor))
         (upper (%parse-gfa-bound (gethash "upper" result-hash)
                                  head-orders descriptor)))
    (make-instance 'gfa-result-interval
                   :descriptor descriptor
                   :non-terminal non-terminal
                   :lower-bound lower
                   :upper-bound upper)))

(defun %parse-gfa-state (obj-hash head-orders context)
  "Parses a GFA state"
  (let* ((descriptor (smt:ensure-identifier (gethash "descriptor" obj-hash)))
         (input-state (%parse-gfa-input-state (gethash "input" obj-hash)
                                              descriptor context))
         (intervals nil))

    (loop for result across (gethash "results" obj-hash)
          do (push (%parse-gfa-result result head-orders context) intervals))
    (make-instance 'gfa-result-state
                   :descriptor descriptor
                   :input input-state
                   :intervals intervals)))

(defun %parse-all-gfa (obj-hash head-orders context)
  "Parses the grammar flow analysis information from the hash OBJ-HASH"
  (let ((g-flow (gethash "grammarFlow" obj-hash)))
    (if (vectorp g-flow)
        (loop for gfa-state across g-flow
              collect (%parse-gfa-state gfa-state head-orders context))
        (progn
          (format
           *trace-output*
           "~&WARNING: GFA data corrupt; expected vector but got: ~a. Skipping.~%"
           (type-of g-flow))
          nil))))

(defmethod initialize-instance :after ((ds monotonicity-data-source)
                                       &key json-file context)
  "Initializes a data source from a JSON file with a SemGuS context CONTEXT"
  (let ((obj (jzon:parse json-file)))
      (let* ((head-orders (%parse-all-head-orders obj context))
             (chc-directions (%parse-all-chc-monotonicity obj context))
             (gfa-results (%parse-all-gfa obj head-orders context)))
        (setf (%chc-data ds) chc-directions)
        (setf (%head-data ds) head-orders)
        (setf (%gfa-data ds) gfa-results)
        gfa-results)))
