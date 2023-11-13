;;;;
;;;; Monotonicity processor
;;;;
(in-package #:com.kjcjohnson.ks2.monotonicity)

(defvar *monotonicity-data* nil "Monotonicity data")

(semgus:register-load-processor :monotonicity-processor)

(defun add-identifier-piece (id new-piece)
  "Adds an indexed piece to an identifier"
  (smt:ensure-identifier (list (smt:identifier-smt id) new-piece)))

(defun interval-chc-head-name (head)
  "Gets the name of an interval CHC head from the concrete CHC"
  (interval-descriptor (chc:name head)))

(defun interval-descriptor (descriptor)
  "Gets the interval descriptor"
  (add-identifier-piece descriptor "Interval"))

(defun var-lb (identifier)
  (add-identifier-piece identifier "Lower"))

(defun var-ub (identifier)
  (add-identifier-piece identifier "Upper"))

(defun generate-interval-head (head)
  (let* ((name (interval-chc-head-name head))
         (sig-length (1- (* 2 (length (chc:signature head)))))
         (signature (make-array sig-length
                                :element-type 'symbol
                                :initial-element nil))
         (roles (make-array sig-length
                            :element-type '(member :input :output :term :unknown)
                            :initial-element :unknown))
         (formals (make-array sig-length
                              :element-type 'symbol
                              :initial-element nil)))
    ;; Populate variables
    (loop with ix = 0
          for sort across (chc:signature head)
          for role across (chc:roles head)
          for formal across (chc:formals head)
          when (eql role :unknown)
            do (error "Cannot intervalify unknown role")
          when (eql role :term)
            do (setf (aref signature ix) sort)
               (setf (aref roles ix) role)
               (setf (aref formals ix) formal)
               (incf ix)
          when (member role '(:input :output))
            do (setf (aref signature ix) sort)
               (setf (aref roles ix) role)
               (setf (aref formals ix) (var-lb formal))
               (incf ix)
               (setf (aref signature ix) sort)
               (setf (aref roles ix) role)
               (setf (aref formals ix) (var-ub formal))
               (incf ix))

    (make-instance 'chc:head
                   :name name
                   :signature signature
                   :roles roles
                   :formals formals)))

(defun generate-interval-symbol-table (orig-chc)
  "Generates a symbol table for an interval CHC"
  (let ((head (chc:head orig-chc))
        inputs outputs term aux
        (ix 0))
    (flet ((make-se (name sort)
             (prog1
                 (make-instance 'chc:symbol-entry
                                :index ix
                                :sort sort
                                :name name)
               (incf ix))))
      (loop for sort across (chc:signature head)
            for role across (chc:roles head)
            for formal across (chc:formals head)
            when (eql role :input)
              do (push (make-se (var-lb formal) sort) inputs)
                 (push (make-se (var-ub formal) sort) inputs)
            when (eql role :output)
              do (push (make-se (var-lb formal) sort) outputs)
                 (push (make-se (var-ub formal) sort) outputs)
            when (eql role :term)
              do (setf term (make-se formal sort)))
      (loop for a across (chc:auxiliary-symbols orig-chc) do
        (push (make-instance 'chc:symbol-entry
                             :name (var-lb (chc:symbol-name a))
                             :sort (chc:symbol-sort a)
                             :index nil)
              aux)
        (push (make-instance 'chc:symbol-entry
                             :name (var-ub (chc:symbol-name a))
                             :sort (chc:symbol-sort a)
                             :index nil)
              aux))
      (make-instance 'chc:symbol-table
                     :inputs (apply #'vector inputs)
                     :outputs (apply #'vector outputs)
                     :term term
                     :auxiliary (apply #'vector aux)
                     :unclassified (apply #'vector nil)
                     :children (chc:child-symbols orig-chc)))))

(defun generate-extrema-guard (orig-chc)
  "Generates a guard against extrema"
  (let ((ub-guard nil)
        (lb-guard nil))
    (loop for body-rel in (chc:body orig-chc) do
      (loop with head = (chc:head body-rel)
            with orders = (orders-for-head head)
            for oix in (chc:output-indices head)
            for actual = (aref (chc:actuals body-rel) oix)
            for sort = (aref (chc:signature head) oix)
            for mono-type = (monotonicity-type *monotonicity-data* orig-chc actual)
            for order = (aref orders oix)
            when (order-extended? order)
              do (case mono-type
                   (:increasing
                    (push (smt:$apply (order-upper-extension-predicate order)
                                      (smt:variable (var-ub actual) sort))
                          ub-guard)
                    (push (smt:$apply (order-lower-extension-predicate order)
                                      (smt:variable (var-lb actual) sort))
                          lb-guard))
                   (:decreasing
                    (push (smt:$apply (order-lower-extension-predicate order)
                                      (smt:variable (var-ub actual) sort))
                          ub-guard)
                    (push (smt:$apply (order-upper-extension-predicate order)
                                      (smt:variable (var-lb actual) sort))
                          lb-guard)))
            when (null mono-type)
              do (push (smt:$not (smt:$apply (order-singleton-interval-predicate
                                              order sort)
                                             (smt:variable (var-lb actual) sort)
                                             (smt:variable (var-ub actual) sort)))
                       ub-guard)
                 (push (smt:$not (smt:$apply (order-singleton-interval-predicate
                                              order sort)
                                             (smt:variable (var-lb actual) sort)
                                             (smt:variable (var-ub actual) sort)))
                       lb-guard)))
    (values lb-guard ub-guard)))

(defun %gen-singleton-check (var sort order &key (invert nil))
  "Generates a singleton interval check for VAR with ORDER. If INVERT, nots the check."
  (let ((check (smt:$apply (order-singleton-interval-predicate order sort)
                           (smt:variable (var-lb var) sort)
                           (smt:variable (var-ub var) sort))))
    (if invert
        (smt:$not check)
        check)))

(defun %update-vars (expression update-fn)
  "Updates variables in ORIG-CHC's constraint according to UPDATE-FN"
  (smt:update-expression
   #'(lambda (expr context)
       (declare (ignore context))
       (?:match expr
         ((smt:var name :sort sort)
          (smt:variable (funcall update-fn name) sort))
         (otherwise
          expr)))
   expression))

(defun extract-non-monotonic-guards (orig-chc)
  "Extracts guards involving only non-monotonic variables"
  (let ((nm-guards nil)
        (constraint nil))
    ;;
    ;; Find guard clauses that only involve non-monotonic variables
    (if (smt:is-application? (chc:constraint orig-chc) "and")
        (loop for child in (smt:children (chc:constraint orig-chc))
              for vars = (smt::find-constants child)
              if (every #'(lambda (v) (and (null (monotonicity-type *monotonicity-data*
                                                                    orig-chc
                                                                    (smt:name v)))
                                           (not (find (smt:name v)
                                                      (chc:output-symbols orig-chc)
                                                      :key #'chc:symbol-name))))
                        vars)
                do (push child nm-guards)
              else
                do (push child constraint))
        (setf constraint (list (chc:constraint orig-chc))))
    ;;
    ;; Intervalize the guards
    (values
     (loop for guard in nm-guards
           for vars = (smt::find-constants guard)
           for checks = (loop for var in vars
                              for order = (order-for-var (smt:name var) orig-chc)
                              collect (%gen-singleton-check (smt:name var)
                                                            (smt:sort var)
                                                            order
                                                            :invert t))
           collect (apply #'smt:$or (append checks
                                            (list (%update-vars guard #'var-ub)))))
     (apply #'smt:$and constraint))))

(defun generate-interval-constraint (orig-chc)
  "Generates a new CHC constraint for interval semantics. Assumes +monotonic for now"
  (flet ((update-vars (constraint update-fn)
           "Updates variables in ORIG-CHC's constraint according to UPDATE-FN"
           (smt:update-expression
            #'(lambda (expr context)
                (declare (ignore context))
                (?:match expr
                  ((smt:var name :sort sort)
                   (smt:variable (funcall update-fn name) sort))
                  (otherwise
                   expr)))
            constraint))
         (output-top-setter ()
           "Creates an SMT expression that binds output variables to top"
           (let ((lb-setter nil)
                 (ub-setter nil))
             (loop with orders = (orders-for-head (chc:head orig-chc))
                   for output-se across (chc:output-symbols orig-chc)
                   for name = (chc:symbol-name output-se)
                   for ix = (chc:symbol-index output-se)
                   for sort = (chc:symbol-sort output-se)
                   for order = (aref orders ix)
                   do (multiple-value-bind (top-lb top-ub)
                          (order-top order sort)
                        (push (smt:$= (smt:variable (var-lb name) sort)
                                      (smt:make-native-literal top-lb))
                              lb-setter)
                        (push (smt:$= (smt:variable (var-ub name) sort)
                                      (smt:make-native-literal top-ub))
                              ub-setter)))
             (values (apply #'smt:$and lb-setter) (apply #'smt:$and ub-setter)))))

    (multiple-value-bind (nm-guards constraint)
        (extract-non-monotonic-guards orig-chc)
      (multiple-value-bind (lb-guard ub-guard)
          (generate-extrema-guard orig-chc)
        (multiple-value-bind (lb-setter ub-setter)
            (output-top-setter)
          (apply #'smt:$and
                 (append
                  nm-guards
                  (list
                   (smt:$or
                    (smt:$and (apply #'smt:$or lb-guard)
                              #+()(smt:make-native-break #'(lambda () ast::*exe-debug*))
                              lb-setter)
                    (update-vars constraint #'var-lb))
                   (smt:$or
                    (smt:$and (apply #'smt:$or ub-guard)
                              #+()(smt:make-native-break #'(lambda () ast::*exe-debug*))
                              ub-setter)
                    (smt:$and
                     (update-vars constraint #'var-ub)
                     #+()(smt:make-native-break (constantly t))))
                   #+()(smt:make-native-break (constantly t))))))))))

(defun generate-interval-chc (chc context)
  "Generates a new CHC for CHC in CONTEXT"
  (format t "Gen CHC: ~a (op: ~a)~%" chc (chc:name (chc:constructor chc)))
  (labels ((left-actual (monotonicity-type actual)
             "The name of the left actual based on ACTUAL"
             (case monotonicity-type
               (:increasing (var-lb actual))
               (:decreasing (var-ub actual))
               (otherwise (var-lb actual)))) ; Doesn't matter
           (right-actual (monotonicity-type actual)
             "The name of the right actual based on ACTUAL"
             (case monotonicity-type
               (:increasing (var-ub actual))
               (:decreasing (var-lb actual))
               (otherwise (var-ub actual)))) ; Doesn't matter
           (convert-body-rel (body-rel)
             "Converts a body relation for interval semantics"
             (let ((actuals (make-array (1- (* 2 (length (chc:actuals body-rel)))))))
               (loop with ix = 0
                     for actual across (chc:actuals body-rel)
                     for mono-type = (monotonicity-type *monotonicity-data* chc actual)
                     for role across (chc:roles (chc:head body-rel))
                     when (eql role :term)
                       do (setf (aref actuals ix) actual)
                          (incf ix)
                     when (member role '(:input :output))
                       do (setf (aref actuals ix) (left-actual mono-type actual))
                          (incf ix)
                          (setf (aref actuals ix) (right-actual mono-type actual))
                          (incf ix))

               (make-instance 'chc:relation
                              :head (semgus:lookup-head
                                     (interval-chc-head-name body-rel)
                                     context)
                              :actuals actuals))))
    (let* ((head (semgus:lookup-head (interval-chc-head-name (chc:head chc)) context))
           (body (map 'vector #'convert-body-rel (chc:body chc))))
      (make-instance 'chc:chc
                     :symbol-table (generate-interval-symbol-table chc)
                     :head head
                     :body body
                     :constraint (generate-interval-constraint chc)
                     :constructor (chc:constructor chc)
                     :data nil #+()(chc:data chc)))))

(defun generate-interval-semantics (context)
  (declare (type semgus:semgus-context context))
  ;; Build new head relations
  (let ((new-heads nil))
    (dolist (head (semgus:head-relations context))
      ;; Generate new signature. Should have a single term + double input/output vars
      (push (chc:name head) (gethash :concrete-descriptors (semgus:metadata context)))
      (push (generate-interval-head head) new-heads))
    (setf (gethash :interval-descriptors (semgus:metadata context))
          (map 'list #'chc:name new-heads))
    (setf (semgus:head-relations context)
          (nconc new-heads (semgus:head-relations context))))

  ;; Generate interval semantics for each CHC
  (let ((new-chcs nil))
    (dolist (chc (semgus:chcs context))
      (push (generate-interval-chc chc context) new-chcs))
    (setf (semgus:chcs context)
          (nconc new-chcs (semgus:chcs context))))
  context)

(defun fixup-root-relations (context)
  "Updates the root relations with interval versions"
  (let* ((root-rel-names (map 'list #'interval-chc-head-name
                              (semgus:root-relations context)))
         (new-roots (map 'list (*:rcurry #'semgus:lookup-head context)
                         root-rel-names)))
    (setf (semgus:root-relations context)
          (nconc new-roots (semgus:root-relations context)))
    (setf (gethash :abstraction (semgus:metadata context)) root-rel-names)))

(defun generate-interval-example (problem descriptor input-state output-state)
  "Generates an interval example from a given example"
  (flet ((order-contains-fn (order left-var right-var value)
           #'(lambda (os)
               (let ((left (smt:get-value os left-var))
                     (right (smt:get-value os right-var)))
                 (order-contains order left right value)))))
    (let* ((inputs nil)
           (output-fns nil)
           (head (semgus:lookup-head descriptor (semgus:context problem))))
      (loop with is = input-state
            for iv in (chc:input-formals head)
            for val = (smt:get-value is iv)
            do (push (cons (var-lb iv) val) inputs)
               (push (cons (var-ub iv) val) inputs))

      (loop with os = output-state
            with orders = (orders-for-head head)
            for oix in (chc:output-indices head)
            for ov = (aref (chc:formals head) oix)
            for order = (aref orders oix)
            for val = (smt:get-value os ov)
            if order
              do (push (order-contains-fn order (var-lb ov) (var-ub ov) val)
                       output-fns)
            else do (error "Not a known order!"))

      (make-instance 'spec:inductive-specification
                     :descriptor (interval-descriptor descriptor)
                     :input-state (smt:make-state inputs)
                     :predicate #'(lambda (os)
                                    (every (*:rcurry #'funcall os)
                                           output-fns))))))

(defun generate-interval-examples (problem)
  "Generates interval inductive examples"
  (let ((new-exs nil))
    (dolist (ex (spec:examples (semgus:specification problem)))

      (push (generate-interval-example problem
                                       (spec:descriptor ex)
                                       (spec:input-state ex)
                                       (spec:output-state ex))
            new-exs))
    (setf (semgus:specification problem)
          (make-instance 'spec:intersection-specification
                         :components
                         (list
                          (semgus:specification problem)
                          (make-instance 'spec:intersection-specification
                                         :components (nreverse new-exs)))))))

(defvar *use-gfa-for-holes* 'cl:null "Set to T, NIL, or CL:NULL")

(defun should-use-gfa-for-holes? ()
  (cond ((eql *use-gfa-for-holes* 'cl:null)
         t)
        ((not *use-gfa-for-holes*)
         nil)
        (t t)))

(defun make-interval-state (lower-state upper-state)
  "Makes an interval state from a lower and an upper bounding state"
  (let ((new-state nil))
    (loop for var in (smt:get-variables lower-state)
          for val = (smt:get-value lower-state var)
          for int-var = (var-lb var)
          do (push (cons int-var val) new-state))
    (loop for var in (smt:get-variables upper-state)
          for val = (smt:get-value upper-state var)
          for int-var = (var-ub var)
          do (push (cons int-var val) new-state))
    (smt:make-state new-state)))

(defun generate-top-hole-semantics (descriptor context)
  "Generates hole semantics for DESCRIPTOR that returns top"
  (let ((head (semgus:lookup-head descriptor context))
        (top-state nil))
    (loop with orders = (orders-for-head head)
          for oix in (chc:output-indices head)
          for order = (aref orders oix)
          for formal = (aref (chc:formals head) oix)
          for sort = (aref (chc:signature head) oix)
          if order
            do (multiple-value-bind (lb ub)
                   (order-top order sort)
                 (push (cons (var-lb formal) lb) top-state)
                 (push (cons (var-ub formal) ub) top-state))
          else do (error "Not a known order!"))
    (let ((top-state (smt:make-state top-state)))
      #'(lambda (is)
          (declare (ignore is))
          top-state))))

(defun generate-gfa-hole-semantics (descriptor nt)
  (let ((data (monotonicity-gfa-intervals *monotonicity-data* descriptor nt))
        (int-data (make-hash-table)))
    (maphash #'(lambda (desc v)
                 (let ((shash (make-hash-table)))
                   (maphash #'(lambda (k ints)
                                (setf (gethash (make-interval-state k k) shash)
                                      (map 'list
                                           #'(lambda (interval)
                                               (make-interval-state
                                                (lower-bound interval)
                                                (upper-bound interval)))
                                           ints)))
                            v)
                   (setf (gethash (interval-descriptor desc) int-data) shash)))
             data)
    #'(lambda (is)
        (declare (ignore is))
        (let* ((state-hash (gethash ast:*root-input-descriptor* int-data))
               (interval-list (gethash ast:*root-input-state* state-hash))
               (interval-count (length interval-list)))
          (cond
            ((= 1 interval-count)
             (first interval-list))
            ((zerop interval-count)
             (error "No hole semantics for: ~a,~a,~a,~a"
                    descriptor nt
                    ast:*root-input-descriptor* ast:*root-input-state*))
            (t
             (error "Multiple hole intervals!")))))))

(defun generate-hole-semantics-for-nt (descriptor nt context)
  (if (and (should-use-gfa-for-holes?)
           ;; We might not have GFA data for the problem, so just use top
           (< 0 (hash-table-count (monotonicity-gfa-intervals *monotonicity-data*
                                                              descriptor nt))))
      (generate-gfa-hole-semantics descriptor nt)
      (generate-top-hole-semantics descriptor context)))

(defun generate-hole-semantics (op-sem-map context)
  "Generates hole semantics"
  ;;
  ;; descriptor -> nt -> lambda(is)
  ;;
  ;; Loop over descriptors
  (dolist (descriptor (gethash :concrete-descriptors (semgus:metadata context)))
    (let* ((interval-descriptor (interval-descriptor descriptor))
           (dhash (gethash interval-descriptor op-sem-map)))
      (unless dhash
        (setf dhash (make-hash-table))
        (setf (gethash interval-descriptor op-sem-map) dhash))

      ;; Loop over non-terminals
      (let ((tt (chc:term-type (semgus:lookup-head descriptor context))))
        (dolist (nt (g:non-terminals-for-term-type context tt))
          (setf (gethash nt dhash)
                (generate-hole-semantics-for-nt descriptor nt context)))))))

(defvar *generate-interval-semantics* 'cl:null "Set to T, NIL, or CL:NULL")

(defun should-generate-interval-semantics? (context)
  "Checks if we should generate interval semantics"
  (cond
    ((null *generate-interval-semantics*)
     nil)
    ((eql *generate-interval-semantics* 'cl:null)
     (*:true
      (nth-value 1 (gethash :generate-interval-semantics (semgus:metadata context)))))
    (t
     t)))

(defun setup-monotonicity-data (context)
  "Generates monotonicity data"
  (flet ((derive-data-pathname (pathname)
           (make-pathname :type "json"
                          :name (str:concat (pathname-name pathname) ".mono")
                          :defaults pathname)))
    (let ((metadata-file
            (or (gethash :monotonicity-data-file (semgus:metadata context))
                (derive-data-pathname (semgus:path context)))))
      (format *trace-output* "Using monotonicity file: ~a~%" metadata-file)
      (setf *monotonicity-data* (make-instance 'monotonicity-data-source
                                               :json-file metadata-file
                                               :context context)))))

(defmethod semgus:on-context-load ((processor (eql :monotonicity-processor)) context)
  "Performs monotonicity post-processing on a loaded context"
  (setf *BV-ORDER-HACK* nil)
  (when (should-generate-interval-semantics? context)
    (setup-monotonicity-data context)
    (generate-interval-semantics context)
    (fixup-root-relations context)))

(defmethod semgus:on-operationalization-load ((processor (eql :monotonicity-processor))
                                              op-sem-map desc-map context)
  "Performs monotonicity post-processing by adding semantics for holes"
  (declare (ignore processor desc-map))
  (when (should-generate-interval-semantics? context)
    (generate-hole-semantics op-sem-map context)))

(defmethod semgus:on-problem-load ((processor (eql :monotonicity-processor)) problem)
  "Performs monotonicity post-processing on a loaded problem"
  (when (should-generate-interval-semantics? (semgus:context problem))
    (when (spec:is-pbe? (semgus:specification problem))
      (generate-interval-examples problem)) ;; We need CEGIS otherwise
    (format t "Generated interval semantics.~%")))
