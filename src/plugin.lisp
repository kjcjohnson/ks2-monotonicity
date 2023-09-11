;;;;
;;;; Solver plugin
;;;;
(in-package #:com.kjcjohnson.ks2.monotonicity)

(plug:defplugin monotonicity-plugin ()
  ()
  (:extends tdp/ks2:top-down-enumerator))

(defmethod s-api:solver-options append ((solver monotonicity-plugin))
  (list
   (s-api:make-solver-option
    :keyword :generate-interval-semantics
    :name "Generate Interval Semantics"
    :description "Whether to force generating interval semantics"
    :type :boolean)
   (s-api:make-solver-option
    :keyword :use-gfa-holes
    :name "Use GFA Holes"
    :description "Use GFA data for hole semantics"
    :type :boolean
    :default t)))

(defmethod s-api:initialize-solver ((solver monotonicity-plugin)
                                    &key
                                      (generate-interval-semantics nil gis-sup-p)
                                      use-gfa-holes
                                    &allow-other-keys)
  "Sets up interval semantics generation. Needs to happen before problem load."
  (if gis-sup-p
      (setf *generate-interval-semantics* generate-interval-semantics)
      (setf *generate-interval-semantics* 'cl:null))
  (setf *use-gfa-for-holes* use-gfa-holes))
