;;;;
;;;; Monotonicity analysis
;;;;
(asdf:defsystem "com.kjcjohnson.ks2.monotonicity"
  :description "Monotonicity for top-down enumeration"
  :version "0.0.1"
  :author "Keith Johnson <quack@duck.systems>"
  :license "MIT"
  :depends-on ("com.kjcjohnson.ks2/solver-api"
               "com.kjcjohnson.synthkit/smt"
               "com.kjcjohnson.synthkit/semgus"
               "com.kjcjohnson.tdp/top-down-enum"
               "com.kjcjohnson.tdp/ks2"
               "systems.duck.plugboard"
               "com.inuoe.jzon"
               "str")
  :pathname "src"
  :serial t
  :components ((:file "package")
               (:file "orders")
               (:file "monotonicity-data-source")
               (:file "monotonicity")
               (:file "plugin")))
