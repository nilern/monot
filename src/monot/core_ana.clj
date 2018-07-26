(ns monot.core-ana
  (:require [clojure.tools.analyzer.jvm :as ana]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]))

;;;; tools.analyzer Utils
;;;; ===============================================================================================

(defn- reduce-children [f acc ast]
  (if-let [child-names (:children ast)]
    (reduce (fn [acc child-name]
              (let [child (child-name ast)]
                (if (vector? child)
                  (reduce f acc child)
                  (f acc child))))
            ast child-names)
    acc))

(defn- map-children [f ast]
  (if-let [child-names (:children ast)]
    (reduce (fn [ast child-name]
              (let [child (child-name ast)]
                (if (vector? child)
                  (assoc ast child-name (mapv f child))
                  (assoc ast child-name (f child)))))
            ast child-names)
    ast))

(defn- walk [inner outer ast]
  (outer (map-children inner ast)))

(defn- postwalk [f ast]
  (walk (partial postwalk f) f ast))

;;;; Syntax Shim
;;;; ===============================================================================================

(defn ! [_] (assert false "monot.core-ana/! used outside monot.core-ana/in-monad"))

;;;; Monad Interface
;;;; ===============================================================================================

(defmulti pure (fn [monad-class value] monad-class))

(defprotocol FlatMap
  (flat-map [self f]))

;;;; Effect Analysis
;;;; ===============================================================================================

(defn- annotate-node-effects [node]
  (if (or (and (= (-> node :fn :op) :var) (= (-> node :fn :var) #'!))
          (reduce-children (fn [acc child] (or acc (::monadic child))) false node))
    (assoc node ::monadic true)
    node))

(def ^:private annotate-effects (partial postwalk annotate-node-effects))

;;;; Monadic Conversion
;;;; ===============================================================================================

;;; It's kind of like CPS conversion.

(defprotocol IsTrivial
  (trivial? [self]))

(defprotocol ContEmitter
  (continue-expr [self expr])
  (continue-computation [self computation]))

(deftype TailCont [monad-class-name]
  IsTrivial
  (trivial? [_] true)

  ContEmitter
  (continue-expr [_ expr] (assert false "unimplemented"))
  (continue-computation [_ computation] (assert false "unimplemented")))

(defn- convert [cont ast]
  (assert false "unimplemented"))

;;;; Syntax Extensions
;;;; ===============================================================================================

(defmacro in-monad [monad-class & body]
  (let [monad-class-name (gensym 'monad-class)
        locals (into {} (map (fn [[name _]] [name {:op :local, :form name, :name name}])) &env)
        analyzer-env (assoc (ana/empty-env) :locals locals)]
    `(let [~monad-class-name ~monad-class]
       ~(emit-form (convert (->TailCont monad-class-name)
                            (ana/analyze `(do ~@body) analyzer-env))))))
