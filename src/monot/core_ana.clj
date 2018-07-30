(ns monot.core-ana
  (:require [clojure.tools.analyzer.jvm :as ana]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]])
  (:import [clojure.lang IDeref]))

;;;; tools.analyzer Utils
;;;; ===============================================================================================

(defn- reduce-children [f acc ast]
  (if-let [child-names (:children ast)]
    (reduce (fn [acc child-name]
              (let [child (child-name ast)]
                (if (vector? child)
                  (reduce f acc child)
                  (f acc child))))
            acc child-names)
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

;;;; Monad Interface
;;;; ===============================================================================================

(defprotocol FlatMap
  (flat-map [self f]))

;;;; Workarounds
;;;; ===============================================================================================

(deftype MonadThunk [mvalue f]
  IDeref
  (deref [_] (flat-map mvalue f)))

(defn ! [_] (assert false "monot.core-ana/! used outside monot.core-ana/in-monad"))

;;;; Effect Analysis
;;;; ===============================================================================================

(def ^:private monadic? #(contains? % ::monadic))

(defn- annotate-node-effects [node]
  (if (or (and (= (-> node :fn :op) :var) (= (-> node :fn :var) #'!))
          (reduce-children (fn [acc child] (or acc (monadic? child))) false node))
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

(deftype NodeCont [orig-node                                ; The unconverted AST node
                   path]                                    ; Path to the subnode whose conversion this is waiting for
  IsTrivial
  (trivial? [_] false)

  ContEmitter
  (continue-expr [_ expr] (assert false "unimplemented"))
  (continue-computation [_ computation] (assert false "unimplemented")))

(deftype NamedCont [cont-ref]
  IsTrivial
  (trivial? [_] true)

  ContEmitter
  (continue-expr [_ expr] (assert false "unimplemented"))
  (continue-computation [_ computation] (assert false "unimplemented")))

(deftype TailCont [pure-ref]
  IsTrivial
  (trivial? [_] true)

  ContEmitter
  (continue-expr [_ expr] {:op       :invoke
                           :fn       pure-ref
                           :args     [expr]
                           :children [:fn :args]})
  (continue-computation [_ computation] computation))

(defn- continue [cont ast]
  (if (monadic? ast)
    (continue-computation cont ast)
    (continue-expr cont ast)))

(defmulti convert-monadic (fn [_cont ast] (:op ast)))

(defn- convert [cont ast]
  (if (monadic? ast)
    (convert-monadic cont ast)
    (continue-expr cont ast)))

;;;; Syntax Extensions
;;;; ===============================================================================================

(defmacro in-monad [pure & body]
  (let [pure-name (gensym 'pure)
        pure-atom (atom nil)
        pure-ref {:op          :local
                  :form        pure-name
                  :assignable? false
                  :name        pure-name
                  :local       :let
                  :atom        pure-atom}
        let-locals (into {} (map (fn [[name _]] [name {:op :local, :form name, :name name}])) &env)
        body-locals (assoc let-locals pure-name pure-ref)]
    (emit-form {:op       :let
                :bindings [{:op    :binding
                            :form  pure-name
                            :name  pure-name
                            :local :let
                            :init  (ana/analyze pure (assoc (ana/empty-env) :locals let-locals))}]
                :body     (->> (ana/analyze `(do ~@body) (assoc (ana/empty-env) :locals body-locals))
                               annotate-effects
                               (convert (->TailCont pure-ref)))
                :children [:bindings :body]})))
