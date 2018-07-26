(ns monot.core
  (:require [clojure.walk :refer [postwalk]]))

;;;;

(defprotocol FlatMap
  (flat-map [self f]))

;;;;

(def ^:private computation? (comp ::computation? meta))

(defn- annotate-computation [form]
  (with-meta form (assoc (meta form) ::computation? true)))

;;;;

(defn- analyze-effects-1 [form]
  (if (and (seq? form)
           (or (= (first form) '!)
               (some computation? form)))
    (annotate-computation form)
    form))

(defn- analyze-effects [form]
  (postwalk analyze-effects-1 form))

;;;;

(def ^{:private true, :dynamic true} pure)

(defprotocol IsTrivial
  (trivial? [self]))

(extend-protocol IsTrivial
  nil
  (trivial? [_] true)

  Object
  (trivial? [self] (not (seq? self))))

(defprotocol ContEmitter
  (continue-expr [self expr])
  (continue-computation [self computation]))

(deftype FnCont [-continue-expr -continue-computation]
  IsTrivial
  (trivial? [_] false)

  ContEmitter
  (continue-expr [_ expr] (-continue-expr expr))
  (continue-computation [_ computation] (-continue-computation computation)))

(deftype ComputationCont [inner]
  IsTrivial
  (trivial? [_] false)

  ContEmitter
  (continue-expr [_ expr] (continue-computation inner expr))
  (continue-computation [_ computation] (continue-computation inner computation)))

(deftype NamedCont [name]
  IsTrivial
  (trivial? [_] true)

  ContEmitter
  (continue-expr [_ expr] `(~name ~expr))
  (continue-computation [_ computation] `(flat-map ~computation ~name)))

(deftype TailCont []
  IsTrivial
  (trivial? [_] true)

  ContEmitter
  (continue-expr [_ expr] `(~pure ~expr))
  (continue-computation [_ computation] computation))

(defn- make-cont [continue-expr-fn]
  (->FnCont continue-expr-fn
            (fn [computation]
              (let [v (gensym 'v)]
                `(flat-map ~computation (fn [~v] ~(continue-expr-fn v)))))))

(defn- continue [cont form]
  (if (computation? form)
    (continue-computation cont form)
    (continue-expr cont form)))

(defn- trivializing [v f]
  (if (trivial? v)
    (f v)
    (let [x (gensym 'x)]
      `(let [~x ~v]
         ~(f x)))))

(defn- trivializing-cont [v f]
  (if (trivial? v)
    (f v)
    (let [k (gensym 'k)
          x (gensym 'x)
          cont* (->NamedCont k)]
      `(let [~k (fn [~x] ~(continue v x))]
         ~(f cont*)))))

(declare convert-if convert-do convert-call convert-args)

(defn- convert [form cont]
  (if (computation? form)
    (if (seq form)
      (case (first form)
        ! (do
            (assert (= (count form) 2))
            (convert (second form) (->ComputationCont cont)))
        if (convert-if form cont)
        do (convert-do form cont)
        (convert-call form cont))
      (assert false "unreachable"))
    (continue cont form)))

(defn- convert-if [[_ condition then else] cont]
  (trivializing-cont cont
                     (fn [cont]
                       (convert condition
                                (make-cont (fn [c]
                                             `(if ~c
                                                ~(convert then cont)
                                                ~(convert else cont))))))))

(defn- convert-do [[_ & stmts :as form] cont]
  (case (count stmts)
    0 (convert nil cont)
    1 (convert (first stmts) cont)
    (convert-call form cont)))                              ; HACK and does not respect tail conts

(defn- convert-call [[ff & argfs] cont]
  (convert ff
           (make-cont (fn [f]
                        (convert-args () argfs
                                      (->FnCont (fn [args]
                                                  (continue cont `(~f ~@(reverse args))))
                                                (fn [_] (assert false "unreachable"))))))))

(defn- convert-args [args argfs cont]
  (if (empty? argfs)
    (continue cont args)
    (let [[argf & argfs] argfs]
      (convert argf (make-cont (fn [arg]
                                 (trivializing arg
                                               (fn [arg]
                                                 (convert-args (cons arg args) argfs cont)))))))))

;;;;

(defmacro in-monad [return & body]
  (binding [pure return]
    (-> `(do ~@body)
        analyze-effects
        (convert (->TailCont)))))
