(ns monot.core
  (:require [clojure.walk :refer [postwalk]]))

(defprotocol FlatMap
  (flat-map [self f]))

(def ^:private trivial? (complement seq?))

(def ^:private computation? (comp ::computation? meta))

(defn- annotate-computation [form]
  (with-meta form (assoc (meta form) ::computation? true)))

(defn- analyze-effects-1 [form]
  (if (and (seq? form)
           (or (= (first form) '!)
               (some computation? form)))
      (annotate-computation form)
    form))

(defn- analyze-effects [form]
  (postwalk analyze-effects-1 form))

(def ^{:private true, :dynamic true} pure)

(defprotocol ContEmitter
  (trivial-cont? [self])
  (continue-expr [self expr])
  (continue-computation [self computation]))

(defn- continue [cont form]
  (if (computation? form)
    (continue-computation cont form)
    (continue-expr cont form)))

(deftype FnCont [-continue-expr -continue-computation]
  ContEmitter
  (trivial-cont? [_] false)
  (continue-expr [_ expr] (-continue-expr expr))
  (continue-computation [_ computation] (-continue-computation computation)))

(defn- make-cont [continue-expr-fn]
  (->FnCont continue-expr-fn
            (fn [computation]
              (let [v (gensym 'v)]
                `(flat-map ~computation (fn [~v] ~(continue-expr-fn v)))))))

(deftype ComputationCont [inner]
  ContEmitter
  (trivial-cont? [_] false)
  (continue-expr [_ expr] (continue-computation inner expr))
  (continue-computation [_ computation] (continue-computation inner computation)))

(deftype NamedCont [name]
  ContEmitter
  (trivial-cont? [_] true)
  (continue-expr [_ expr] `(~name ~expr))
  (continue-computation [_ computation] `(flat-map ~computation ~name)))

(deftype TailCont []
  ContEmitter
  (trivial-cont? [_] true)
  (continue-expr [_ expr] `(~pure ~expr))
  (continue-computation [_ computation] computation))

(declare convert-if convert-do convert-call convert-args)

(defn- convert [form cont]
  (if (computation? form)
    (if (seq form)
      (case (first form)
        !  (do
             (assert (= (count form) 2))
             (convert (second form) (->ComputationCont cont)))
        if (convert-if form cont)
        do (convert-do form cont)
        (convert-call form cont))
      (assert false "unreachable"))
    (continue cont form)))

(defn convert-if [[_ condition then else] cont]
  (if (trivial-cont? cont)
    (convert condition
             (make-cont (fn [c] `(if ~c ~(convert then cont) ~(convert else cont)))))
    (let [k     (gensym 'k)
          v     (gensym 'v)
          cont* (->NamedCont k)]
      `(let [~k (fn [~v] ~(continue cont v))]
         ~(convert condition
                   (make-cont (fn [c] `(if ~c ~(convert then cont*) ~(convert else cont*)))))))))

(defn- convert-do [[_ & stmts :as form] cont]
  (case (count stmts)
    0 (convert nil cont)
    1 (convert (first stmts) cont)
    (convert-call form cont))) ; HACK and does not respect tail conts

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
                                 (if (trivial? arg)
                                   (convert-args (cons arg args) argfs cont)
                                   (let [a (gensym 'a)]
                                     `(let [~a ~arg]
                                        ~(convert-args (cons a args) argfs cont))))))))))

(defmacro in-monad [return & body]
  (binding [pure return]
    (-> `(do ~@body)
        analyze-effects
        (convert (->TailCont)))))
