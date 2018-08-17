(ns monot.core
  (:require [clojure.tools.analyzer.jvm :as ana]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]])
  (:import [clojure.lang IDeref APersistentMap]))

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
                (assoc ast child-name (if (vector? child) (mapv f child) (f child)))))
            ast child-names)
    ast))

(defn- walk [inner outer ast]
  (outer (map-children inner ast)))

(defn- postwalk [f ast]
  (walk (partial postwalk f) f ast))

(defn- next-child-name [children child-name]
  (second (drop-while #(not= % child-name) children)))

(defn- subnode-with-path
  "Get the first subnode under `child-name` and its path or nil when `(= (get node child-name) [])`."
  [node child-name]
  (let [child (get node child-name)]
    (if (vector? child)
      (when (seq child)
        [(first child) [child-name 0]])
      [child [child-name]])))

(declare next-path)

(defn- next-subnode-with-path [node child-name]
  (or (subnode-with-path node child-name)
      (next-path node [child-name])))

(defn- next-path
  "The next subnode of `node` in evaluation order after `path` and its path or nil when no more subnodes remain."
  [{:keys [children] :as node} path]
  (case (count path)
    1 (let [child-name (first path)]
        (when-let [path*-head (next-child-name children child-name)]
          (next-subnode-with-path node path*-head)))
    2 (let [path* (update path 1 inc)]
        (if-let [child* (get-in node path*)]
          [child* path*]
          (recur node (subvec path 0 1))))))

(defn- first-path
  "The first subnode of `node` and its path or nil."
  [{:keys [children] :as node}]
  (when-let [child-name (first children)]
    (next-subnode-with-path node child-name)))

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

(defn- !-node? [node]
  (let [res (and (= (:op node) :invoke)
                 (= (-> node :fn :op) :var)
                 (= (-> node :fn :var) #'!))]
    (assert (or (not res) (= (count (:args node)) 1)))
    res))

;;;; Monadic Conversion
;;;; ===============================================================================================

;;; It's kind of like CPS conversion.

(defprotocol IsTrivial
  (trivial? [self]))

(extend-protocol IsTrivial
  APersistentMap
  (trivial? [{:keys [op]}]
    (case op
      (:const :local :quote :the-var) true
      false)))

(defn- trivializing [expr f]
  (if (trivial? expr)
    (f expr)
    (let [name (gensym 'v)
          aatom (atom nil)
          aexpr {:op          :local
                 :form        name
                 :name        name
                 :assignable? false
                 :local       :let
                 :atom        aatom}]
      {:op       :let
       :bindings [{:op       :binding
                   :form     name
                   :name     name
                   :local    :let
                   :init     expr
                   :atom     aatom
                   :children [:init]}]
       :body     (f aexpr)
       :children [:bindings :body]})))

(defn- emit-bind [computation f]
  (let [name (gensym 'v)
        aatom (atom nil)
        acomp {:op          :local
               :form        name
               :name        name
               :assignable? false
               :local       :arg
               :arg-id      0
               :variadic?   false
               :atom        aatom}
        recur-label (gensym 'recur)]
    {:op          :protocol-invoke
     :protocol-fn {:op   :var
                   :form `flat-map
                   :var  #'flat-map}
     :target      computation
     :args        [{:op              :fn
                    :variadic?       false
                    :max-fixed-arity 1
                    :methods         [{:op          :fn-method
                                       :loop-id     recur-label
                                       :variadic?   false
                                       :params      [{:op        :binding
                                                      :form      name
                                                      :name      name
                                                      :local     :arg
                                                      :arg-id    0
                                                      :variadic? false
                                                      :atom      aatom
                                                      :children  []}]
                                       :fixed-arity 1
                                       :body        {:op         :do
                                                     :statements []
                                                     :ret        (f acomp)
                                                     :body?      true
                                                     :children   [:statements :ret]}
                                       :children    [:params :body]}]
                    :once            false
                    :children        [:methods]}]
     :children    [:fn :args]}))

(declare ->NamedCont continue)

(defn- trivializing-cont [cont f]
  (if (trivial? cont)
    (f cont)
    (let [k (gensym 'k)
          katom (atom nil)
          kexpr {:op          :local
                 :form        k
                 :name        k
                 :assignable? false
                 :local       :let
                 :atom        katom}
          v (gensym 'v)
          vatom (atom nil)
          vexpr {:op          :local
                 :form        v
                 :name        v
                 :assignable? false
                 :local       :arg
                 :arg-id      0
                 :variadic    false
                 :atom        vatom}
          recur-label (gensym 'recur)]
      {:op       :let
       :bindings [{:op       :binding
                   :form     k
                   :name     k
                   :local    :let
                   :init     {:op              :fn
                              :variadic?       false
                              :max-fixed-arity 1
                              :methods         [{:op          :fn-method
                                                 :loop-id     recur-label
                                                 :variadic?   false
                                                 :params      [{:op        :binding
                                                                :form      v
                                                                :name      v
                                                                :local     :arg
                                                                :arg-id    0
                                                                :variadic? false
                                                                :atom      vatom
                                                                :children  []}]
                                                 :fixed-arity 1
                                                 :body        {:op         :do
                                                               :statements []
                                                               :ret        (continue cont vexpr)
                                                               :body?      true
                                                               :children   [:statements :ret]}
                                                 :children    [:params :body]}]
                              :once            false
                              :children        [:methods]}
                   :atom     katom
                   :children [:init]}]
       :body     (f (->NamedCont kexpr))
       :children [:bindings :body]})))

(defprotocol ContEmitter
  (continue [self expr])
  (continue-computation [self computation]))

(declare ->NodeCont convert)

(deftype NodeCont [parent                                   ; The parent continuation of this
                   orig-node                                ; The unconverted AST node
                   new-node                                 ; The (partial) converted AST node
                   path]                                    ; Path to the subnode whose conversion this is waiting for
  IsTrivial
  (trivial? [_] false)

  ContEmitter
  (continue [_ expr]
    (trivializing expr (fn [aexpr]
                         (let [new-node (assoc-in new-node path aexpr)]
                           (if-let [[subnode path*] (next-path orig-node path)]
                             (convert (->NodeCont parent orig-node new-node path*) subnode)
                             (continue parent new-node))))))

  (continue-computation [_ computation]
    (emit-bind computation
               (fn [acomp]
                 (let [new-node (assoc-in new-node path acomp)]
                   (if-let [[subnode path*] (next-path orig-node path)]
                     (convert (->NodeCont parent orig-node new-node path*) subnode)
                     (continue parent new-node)))))))

(defn- convert-case-branches [cont case-ast test*]
  (-> case-ast
      (assoc :test test*)
      (update :thens (partial mapv (partial convert cont)))
      (update :default (partial convert cont))))

(deftype CaseCont [parent orig-node]
  IsTrivial
  (trivial? [_] false)

  ContEmitter
  (continue [_ expr] (convert-case-branches parent orig-node expr))
  (continue-computation [_ computation] (emit-bind computation (partial convert-case-branches parent orig-node))))

(defn- convert-if-branches [cont if-ast test*]
  (-> if-ast
      (assoc :test test*)
      (update :then (partial convert cont))
      (update :else (fn [else-ast]
                      (let [converted (convert cont else-ast)]
                        ;; HACK: Must have :form, otherwise emit-form will not emit else branch:
                        (assoc converted :form (emit-form converted)))))))

(deftype IfCont [parent orig-node]
  IsTrivial
  (trivial? [_] false)

  ContEmitter
  (continue [_ expr] (convert-if-branches parent orig-node expr))
  (continue-computation [_ computation] (emit-bind computation (partial convert-if-branches parent orig-node))))

(deftype BindCont [parent]
  IsTrivial
  (trivial? [_] false)

  ContEmitter
  (continue [self expr] (continue-computation self expr))
  (continue-computation [_ computation]
    (assert (!-node? computation))
    (continue-computation parent (get-in computation [:args 0]))))

(deftype NamedCont [cont-ref]
  IsTrivial
  (trivial? [_] true)

  ContEmitter
  (continue [_ expr]
    {:op       :invoke
     :fn       cont-ref
     :args     [expr]
     :children [:fn :args]})

  (continue-computation [_ computation] computation
    {:op          :protocol-invoke
     :protocol-fn {:op :var, :form `flat-map, :var #'flat-map}
     :target      computation
     :args        [cont-ref]
     :children    [:protocol-fn :target :args]}))

(deftype TailCont [pure-ref]
  IsTrivial
  (trivial? [_] true)

  ContEmitter
  (continue [_ expr] {:op       :invoke
                      :fn       pure-ref
                      :args     [expr]
                      :children [:fn :args]})
  (continue-computation [_ computation] computation))

(defmulti convert-monadic
          (fn [_cont {:keys [op]}]
            (case op
              (:def :do :host-interop :instance-call :instance-field :instance? :keyword-invoke :map :monitor-enter
                :monitor-exit :new :primitive-invoke :protocol-invoke :set :set! :static-call :vector :with-meta)
              ::basic-block

              op)))

;;; TODO: Local binding, probably straightforward: let letfn binding
;;;       Function-type things, treated like constants: fn fn-method deftype reify method
;;;       Never ::monadic (?): (const quote local static-field the-var var import)
;;;       Loop, needs to be trampolined: loop recur
;;;       Exceptions, maybe use something like MonadError (?): try catch throw

(defn- convert-basic-block [cont ast]
  (if-let [[child path] (first-path ast)]
    (convert (->NodeCont cont ast ast path) child)
    ast))

(defmethod convert-monadic ::basic-block [cont ast] (convert-basic-block cont ast))

(defmethod convert-monadic :case [cont {:keys [test] :as ast}]
  (trivializing-cont cont (fn [k] (convert (->CaseCont k ast) test))))

(defmethod convert-monadic :if [cont {:keys [test] :as ast}]
  (trivializing-cont cont (fn [k] (convert (->IfCont k ast) test))))

(defmethod convert-monadic :invoke [cont ast]
  (if (!-node? ast)
    (let [[arg arg-path] (next-path ast [:fn])]             ; Skip :fn to avoid generating any references to `!`.
      ;; Use ->BindCont to redirect `continue` calls to `continue-computation`:
      (convert (->NodeCont (->BindCont cont) ast ast arg-path) arg))
    (convert-basic-block cont ast)))

(defn- convert [cont ast]
  (if (monadic? ast)
    (convert-monadic cont ast)
    (continue cont ast)))

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
        body-locals (assoc let-locals pure-name pure-ref)
        ast {:op       :let
             :bindings [{:op       :binding
                         :form     pure-name
                         :name     pure-name
                         :local    :let
                         :init     (ana/analyze pure (assoc (ana/empty-env) :locals let-locals))
                         :children []}]
             :body     (->> (ana/analyze `(do ~@body) (assoc (ana/empty-env) :locals body-locals))
                            annotate-effects
                            (convert (->TailCont pure-ref)))
             :children [:bindings :body]}]
    (emit-form ast)))
