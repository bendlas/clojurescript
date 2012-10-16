(ns cljs.optimizer
  (:require
   [clojure.walk :as walk]
   [clojure.zip :as zip]))

(defn emit-assocr [m kvs]
  (let [step (fn [cont [k v]]
               `(let [cont# ~cont]
                  (if (contains? ~m ~k)
                    (assoc! cont# ~k ~v)
                    cont#)))]
    (list `persistent!
          (reduce step
                  `(transient ~m)
                  kvs))))

(defmacro assocr [m & {:as kvs}]
  (let [m-sym (gensym "m")]
    `(let [~m-sym ~m]
       ~(emit-assocr m-sym kvs))))

(defmulti walk-children :op)

(defn block-children [{:keys [statements ret]}]
  (conj (vec statements) ret))

(defn walk-block-children [{:keys [statements ret] :as block} f]
  (let [statements (walk-children statements f)
        ret (walk-children ret f)]
    (f (assoc block
         :statements statements
         :ret ret
         :children (conj (vec statements) ret)))))

(defn walk-let-children [{:keys [bindings statements ret] :as form} f]
  (let [bi (map #(walk-children (:init %) f) bindings)
        statements (map #(walk-children % f) statements)
        ret (walk-children ret f)]
    (f (assoc form
         :bindings (map #(assoc %1 :init %2) bindings bi)
         :statements statements
         :ret ret
         :children (into (vec bi)
                         (conj (vec statements) ret))))))

(defmethod walk-children :letfn [form f]
  (walk-let-children form f))

(defmethod walk-children :let* [form f]
  (walk-let-children form f))

(defmethod walk-children :loop* [form f]
  (walk-let-children form f))

(defmethod walk-children :default [form f]
  (cond
    (nil? form) nil
    (map? form) (walk-block-children form f)
    (sequential? form) (map #(walk-children % f) form)
    :else (throw (ex-info (str "Can't walk " form) {:form form}))))

(defmacro def-child-walker [op ana-keys extract-children]
  (let [form-sym (gensym "form-")
        f-sym (gensym "f-")
        key-walkers
        (into {} (for [e ana-keys]
                   (if (map? e)
                     (let [[k v] (first e)]
                       (assert (= 1 (count e)))
                       [k (walk/postwalk-replace
                           {'w# `#(walk-children % ~f-sym)
                            'ch# `(~(keyword k) ~form-sym)}
                           v)])
                     [e `(walk-children (~(keyword e) ~form-sym) ~f-sym)])))
        let-keys (keys key-walkers)]
    `(defmethod walk-children ~op [~form-sym ~f-sym]
       (let ~(vec (interleave let-keys (vals key-walkers)))
         (~f-sym (assoc ~form-sym
                   ~@(interleave (map keyword let-keys) let-keys)
                   :children ~extract-children))))))

(def-child-walker :try* [try catch finally]
  (vec (mapcat block-children
               [try catch finally])))

(def-child-walker :def [init]
  (when init [init]))

(def-child-walker :fn [methods]
  (vec (mapcat block-children methods)))

(def-child-walker :recur [{exprs (mapv w# ch#)}]
  exprs)

(def-child-walker :new [ctor args]
  (into [ctor] args))

(def-child-walker :set! [target val]
  [target val])

(def-child-walker :dot [target args]
  [into [target] args])

;; business end

(defn remove-unused [form]
  (cond
    (and (= :var (:op form))
         (= :statement (-> form :env :context)))
    {:op :no-op}

    :else
    form))

(def log (atom []))

(defn shake-unused-vars [form]
  (let [res (walk-children form remove-unused)]
    (swap! log conj {:before form :after res})
    res))

(defn optimize-toplevel-form [form]
  (shake-unused-vars form))
