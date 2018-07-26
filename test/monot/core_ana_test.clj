(ns monot.core-ana-test
  (:require [clojure.test :refer [deftest is]]
            [monot.core-ana :refer [in-monad pure FlatMap]])
  (:import [clojure.lang PersistentVector]))

(defmethod pure PersistentVector [_ value] [value])

(extend-type PersistentVector
  FlatMap
  (flat-map [self f] (into [] (mapcat f) self)))

(deftest vector-pure
  (is (= (in-monad PersistentVector 23) [23])))

(deftest vector-comprehension
  (is (= (in-monad PersistentVector
                   (! [(! [1 2])
                       (! [1 2])]))
         [1 3 1 4 2 3 2 4])))
