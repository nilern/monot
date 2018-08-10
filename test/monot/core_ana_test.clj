(ns monot.core-ana-test
  (:require [clojure.test :refer [deftest is]]
            [monot.core-ana :refer [FlatMap in-monad !]])
  (:import [clojure.lang PersistentVector]))

(extend-type PersistentVector
  FlatMap
  (flat-map [self f] (into [] (mapcat f) self)))

(deftest vector-pure
  (is (= (in-monad vector 23) [23])))

(deftest vector-comprehension
  (is (= (in-monad vector
           (! [(! [1 2])
               (! [3 4])]))
         [1 3 1 4 2 3 2 4])))

(deftest vector-if
  (is (= (in-monad vector
           (if (! [true false])
             (! [1 2])
             (! [3 4])))
         [1 2 3 4])))