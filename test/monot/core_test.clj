(ns monot.core-test
  (:require [clojure.test :refer [deftest is]]
            [monot.core :refer [in-monad FlatMap]]))

(extend-type clojure.lang.PersistentVector
  FlatMap
  (flat-map [self f] (into (empty self) (mapcat f) self)))

(deftest vector-pure
  (is (= (in-monad vector 23) [23])))

(deftest vector-comprehension
  (is (= (in-monad vector
           (! (vector (! (vector 1 2))
                      (! (vector 3 4)))))
         [1 3 1 4 2 3 2 4])))
