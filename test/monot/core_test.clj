(ns monot.core-test
  (:require [clojure.test :refer [deftest is]]
            [monot.core :refer [in-monad !]]))

(defn- vector-bind [mv f]
  (into [] (mapcat f) mv))

(deftest vector-pure
  (is (= (in-monad vector vector-bind 23) [23])))

(deftest vector-comprehension
  (is (= (in-monad vector vector-bind
           (! [(! [1 2])
               (! [3 4])]))
         [1 3 1 4 2 3 2 4])))

(deftest vector-if
  (is (= (in-monad vector vector-bind
           (if (! [true false])
             (! [1 2])
             (! [3 4])))
         [1 2 3 4])))