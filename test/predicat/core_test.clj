(ns predicat.core-test
  (:require [clojure.test :refer :all]
            [predicat.core :refer :all]))

(use-fixtures :once (fn [test] (binding [*expand-to-primitives* true
                                         *narrow-subject* true]
                                 (test))))

(deftest cata-p-test
  (testing "cata-p"
    (is (= 2 (cata-p ((p odd?) 1)
               f f
               s (inc s))))
    (is (= 1 (f->s (cata-p ((p even?) 1)
                     f f
                     s (inc s)))))))

(defn is-f? [f q s]
  (is (cata-p f _ f _ nil))
  (is (= q (f->q f)))
  (is (= s (f->s f))))

(deftest p-test
  (testing "p"
    (let [gte1? (p #(>= % 1))]
      (is (= 1 (gte1? 1)))
      (let [f (gte1? 0)]
        (is-f? f '(p (fn [a] (>= a 1))) 0)
        (is (= 1 (count (get-stack-f f))))))))

(deftest p<-test
  (testing "p<"
    (let [check? (p< (fn [s] (case (:d s)
                               :a (p #(>= (:v %) 1))
                               :b (p #(< (:v %) 1)))))]
      (is (= {:d :a, :v 2} (check? {:d :a, :v 2})))
      (is (= {:d :b, :v 0} (check? {:d :b, :v 0})))
      (let [f (check? {:d :a, :v 0})]
        (is-f? f '(p< (fn [s] (case (:d s)
                                :a (p (fn [a] (>= (:v a) 1)))
                                :b (p (fn [b] (< (:v b) 1))))))
               {:d :a, :v 0})
        (is (= 2 (count (get-stack-f f))))
        (is-f? (get-root-f f) '(p (fn [a] (>= (:v a) 1))) {:d :a, :v 0})))))

(defpp gte? [min] (p #(>= % min)))
(defpp lt? [max] (p #(< % max)))
(defpp between? [min max] (p-and (gte? min) (lt? max)))
(defpq q-in [ks] (q #(get-in % ks)))

(defn check-f [p s [n last-q & [last-s]]]
  (testing (list (p->q p) s)
    (let [f (p s)]
      (is-f? f (p->q p) s)
      (let [fs (get-stack-f f)
            last-f (last fs)]
        (is (= n (count fs)))
        (is (= last-q (f->q last-f)))
        (is (= (or last-s s) (f->s last-f)))))))

(defn check-s [p s]
  (is (= s (p s))))

(deftest q-in-test
  (testing "q-in"
    (check-s (q-in [:a :b] (p odd?)) {:a {:b 1}})
    (check-f (q-in [:a :b] (p even?)) {:a {:b 1}}
             [2 '(p even?) 1])))

(deftest p-and-test
  (check-f (p-and (between? 2 4) (p odd?)) 0
           [4 '(p-and (p (fn [a] (>= a 2))) (p odd?))])
  (check-f (p-and (between? 2 4) (p odd?)) 1
           [5 '(p (fn [a] (>= a 2)))])
  (check-f (p-and (between? 2 4) (p odd?)) 2
           [2 '(p odd?)])
  (check-s (p-and (between? 2 4) (p odd?)) 3)
  (check-f (p-and (q-in [:age] (between? 18 40)) (q-in [:age] (p even?)))
           {:age 41}
           [5 '(p-and (p (fn [a] (< a 40))) (p even?)) 41])
  (check-f (p-and (q-in [:age] (between? 18 40)) (p map?))
           {:age 41}
           [6 '(p (fn [a] (< a 40))) 41])
  (check-f (p-and (q-in [:age] (between? 18 40)) (p seq?)) {:age 41}
           [4 '(p-and (q-in [:age] (p (fn [a] (< a 40)))) (p seq?))])
  (binding [*expand-to-primitives* false]
    (check-f (between? 1 2) 3
             [3 '(lt? 2)])))

(deftest p-&&-test
  (testing "p-&&"
    (check-f (p-&& (between? 2 4) (p odd?)) 0
             [5 '(p (fn [a] (>= a 2)))])
    (check-f (p-&& (between? 2 4) (p odd?)) 2
             [2 '(p odd?)])
    (check-s (p-&& (between? 2 4) (p odd?)) 3)))

(deftest p-or-test
  (testing "p-or"
    (check-s (p-or (between? 2 4) (p odd?)) 1)
    (check-s (p-or (between? 2 4) (p odd?)) 2)
    (check-f (p-or (between? 2 4) (p odd?)) 0
             [4 '(p-or (p (fn [a] (>= a 2))) (p odd?))])))

(deftest p-not-test
  (testing "p-not"
    (check-f (p-not (p-or (between? 2 4) (p odd?))) 2
             [6 '(p-or (p-not (p (fn [a] (>= a 2))))
                       (p-not (p (fn [a] (< a 4)))))])
    (check-f (p-not (p-or (between? 2 4) (p odd?))) 1
             [3 '(p-not (p odd?))])
    (check-s (p-not (p-or (between? 2 4) (p odd?))) 0)
    (binding [*expand-to-primitives* false]
      (check-f (p-not (gte? 2)) 2
               [1 '(p-not (gte? 2))]))))

(defn check-f* [p s [n last-q & [last-s]]]
  (testing (list (p->q p) s)
    (let [f (p s)]
      (is (cata-p f _ f _ nil))
      (is (= (p->q p) (f->q f)))
      (let [fs (get-stack-f f)
            last-f (last fs)]
        (is (= n (count fs)))
        (is (= last-q (f->q last-f)))
        (is (= (or last-s s) (f->s last-f)))))))

(deftest p-all-test
  (testing "p-all"
    (check-f* (p-all (between? 2 3)) [1 2 3 4]
              [2 '(p-all (p-and (gte? 2) (lt? 3))) [1 3 4]])
    (check-f* (p-all (between? 2 5)) [1 2 3 4]
              [5 '(p (fn [a] (>= a 2))) 1])
    (check-s (p-all (between? 2 5)) [2 3 4])
    (check-f* (p-all (between? 2 5)) [4 6 7]
              [4 '(p-all (p (fn [a] (< a 5)))) [6 7]])))

(deftest p-no-test
  (check-f* (p-no (p odd?)) [1 2]
            [2 '(p-not (p odd?)) 1])
  (binding [*narrow-subject* false]
    ;; p-no overrides narrow subject
    (check-f* (p-no (p odd?)) [1 2]
              [2 '(p-not (p odd?)) 1]))
  (check-s (p-no (p odd?)) [2 4]))

(deftest p-some-test
  (check-s (p-some (between? 2 3)) [1 2 3 4])
  (check-f* (p-some (between? 0 1)) [1 2 3 4]
            [4 '(p-some (p (fn [a] (< a 1))))])
  (check-f* (p-some (between? 2 3)) [1 3 4]
            [2 '(p-some (p-and (gte? 2) (lt? 3)))]))

(deftest p-some-not-test
  (testing "p-some-not"
    (check-s (p-some-not (p odd?)) [1 2])
    (check-f (p-some-not (p odd?)) [1 3]
             [1 '(p-some-not (p odd?))])))

(deftest app-p-test
  (testing "app-p"
    (is (= 3 (app-p + ((p odd?) 1) ((p even?) 2))))
    (is-f? (app-p + ((p odd?) 1) ((p even?) 3)) '(p even?) 3)))

(deftest bind-p-test
  (testing "bind-p"
    (is-f? (bind-p [a ((p even?) 1)]
             (inc a))
           '(p even?)
           1)
    (is (= 3 (bind-p [a ((p even?) 2)]
               (inc a))))))

(deftest let-p-test
  (testing "let-p"
    (is (= 9 (let-p [a ((p odd?) 1)
                     a* (+ a 2)
                     b (* a* a*)]
               ((p odd?) b))))
    (is-f? (let-p [a ((p even?) 1)
                   a* (+ a 2)
                   b (* a* a*)]
             ((p odd?) b))
           '(p even?)
           1)))





















