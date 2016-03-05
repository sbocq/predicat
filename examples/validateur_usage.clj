(ns validateur-usage
  (:require [predicat.core :refer :all]))

;;
;; Examples inspired from Validateur's usage guide, which can be found here:
;; http://clojurevalidations.info/articles/getting_started.html
;;


;;;
;;; Definition of a predicate to test if a map contains a key path
;;;

(defn ncontains? [m ks]
  (if (set? ks)
    (every? (partial contains? m) ks)
    (if-let [k (first ks)]
      (when (contains? m k)
        (recur (k m) (rest ks)))
      true)))

(defpp present? [ks] (p #(ncontains? % ks)))

(defp no-spaces? (p (partial re-matches #"^[^\s]*$")))


;;;
;;; Definition of a custom query to access map values by key
;;;

(defpq q-in [ks] (q #(get-in % ks)))


(let [v (p-&& (present? [:user-name]) (q-in [:user-name] no-spaces?))]
  (v {:user-name "99 bananas"}))
;; => #F[((p-&& (present? [:user-name]) (q-in [:user-name] no-spaces?))
;;        {:user-name "99 bananas"})]

(expand-root-f *1)
;; => #F[((q-in [:user-name] no-spaces?) {:user-name "99 bananas"})]


;;;
;;;  Turn-on subject reduction
;;;

(let [v (p-&& (present? [:user-name])
              (q-in [:user-name] no-spaces?))]
  (v {:user-name "99 bananas"})
  (binding [*reduce-subject* true]
    (expand-root-f *1)))
;; => #F[(no-spaces? "99 bananas")]


(let [v (p-and (present? [:name]) (present? [:age]))
      extra-nested (q-in [:user :profile]
                         (p-and (present? [:age]) (present? [:birthday :year])))]
  [(v {})
   (v {:user {:name "name"}})
   (extra-nested {:user {:profile {:age 10
                                   :birthday {:year 2004}}}})
   (extra-nested {:user {:profile {:age 10}}})])
;; => [#F[((p-and (present? [:name]) (present? [:age])) {})]
;;     #F[((p-and (present? [:name]) (present? [:age])) {:user {:name "name"}})]
;;     {:user {:profile {:age 10, :birthday {:year 2004}}}}
;;     #F[((q-in [:user :profile] (p-and (present? [:age])
;;                                       (present? [:birthday :year])))
;;         {:user {:profile {:age 10}}})]]
(mapv expand-root-f (remove map? *1))
;; => [#F[((p-and (present? [:name]) (present? [:age])) {})]
;;     #F[((p-and (present? [:name]) (present? [:age])) {:user {:name "name"}})]
;;     #F[((q-in [:user :profile] (present? [:birthday :year]))
;;         {:user {:profile {:age 10}}})]]


;;;
;;; Definition of parameterized predicates with `defp(arameterized)p(redicate)'
;;;

(defpp gte? [min] (p #(>= % min)))

(defpp lt? [max] (p #(< % max)))

(defpp within? [min max] (p-and (gte? min) (lt? max)))


;;;
;;; Definition of queries to access:
;;; - nested map values with `defp(arameterized)q(uery)
;;; - the length of a value with a plain query definition

(defpq q-in [ks] (q #(get-in % ks)))

(defq q-on-length (q count))


;;;
;;; Usage
;;;

(defp check-secret (p-and (q-in [:password] (q-on-length (within? 5 15)))
                          (q-in [:phone] (q-on-length (p (partial = 10))))))
(check-secret {:password "hiohjk" :phone "0907287"})
(expand-root-f *1)
;; => #F[((q-in [:phone] (q-on-length (p (partial = 10))))
;;        {:password "hiohjk", :phone "0907287"})]

(check-secret {:password "hio" :phone "0907287890"})
(expand-root-f *1)
;; => #F[((q-in [:password] (q-on-length (gte? 5)))
;;        {:password "hio", :phone "0907287890"})]

(check-secret {:password "hiohjk" :phone "0907287890"})
;; => {:password "hiohjk", :phone "0907287890"}

(defp check-profile (present? #{:first-name :last-name}))

(defp check-account (p-and (q-in [:secrets] check-secret)
                           (q-in [:profile] check-profile)))


(check-account {:profile {:first-name "John" :last-name "Snow"}
                :secrets {:password "hio" :phone "0907287890"}})
(expand-root-f *1)
;; => #F[((q-in [:secrets] (q-in [:password] (q-on-length (gte? 5))))
;;        {:profile {:first-name "John", :last-name "Snow"},
;;         :secrets {:password "hio", :phone "0907287890"}})]

(explain-f *2)
;; #F[(check-account {:profile {:first-name "John", :last-name "Snow"},
;;                    :secrets {:password "hio", :phone "0907287890"}})]
;; #F[((p-and (q-in [:secrets] check-secret)
;;            (q-in [:profile] check-profile))
;;     {:profile {:first-name "John", :last-name "Snow"},
;;      :secrets {:password "hio", :phone "0907287890"}})]
;; #F[((q-in [:secrets] check-secret)
;;     {:profile {:first-name "John", :last-name "Snow"},
;;      :secrets {:password "hio", :phone "0907287890"}})]
;; #F[((q-in [:secrets] (p-and (q-in [:password] (q-on-length (within? 5 15)))
;;                             (q-in [:phone] (q-on-length (p (partial = 10))))))
;;     {:profile {:first-name "John", :last-name "Snow"},
;;      :secrets {:password "hio", :phone "0907287890"}})]
;; #F[((q-in [:secrets] (q-in [:password] (q-on-length (within? 5 15))))
;;     {:profile {:first-name "John", :last-name "Snow"},
;;      :secrets {:password "hio", :phone "0907287890"}})]
;; #F[((q-in [:secrets]
;;           (q-in [:password] (q-on-length (p-and (gte? 5) (lt? 15)))))
;;     {:profile {:first-name "John", :last-name "Snow"},
;;      :secrets {:password "hio", :phone "0907287890"}})]
;; #F[((q-in [:secrets] (q-in [:password] (q-on-length (gte? 5))))
;;     {:profile {:first-name "John", :last-name "Snow"},
;;      :secrets {:password "hio", :phone "0907287890"}})]
;; #F[((q-in [:password] (q-on-length (gte? 5)))
;;     {:password "hio", :phone "0907287890"})]
;; #F[((q-on-length (gte? 5)) "hio")]
;; #F[((gte? 5) 3)]


;;;
;;; For illustration
;;;

(defmulti renderq (fn [q] (first q)))
(defmethod renderq 'q-in [q] (str "in " (second q) ", " (renderq (nth q 2))))
(defmethod renderq 'q-on-length [q] (str "length " (renderq (second q))))
(defmethod renderq 'gte? [q] (str "must be greater or equal to " (second q)))


(let [f (expand-root-f
         (check-account {:profile {:first-name "John" :last-name "Snow"}
                         :secrets {:password "hio" :phone "0907287890"}}))]
  (renderq (f->q f)))
;; => "in [:secrets], in [:password], length must be greater or equal to 5"
