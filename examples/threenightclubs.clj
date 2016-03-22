;; This is example show on how to compose and apply predicates using the
;; Prediccat core library.
;;
;; This is based on another example that illustrates how to use Scalaz validation
;; in Scala, which can be found here:
;; https://gist.github.com/oxbowlakes/970717

(ns threenightclubs
  (require [predicat.core :refer :all]))

(defrecord Person [gender age clothes sobriety])

;; Concise printing
(defmethod print-method Person [p ^java.io.Writer w]
  (.write w (str "#Person" (into {} p))))


;;;
;;; Definition of parameterized predicates with `defp(arameterized)p(redicate)'
;;;

(defpp gte? [min] (p #(>= % min)))

(defpp lt? [max] (p #(< % max)))

(defpp between? [min max] (p-and (gte? min) (lt? max)))


;;;
;;; Definition of a query to access nested map values with
;;; `defp(arameterized)q(uery)
;;;

(defpq q-in [ks] (q #(get-in % ks)))


;;;
;;; Definition of constant predicates with `defp(redicate)'
;;;

;; First CHECK
(defp check-age (q-in [:age] (between? 18 40)))

;; Second CHECK
(defp check-clothes (p< #(q-in [:clothes]
                               (case (:gender %)
                                 :male (p (partial some #{"Tie"}))
                                 :female (p (partial not-any? #{"Trainers"}))))))

;; Third CHECK
(defp check-sobriety
  (q-in [:sobriety] (p-not (p #{:drunk :paralytic :unconscious}))))


;;;
;;; Plain function to compute the entrance fee
;;;

(defn compute-cost [person]
  (if (= (:gender person) :female) 0 5))


(comment
  "Part One : Clubbed to Death

 Now let's compose some validation checks"
  )

(defn cost-to-enter [person]
  (app-p compute-cost ((p-and check-age check-clothes check-sobriety) person)))

;; Now let's see these in action

(def Ken (Person. :male 28 #{"Tie" "Shirt"} :tipsy))
(def Dave (Person. :male 41 #{"Tie" "Jeans"} :sober))
(def Ruby (Person. :female 25 #{"High Heels"} :tipsy))


(comment
  "Let's go clubbing!"
  )

(check-age Ken)
;; => #Person{:gender :male, :age 28, :clothes #{"Tie" "Shirt"},
;;            :sobriety :tipsy}


(cost-to-enter Dave)
;; => #F[((p-and check-age check-clothes check-sobriety)
;;        #Person{:gender :male, :age 41, :clothes #{Tie Jeans},
;;                :sobriety :sober})]
;;
(get-root-f *1)
;; => #F[((q-in [:age] (lt? 40))
;;        #Person{:gender :male, :age 41, :clothes #{Tie Jeans},
;;                :sobriety :sober})]
;; By default get-root-f doesn't narrow the subject but expanding a failure
;; interactively or calling explain-f always does. The behavior can be tuned with
;; *narrow-subject*.
(*1)
;; => #F[((lt? 40) 41)]

(cost-to-enter Ken)
;; => 5


(cost-to-enter Ruby)
;;=> 0


(cost-to-enter (map->Person (assoc Ruby :age 17)))
;; => #F[((p-and check-age check-clothes check-sobriety)
;;        #Person{:gender :female, :age 17, :clothes #{High Heels},
;;                :sobriety :tipsy})]
(get-root-f *1)
;; => #F[((q-in [:age] (gte? 18))
;;        #Person{:gender :female, :age 17, :clothes #{High Heels},
;;                :sobriety :tipsy})]
(*1)
;; => #F[((gte? 18) 17)]

(cost-to-enter (map->Person (assoc Ken :sobriety :unconscious)))
;; => #F[((p-and check-age check-clothes check-sobriety)
;;        #Person{:gender :male, :age 28, :clothes #{Tie Shirt},
;;                :sobriety :unconscious})]
(get-root-f *1)
;; => #F[((q-in [:sobriety] (p-not (p #{:paralytic :drunk :unconscious})))
;;        #Person{:gender :male, :age 28, :clothes #{Tie Shirt},
;;                :sobriety :unconscious})]
(*1)
;; => #F[((p-not (p #{:paralytic :drunk :unconscious})) :unconscious)]

(comment
  "Dave tried the second nightclub after a few more drinks in the
  pub")

(cost-to-enter (map->Person (assoc Dave :sobriety :paralytic)))
;; => #F[((p-and check-age check-clothes check-sobriety)
;;        #Person{:gender :male, :age 41, :clothes #{Tie Jeans},
;;                :sobriety :paralytic})]
(get-root-f *1)
;; => #F[((p-and (q-in [:age] (lt? 40))
;;               (q-in [:sobriety]
;;                     (p-not (p #{:paralytic :drunk :unconscious}))))
;;        #Person{:gender :male, :age 41, :clothes #{Tie Jeans},
;;                :sobriety :paralytic})]
(*1)
;; "1. ((q-in [:age] (lt? 40))
;;      #Person{:gender :male, :age 41, :clothes #{\"Tie\" \"Jeans\"},
;;              :sobriety :paralytic})"
;; "2. ((q-in [:sobriety] (p-not (p #{:paralytic :drunk :unconscious})))
;;      #Person{:gender :male, :age 41, :clothes #{\"Tie\" \"Jeans\"},
;;              :sobriety :paralytic})"
;; => #F[((p-and (q-in [:age] (lt? 40)) (q-in [:sobriety]
;;               (p-not (p #{:paralytic :drunk :unconscious}))))
;;        #Person{:gender :male, :age 41, :clothes #{"Tie" "Jeans"},
;;                :sobriety :paralytic})]
(*1 1)
;; => #F[((q-in [:age] (lt? 40))
;;        #Person{:gender :male, :age 41, :clothes #{"Tie" "Jeans"},
;;                :sobriety :paralytic})]
(*1)
;; => #F[((lt? 40) 41)]


(cost-to-enter Ruby)
;; => 0


(comment
  " Part Three : Gay Bar")

(defp check-gender (q-in [:gender] (p (partial = :male))))

(defn cost-to-enter [person]
  (bind-p [p ((p-and check-age check-clothes check-sobriety check-gender)
              person)]
    (+ (:age p) 1.5)))


(cost-to-enter (Person. :male 59 #{"Jeans"} :paralytic))
;; => #F[((p-and check-age check-clothes check-sobriety check-gender)
;;        #Person{:gender :male, :age 59, :clothes #{Jeans},
;;                :sobriety :paralytic})]
(get-root-f *1)
;; => #F[((p-and (q-in [:age] (lt? 40))
;;               (q-in [:clothes] (p (partial some #{"Tie"})))
;;               (q-in [:sobriety]
;;                     (p-not (p #{:paralytic :drunk :unconscious}))))
;;        #Person{:gender :male, :age 59, :clothes #{Jeans},
;;                :sobriety :paralytic})]
;; By default, get-root-f doesn't narrow the subject.
(binding [*narrow-subject* true]
  (get-root-f *1 2))
;; => #F[((p (partial some #{"Tie"})) #{"Jeans"})]


(cost-to-enter Ken)
;; => 29.5

(cost-to-enter Ruby)
;; => #F[((p-and check-age check-clothes check-sobriety check-gender)
;;     #Person{:gender :female, :age 25, :clothes #{High Heels},
;;             :sobriety :tipsy})]
(get-root-f *1)
;; => #F[((q-in [:gender] (p (partial = :male)))
;;        #Person{:gender :female, :age 25, :clothes #{High Heels},
;;                :sobriety :tipsy})]

