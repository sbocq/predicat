(ns ^{:doc "Core Predicat library to create and compose predicates with
  traceable failures. It contains functions to create predicates (`p', `p<',
  `defp', `defpp') or compose predicates (`p-and', `p-or', `p-not', `p-some',
  ...) from existing ones. A predicate P is a function object that returns the
  subject S to which it is applied to upon success, or otherwise a proposition
  failure F. Results can be manipulated without nesting conditionnal statements
  in applicative (`app-p') or monadic (`let-p') manners. Predicates resulting
  from the composition of other predicates can be expanded by evaluating them as
  nullary function or by using one of the `p-expand*' function. Proposition
  failures can be inspected iteratively by evaluating them as nullary functions
  or by using one of the `explain-f*' functions."} predicat.core)

(comment
  "
Glossary:

- A predicate function PF is a function of a subject S. It returns a proposition
  result that is its argument S when successfull or else a proposition failure F.

- A predicate of type P captures the symbolic expression EXPR of its predicate
  for inspection the matching compiled predicate function PF.

- A proposition failure of type F captures, the predicate expressions, the
  predicate function PF and the subject S of a proposition that fails.

Conventions:

- Functions suffixed by `-p' take a proposition result as argument.

- Functions prefixed by `p-' compose predicates.

- Functions suffixed by `-f' take a proposition failure as argument.

- Parameters named `q' denote a delayed quoted expression.

- Parameters named `pf' denote a predicate function.

- Parameters named `p' denote, depending on the context, a predicate or a
  proposition result.

- Parameters named `f' denote, depending on the context, a failure or a function.

Examples assume the following predicates have been defined:

(do
  (defpp gte? [min] (p #(>= % min)))
  (defpp lt? [max] (p #(< % max)))
  (defpp between? [min max] (p-and (gte? min) (lt? max))))
")

(def ^:dynamic *narrow-subject*
  "If true, do not preserve the subject while expanding a failure (default:
  false)."
  false)

(def ^:dynamic *expand-to-primitives*
  "If true, including primitive predicates while expanding failures (default:
  false)."
  false)

(defn- primitive-q?
  "Return true if the predicate expression Q is a primitive expression."
  [q] (and
       ;; expr is not a predicate fuction defined by user
       (not (symbol? q))
       ;; expr denotes a primitive
       (= 'p (first q))))


;;;
;;; Predicate type P
;;;

(declare p->next-p)

(deftype P [q ops pf next-p]
  clojure.lang.IFn
  ;; expand
  (invoke [this] (p->next-p this))
  ;; apply
  (invoke [_ s] (pf s)))

(defn ->P
  "Create a predicate P. Its parameters are a delayed expression Q,
  the predicate operands OPS, the predicate function PF generated from EXPR and
  the next predicate NEXT-P to which it expands (nil if none i.e. predicate is a
  primitive)."
  [q ops pf next-p] (P. q ops pf next-p))

(defn p->q
  "Return the quoted expression of a predicate P."
  [p] @(.q p))

(defn p->ops
  "Return the operands of a predicate P."
  [p] (.ops p))

(defn p->pf
  "Return the predicate function of a predicate P."
  [p] (.pf p))

(defn p->next-p
  "Return a new predicate equivalent to P but with its expression expanded."
  [p] (or (when-let [next-p @(.next-p p)]
            (when (or *expand-to-primitives*
                      (not (primitive-q? (p->q next-p))))
              next-p))
          p))

(defmethod print-method P [p ^java.io.Writer w]
  (.write w (str "#P[" (p->q p) "]")))

(defn p-expand-all
  "Return the vector of the expansions of predicate P.

  Examples:
  > (p-expand-all (between? 1 2))
  ;; => [#P[(between? 1 2)] #P[(p-and (gte? 1) (lt? 2))]]
  "
  [p]
  {:pre [(instance? P p)]}
  (loop [acc [p], p p, n (p->next-p p)]
    (if (= (p->q p) (p->q n)) acc (recur (conj acc n) n (n)))))

(defn p-expand-last
  "Return the last expansion of predicate P.

  Examples:
  > (p-expand-last (between? 1 2))
  ;; => #P[(p-and (gte? 1) (lt? 2))]
  "
  [p] (last (p-expand-all p)))

(defn p-explain
  "Print the expansions of predicate P.

  Examples:
  > (p-explain (between? 1 2))
  #P[(between? 1 2)]
  #P[(p-and (gte? 1) (lt? 2))]
  ;; => nil
  "
  [p] (doseq [p (p-expand-all p)] (prn p)))


;;;
;;; Proposition failure type F
;;;

(declare iexpand-f)

(deftype F [q pf s fs next-f]
  clojure.lang.IFn
  ;; expand failure
  (invoke [this] (iexpand-f this))
  ;; apply
  (invoke [this index] (iexpand-f this index)))

(defn ->F
  "Create a proposition failure. Its paremeters are the expression EXPR that
  fails, the predicate function PF and subject S that lead to this failure such
  that `(equal this (pf s))', sub-failures fs, and the next failure NEXT-F to
  which this expression can be expanded (nil if none)."
  ([q pf s next-f] (->F q pf s [] next-f))
  ([q pf s fs next-f] (F. q pf s fs next-f)))

(defn f->q
  "Return the quoted expression of the predicate that failed for failure F."
  [f] @(.q f))

(defn f->pf
  "Return the predicate function of the predicate that failed for failure F."
  [f] (.pf f))

(defn f->s
  "Return the subject of failure F."
  [f] (.s f))

(defn f->next-f
  "Expand a failure F to the next most specific failure."
  [f] (or (when-let [next-f @(.next-f f)]
            ;; pf failures can always be expanded e.g. p-and:
            ;;   #F[((p-and ((p even?) (p (odd? 1)))) 1)] => #F[((p even?) 1)]
            ;; or failure may be expanded depending if primitive or not
            (when (or *expand-to-primitives*
                      (:expand (meta (f->pf f)))
                      (not (primitive-q? (f->q next-f)))
                      (not (= (f->s f) (f->s next-f))))
              next-f))
          f))

(defmethod print-method F [f ^java.io.Writer w]
  (.write w (str "#F[(" (f->q f) " " (with-out-str (pr (f->s f))) ")]")))

(defn- iexpand-f
  "Expand interractively failures."
  ([f]
   (let [next-f (f->next-f f)]
     (when-let [fs (seq (.fs next-f))]
       (doseq [[i f*] (map-indexed vector fs)]
         (prn (str (inc i) ". " (f->q f*)))))
     next-f))
  ([f index]
   (nth (.fs (f->next-f f)) (dec index) nil)))

(defn expand-all-f
  "Collect the consecutive expansions of a proposition failure F into a vector
  until it can't be expanded further. Expansions depth can be controlled with the
  dynamic variables *narrow-subject* and *expand-to-primitives*.

  Examples:

  > (expand-all-f ((between? 1 2) 3))
  ;; => [#F[((between? 1 2) 3)]
         #F[((p-and (gte? 1) (lt? 2)) 3)]
         #F[((lt? 2) 3)]]
  "
  [f]
  {:pre [(instance? F f)]}
  (loop [acc [f], f f]
    (let [n (or (let [next-f (f->next-f f)]
                  (when (or (:narrow (meta (f->pf f)))
                            *narrow-subject*
                            (= (f->s f) (f->s next-f)))
                    next-f))
                f)]
      (if (and (= (f->q f) (f->q n)) (= (f->s f) (f->s n)))
        acc
        (recur (conj acc n) n)))))

(defn expand-root-f
  "Return the last expansion of a proposition failure F.

  Examples:

  > (expand-root-f ((between? 1 2) 3))
  ;; => #F[((lt? 2) 3)]
  "
  ([f] (last (expand-all-f f)))
  ([f index] (last (expand-all-f (f index)))))

(defn explain-f
  "Print the expansions of a proposition failure F.

  Examples:

  > (explain-f ((between? 1 2) 3))
  #F[((between? 1 2) 3)]
  #F[((p-and (gte? 1) (lt? 2)) 3)]
  #F[((lt? 2) 3)]
  ;; => nil
  "
  [f] (binding [*narrow-subject* true]
        (doseq [f (expand-all-f f)] (prn f))))


;;;
;;; Catamorphism for proposition results
;;;

(defmacro cata-p
  "For a proposition EXPR whose result is a failure, evaluate F-EXPR where F is
  bound to the failure. When it is a success, evaluate S-EXPR where S is bound to
  the success. If S and S-EXPR are omitted, return its result in case of success.

  Use this function to dispatch on the result of a proposition independently from
  the underlying representation.

  Examples:

  > (cata-p ((p odd?) 1)
      f [:failure f]
      s [:success (inc s)])
  ;; =>  [:success 2]

  > (cata-p ((p even?) 1)
      f [:failure f]
      s [:success (inc s)])
  ;; => [:failure #F[((p even?) 1)]]
  "
  [expr f f-expr & [s s-expr]]
  (let [r* (gensym "r")]
    `(let [~r* ~expr]
       (if (instance? F ~r*)
         ~(cond (= f f-expr) r*
                (= f '_) f-expr
                :else `(let [~f ~r*] ~f-expr))
         ~(cond (or (not s) (= s s-expr)) r*
                (= s '_) s-expr
                :else `(let [~s ~r*] ~s-expr))))))


;;;
;;; Custom constructors with private helpers
;;;

(defn- scrub-fn
  "Clean up \"...__auto__...\" and \"...#\" symbols from simple expressions.

  Example: > (scrub-fn '(fn [a] (> a 1) #(> b %))) < ;; => (fn [a] (> a
  1) (fn* [c] (> b c))))
  "
  [form]
  (if (seq? form)
    (case (first form) (fn fn*)
          (let [[ps & body] (rest form)
                all-letters (map (comp str char) (range (int \a) (int\z)))
                [smap] (reduce
                        (fn [[smap free :as state] sym]
                          (if (symbol? sym)
                            (let [n (name sym), match? (partial = n)]
                              (cond
                                ;; gensym or auto-var => bind to free letter
                                (and (not (smap sym))
                                     (or (= (last n) \#)
                                         (.contains n "__auto__")))
                                [(assoc smap sym (symbol (first free)))
                                 (rest free)]
                                ;; collision?
                                (and (= (count n) 1) (some match? all-letters))
                                (if (some match? free)
                                  ;; free letter used => not free anymore
                                  [smap (remove match? free)]
                                  ;; bound letter used => rebind to free one
                                  (if-let [e (first
                                              (filter (comp (partial = sym)
                                                            second)
                                                      smap))]
                                    [(assoc smap
                                            (first e) (symbol (first free)))
                                     (rest free)]
                                    state))
                                ;; skip
                                :else state))
                            state))
                        [{} all-letters]
                        (flatten form))]
            (list* 'fn (vec (map #(get smap % %) ps))
                   (clojure.walk/prewalk-replace (assoc smap 'fn* 'fn) body)))
          form)
    form))

(defn ^:no-doc make-pf*
  "Make a primitive predicate function from expression Q and a predicate function
  F that returns nil when it fails."
  ;; A primitive failure expands to itself and can't be expanded.
  [q f] (fn [s] (if (f s) s (->F q (make-pf* q f) s (delay nil)))))

(defmacro p
  "Create a primitive predicate (of type P) from a function expression of a
  single argument FN-EXPR. This predicate will return a failure when the function
  returns nil.

  Example: > (p #(>= % 1))
  ;; => #P[(p (fn [a] (>= a 1)))]
  "
  ;; Here we substitute variables bound in the environment ourselves since macros
  ;; capture quoted expressions.
  [fn-expr] (let [q (list 'p (clojure.walk/prewalk scrub-fn fn-expr))
                  names (keys &env)
                  quoted (list 'quote names)]
              `(let [q# (delay (clojure.walk/prewalk-replace
                                (zipmap ~quoted ~(cons 'list names)) '~q))]
                 (->P q# nil (make-pf* q# ~fn-expr) (delay nil)))))

(defn ^:no-doc make-pf<*
  "Make a predicate from expression Q and a function that returns a predicate
  that depends on the subject."
  [q fn-p] (fn [s] (cata-p ((fn-p s) s)
                     f (->F q (make-pf<* q fn-p) s (delay f)))))

(defmacro p<
  "Create a primitive predicate (of type P) from a function that returns a
  predicate that depends on the subject."
  [fn-p-expr] (let [q (list 'p< (clojure.walk/prewalk scrub-fn fn-p-expr))
                    names (keys &env)
                    quoted (list 'quote names)]
                `(let [q# (delay (clojure.walk/prewalk-replace
                                  (zipmap ~quoted ~(cons 'list names)) '~q))]
                   (->P q# nil (make-pf<* q# ~fn-p-expr) (delay nil)))))

(defn ^:no-doc wrap-pf*
  "Wrap an expression Q that evals to predicate function PF into another
  predicate function that, when it fails with failure F, returns (Q, PF) as a
  parent failure followed by F as expanded failure."
  [q pf] (fn [s] (cata-p (pf s) f (->F q (wrap-pf* q pf) s (delay f)))))

(defmacro defpp
  "Define a Parameterized Predicate. Bind a predicate expression
  P-EXPR (of type P) with free variables ARGS to a NAME."
  [name args p-expr]
  `(defn ~name ~args
     (let [q# (delay (list '~name ~@args))
           p-expr# ~p-expr]
       (->P q# nil (wrap-pf* q# (p->pf p-expr#)) (delay p-expr#)))))

(defmacro defp
  "Define a Predicate. Bind a predicate expression P-EXPR (of type P) to a NAME."
  [name p-expr]
  `(def ~name (let [q# (delay '~name)
                    p-expr# ~p-expr]
                (->P q# nil (wrap-pf* q# (p->pf p-expr#)) (delay p-expr#)))))


;;;
;;; Custom queries to focus on a subject attribute
;;;

(deftype Q [q qf]
  clojure.lang.IFn
  ;; apply
  (invoke [_ s] (qf s)))

(defn ->Q
  "Create a query Q. Its parameters are a delayed expression Q, and a query
  function QF."
  [q qf] (Q. q qf))

(defn q->q
  "Return the quoted expression of a query Q."
  [q] @(.q q))

(defn q->qf
  "Return the query function of a query Q."
  [q] (.qf q))

(defmethod print-method Q [q ^java.io.Writer w]
  (.write w (str "#Q[" (q->q q) "]")))

(defmacro q
  "Create a query (of type Q) from a query expression Q-EXPR.

  Example:
  > (q #(partial get-in %))
  ;; => #Q[(q (fn [a] (partial get-in a)))]
  "
  ;; Here we substitute variables bound in the environment ourselves since macros
  ;; capture quoted expressions.
  [q-expr] (let [q (list 'q (clojure.walk/prewalk scrub-fn q-expr))
                 names (keys &env)
                 quoted (list 'quote names)]
             `(let [q# (delay (clojure.walk/prewalk-replace
                               (zipmap ~quoted ~(cons 'list names)) '~q))]
                (->Q q# ~q-expr))))

(defn p-q
  "Lift a predicate P into a predicate that applies P to the subject obtained by
  applying a QUERY to it main subject.

  Examples:
  > (defpq q-in [ks] (q #(get-in % ks)))
  ;; => #'q-in

  > ((p-q (q-in [:a :b]) (p odd?)) {:a {:b 1}})
  ;; => {:a {:b 1}}
  ;; same as:
  > ((q-in [:a :b] (p odd?)) {:a {:b 1}})
  ;; => {:a {:b 1}}

  > ((p-q (q-in [:a :b]) (p even?)) {:a {:b 1}})
  ;; => #F[((q-in [:a :b] (p even?)) {:a {:b 1}})]

  > (expand-root-f *1)
  ;; => #F[((q-in [:a :b] (p even?)) {:a {:b 1}})]

  > (binding [*narrow-subject* true]
      (expand-root-f *1))
  ;; => #F[((p even?) 1)]
  "
  [query p]
  (letfn [(make-p-q-pf [qq qf q pf]
            (with-meta
              #(let [s (qf %)]
                 (cata-p (pf s)
                   f (->F q (make-p-q-pf qq qf q pf) %
                          (delay
                           (let [next-f (f->next-f f)
                                 next-q (f->q next-f)]
                             (if (and (not (= (f->q f) next-q))
                                      (= (f->s f) (f->s next-f)))
                               ;; Can expand the inner failure further while
                               ;; preserving the subject
                               (let [q* (delay
                                         (seq (concat @qq [(f->q next-f)])))
                                     pf* (make-p-q-pf qq qf q* (f->pf next-f))]
                                 (->F q* pf* % (delay (f->next-f (pf* %)))))
                               ;; Return the failure that focuses on the subject
                               ;; fetched by the query.
                               f))))
                   _ %))
              {:expand true}))]
    (let [qq (.q query)
          q (delay (seq (concat @qq [(p->q p)])))]
      (->P q [query] (make-p-q-pf qq (q->qf query) q (p->pf p))
           (delay (p-q query (p->next-p p)))))))

(defmacro defpq
  "Define a Parameterized Query. Bind a query Q-EXPR (of type Q) with free
  variables ARGS to a NAME.

  Example:
  > (defpq q-in [ks] (q #(get-in % ks)))
  ;; => #'q-in

  > ((q-in [:age] (p #(>= 1))) {:age 1})
  ;; => 1
  "
  ([name args q-expr]
   (list `defpq name "" args q-expr))
  ([name doc args q-expr]
   (let [p (gensym "p-")]
     `(defn ~name
        ~doc
        ([~@args] (->Q (delay (list '~name ~@args)) (q->qf ~q-expr)))
        ([~@args ~p] (p-q (~name ~@args) ~p))))))

(defmacro defq
  "Define a Query. Bind a query Q-EXPR (of type Q) to a NAME.

  Example:
  > (defq q-length (q count))
  ;; => #'q-in

  > ((q-length (p #(>= % 1))) [1 2])
  ;; => [1 2]
  "
  ([name q-expr] (list `defq name "" q-expr))
  ([name doc q-expr] (let [p (gensym "p-")]
                       `(defn ~name
                          ~doc
                          ([] (->Q (delay (list '~name)) (q->qf ~q-expr)))
                          ([p#] (p-q (~name) p#))))))

(defpq q-nth
  "Query function that applies a predicate p to the nth element of the vector
  subject it is passed as argument."
  [i] (q #(nth % i)))


;;;
;;; Combinators on predicates
;;;

(defn- expand-failures [fs]
  ;; Check if next failures have the same subject. If not, don't expand those
  ;; that haven't the same subject as the parent.
  (let [next-fs (map f->next-f fs)]
    (if (apply = (map f->s next-fs))
      next-fs
      (let [s (f->s (first fs))]
        (reduce (fn [fs [f next-f]]
                  (conj fs (if (= s (f->s next-f)) next-f f)))
                []
                (map list fs next-fs))))))

(defn- make-and-pf [q pfs]
  (with-meta
    #(let [fs (reduce (fn [fs pf] (cata-p (pf %) f (conj fs f) _ fs)) [] pfs)]
       (if (seq fs)
         ;; at least one predicate failed
         (->F q (make-and-pf q pfs) %
              (vec fs)
              (delay (if (seq (rest fs))
                       ;; multiple predicates failed
                       (let [fs* (if (= (count pfs) (count fs))
                                   ;; all failed => expand them all
                                   (expand-failures fs)
                                   ;; some failed => keep those that failed as is
                                   fs)]
                         ((make-and-pf (delay (cons 'p-and (map f->q fs*)))
                                       (map f->pf fs*))
                          (f->s (first fs*))))
                       ;; single predicate failed, get rid of 'p-and op
                       (first fs))))
         ;; success
         %))
    ;; e.g. (p-and (p foo)) must be expanded to (p foo)
    {:expand true}))

(defn p-and
  "Return a new predicate that is the conjunction of the predicates P1, P2 ...
  PN.

  Examples:

  > ((p-and (between? 2 4) (p odd?)) 0)
  ;; => #F[((p-and (between? 2 4) (p odd?)) 0)]

  > (expand-root-f *1)
  ;; => #F[((p-and (gte? 2) (p odd?)) 0)]

  > ((p-and (between? 2 4) (p odd?)) 1)
  ;; => #F[((p-and (between? 2 4) (p odd?)) 1)]

  > (expand-root-f *1)
  ;; => #F[((gte? 2) 1)]

  > ((p-and (between? 2 4) (p odd?)) 2)
  ;; => #F[((p-and (between? 2 4) (p odd?)) 2)]

  > (expand-root-f *1)
  ;; => #F[((p odd?) 2)]

  > ((p-and (between? 2 4) (p odd?)) 3)
  ;; => 3

  See also: p-&&, p-or, p-all
  "
  [p1 p2 & pn]
  (let [ps (into [p1 p2] pn)
        q (delay (cons 'p-and (map p->q ps)))]
    (->P q ps (make-and-pf q (map p->pf ps))
         (delay (apply p-and (map p->next-p ps))))))

(defn p-&&
  "Create a conjunction from a sequence of predicates that short circuits the
  evaluation of the remaining propositions on the first failure.

  > ((p-&& (between? 2 4) (p odd?)) 0)
  ;; => #F[((p-&& (between? 2 4) (p odd?)) 0)]

  > (expand-root-f *1)
  ;; => #F[((gte? 2) 1)]

  > ((p-&& (between? 2 4) (p odd?)) 2)
  ;; => #F[((p-&& (between? 2 4) (p odd?)) 2)]

  > (expand-root-f *1)
  ;; => #F[((p odd?) 2)]

  > ((p-&& (between? 2 4) (p odd?)) 3)
  ;; => 3

  See also: p-and
  "
  [p1 p2 & pn]
  (letfn [(make-&&-pf [q pfs]
            (with-meta
              #(if-let [f (loop [pfs* pfs]
                            (when-let [pf (first pfs*)]
                              (cata-p (pf %) f f _ (recur (rest pfs*)))))]
                 (->F q (make-&&-pf q pfs) % [f] (delay ((f->pf f) %)))
                 %)
              {:expand true}))]
    (let [ps (into [p1 p2] pn)
          q (delay (cons 'p-&& (map p->q ps)))]
      (->P q ps (make-&&-pf q (map p->pf ps))
           (delay (apply p-&& (map p->next-p ps)))))))

(defn- make-or-pf [q pfs]
  (with-meta
    #(if-let [fs (loop [fs [], pfs* pfs]
                   (if (seq pfs*)
                     (cata-p ((first pfs*) %)
                       f (recur (conj fs f) (rest pfs*))
                       _ nil)
                     fs))]
       (->F q (make-or-pf q pfs) %
            fs
            ;; all failed => expand them all
            (delay (let [fs* (expand-failures fs)]
                     ((make-or-pf (delay (cons 'p-or (map f->q fs*)))
                                  (map f->pf fs*))
                      (f->s (first fs*))))))
       %)
    {:expand true}))

(defn p-or
  "Return a new predicate that is the disjunction of predicates P1, P2 ... PN.

  Examples:

  > ((p-or (between? 2 4) (p odd?)) 2)
  ;; => 2

  > ((p-or (between? 2 4) (p odd?)) 1)
  ;; => 1

  > ((p-or (between? 2 4) (p odd?)) 0)
  ;; => #F[((p-&& (between? 2 4) (p odd?)) 0)]

  (expand-root-f *1)
  ;; => #F[((p-or (gte? 2) (p odd?)) 0)]

  See also: p-and, p-some
  "
  [p1 p2 & pn] (let [ps (into [p1 p2] pn)
                     q (delay (cons 'p-or (map p->q ps)))]
                 (->P q ps (make-or-pf q (map p->pf ps))
                      (delay (apply p-or (map p->next-p ps))))))

(defn p-not
  "Lift a predicate P into a predicate that succeeds if P fails.

  Examples:

  > ((p-not (p-or (between? 2 4) (p odd?))) 2)
  ;; => #F[((p-not (p-or (between? 2 4) (p odd?))) 2)]

  > (expand-root-f *1)
  ;; => #F[((p-or (p-not (gte? 2)) (p-not (lt? 4))) 2)]

  > ((p-not (p-or (between? 2 4) (p odd?))) 1)
  ;; => #F[((p-not (p-or (between? 2 4) (p odd?))) 1)]

  > (expand-root-f *1)
  ;; => #F[((p-not (p odd?)) 1)]

  > ((p-not (p-or (between? 2 4) (p odd?))) 0)
  ;; => 0

  See also: p-no
  "
  [p]
  (letfn [(make-not-pf [q p]
            #(cata-p ((p->pf p) %)
               f %
               _ (->F q (make-not-pf q p) %
                      (delay
                       (let [ops (p->ops p)]
                         ((case (first (p->q p))
                            p-not (p->pf (first ops))
                            p-q (p-q (first ops) (p-not (second ops)))
                            p-or (make-and-pf
                                  (delay (list 'p-and (map list
                                                           (repeat 'p-not)
                                                           (map p->q ops))))
                                  (map (comp p->pf p-not) ops))
                            p-and (make-or-pf
                                   (delay (list 'p-or (map list
                                                           (repeat 'p-not)
                                                           (map p->q ops))))
                                   (map (comp p->pf p-not) ops))
                            (let [p* (p->next-p p)]
                              (make-not-pf (delay (list 'p-not (p->q p*)))
                                           p*)))
                          %))))))]
    (let [q (delay (list 'p-not (p->q p)))]
      (->P q [p] (make-not-pf q p)
           (delay (p-not (p->next-p p)))))))


;;;
;;; Categorical proposition operators
;;; https://en.wikipedia.org/wiki/Categorical_proposition
;;;

(defn p-all
  "Lift a predicate P into a predicate that succeeds if all the elements of a
  collection passed as its subject satisfy it.

  Examples:

  > ((p-all (between? 2 3)) [1 2 3 4])
  ;; => #F[((p-all (between? 2 3)) [1 3 4])]

  > (expand-root-f *1)
  ;; => #F[((p-all (p-and (gte? 2) (lt? 3))) [1 3 4])]

  > ((p-all (between? 2 5)) [1 2 3 4])
  ;; => #F[((p-all (between? 2 5)) [1])]

  > (expand-root-f *1)
  ;; => #F[((gte? 2) 1)]

  > ((p-all (between? 2 5)) [2 3 4])
  ;; => [2 3 4]

  > ((p-all (between? 2 5)) [4 6 7])
  ;; => #F[((p-all (between? 2 5)) [4 6 7])]

  > (expand-root-f *1)
  ;; => #F[((p-all (lt? 5)) [6 7])]
   "
  [p] (letfn [(make-all-pf [q pf]
                #(let [fs (reduce (fn [fs s] (cata-p (pf s) f (conj fs f) _ fs))
                                  []
                                  %)]
                   (if (seq fs)
                     (let [ss (mapv f->s fs)]
                       (->F q pf ss
                            (delay
                             (if (seq (rest fs))
                               (let [fs* (map (comp f->next-f) fs)]
                                 (if (apply = (map f->q fs*))
                                   (let [f* (first fs*)
                                         q* (delay (list 'p-all (f->q f*)))
                                         pf* (f->pf f*)]
                                     (->F q* pf* ss
                                          (delay (f->next-f
                                                  ((make-all-pf q* pf*) ss)))))
                                   ;; can't reduce more
                                   nil))
                               (first fs)))))
                     %)))]
        (let [q (delay (list 'p-all (p->q p)))]
          (->P q [p] (make-all-pf q (with-meta (p->pf p) {:narrow true}))
               (delay (p-all (p->next-p p)))))))

(defn p-no
  "Lift a predicate P into a predicate that succeeds if none of the elements of a
  collection passed as its subject satisfy it.

  Examples:

  > ((p-no (p odd?)) [1 2])
  ;; => #F[((p-no (p odd?)) [1])]

  > (expand-root-f *1)
  ;; => #F[((p-not (p odd?)) 1)]

  > ((p-no (p odd?)) [2 4])
  ;; => [2 4]

  See also: p-all
  "
  [p] (let [p* (p-all (p-not p))
            q (delay (list 'p-no (p->q p)))]
        (->P q [p] #(let [pf (f->pf p*)]
                      (cata-p (pf %)
                        f (let [ss (f->s f)]
                            (->F q (with-meta pf {:narrow true}) ss
                                 (if (seq (rest ss))
                                   (delay ((p-no p) ss))
                                   (.next-f f))))))
             (.next-p p*))))

(defn p-some
  "Lift a predicate P into a predicate that succeeds if one of the elements of a
  collection passed as its subject satisfy it.

  Examples:
  > ((p-some (between? 2 3)) [1 2 3 4])
  ;; [1 2 3 4]

  > ((p-some (between? 0 1)) [1 2 3 4])
  ;; => #F[((p-some (between? 0 1)) [1 2 3 4])]

  > (expand-root-f *1)
  ;; => #F[((p-some (lt? 1)) [1 2 3 4])]

  > ((p-some (between? 2 3)) [1 3 4])
  ;; => #F[((p-some (between? 2 3)) [1 3 4])]

  > (expand-root-f *1)
  ;; => #F[((p-some (p-and (gte? 2) (lt? 3))) [1 3 4])]

  See also: p-all, p-some-not
  "
  [p] (letfn [(make-some-pf [q pf]
                #(let [fs (loop [fs [], ss %]
                            (if (seq ss)
                              (cata-p (pf (first ss))
                                f (recur (conj fs f) (rest ss))
                                _ nil)
                              fs))]
                   (if (seq fs)
                     (->F q pf %
                          (delay
                           (if (seq (rest fs))
                             (let [fs* (map (comp f->next-f) fs)]
                               (if (apply = (map f->q fs*))
                                 (let [f* (first fs*)
                                       q* (delay (list 'p-some (f->q f*)))
                                       pf* (f->pf f*)]
                                   (->F q* pf* %
                                        (delay (f->next-f ((make-some-pf q* pf*)
                                                           %)))))
                                 ;; can't reduce more
                                 nil))
                             (first fs))))
                     %)))]
        (let [q (delay (list 'p-some (p->q p)))]
          (->P q [p] (make-some-pf q (with-meta (p->pf p) {:narrow true}))
               (delay (p-some (p->next-p p)))))))

(defn p-some-not
  "Lift a predicate P into a predicate that succeeds if one of the elements of a
  collection passed as its subject does not satisfy it.

  Examples:

  > ((p-some-not (p odd?)) [1 2])
  ;; => [1 2]

  > ((p-some-not (p odd?)) [1 3])
  ;; => #F[((p-some-not (p odd?)) [1 3])]
  "
  [p] (let [p* (p-some (p-not p))
            q (delay (list 'p-some-not (p->q p)))]
        (->P q [p] #(let [pf (f->pf p*)]
                      (cata-p (pf %)
                        f (let [ss (f->s f)]
                            (->F q (with-meta pf {:narrow true}) ss
                                 (if (seq (rest ss))
                                   (delay ((p-some-not p) ss))
                                   (.next-f f))))))
             (.next-p p*))))


;;;
;;; Functor/Applicative
;;;

(defn app-p
  "Apply a function F to the proposition results PS only if none
  of them is a failure. Otherwise return the first failure.

  Examples:

  > (app-p + ((p odd?) 1) ((p even?) 2))
  ;;=> 3

  > (app-p + ((p odd?) 1) ((p even?) 3))
  ;; => #F[((p even?) 3)]

  > (app-p + ((p even?) 1) ((p even?) 3))
  ;; => #F[((p-and (q-nth 0 (p even?)) (q-nth 1 (p even?))) [1 3])]

  See also: p-&&
  "
  [f & ps] (let [fs (filter (fn [p] (cata-p p f f _ nil)) ps)]
             (case (count fs)
               0 (apply f ps)
               1 (first fs)
               (letfn [(nth-pf [i pf]
                         (fn [s]
                           (cata-p (pf (nth s i))
                             f (->F (delay
                                     (list 'q-nth i (f->q f)))
                                    (nth-pf i (f->pf f))
                                    s
                                    (delay f)))))]
                 ((make-and-pf (delay
                                (cons 'p-and
                                      (map-indexed (fn [i q]
                                                     (list 'q-nth i q))
                                                   (map f->q fs))))
                               (map-indexed nth-pf (map f->pf fs)))
                  (mapv f->s fs))))))


;;;
;;; Monad
;;;

(defn ^:no-doc bind-p* [[s p] expr]
  `(let [r# ~p]
     (cata-p r#
       ~'_ r#
       ~s ~expr)))

(defmacro bind-p
  "Evaluate the expression EXPR where the symbol S is bound to the success of a
  proposition P. If P fails, return its failure without evaluating EXPR.

  Examples:

  > (bind-p [a ((p even?) 1)]
      (inc a))
  ;; => #F[((p even?) 1)]

  > (bind-p [a ((p even?) 2)]
      (inc a))
  ;; => 3

  See also: let-p
  "
  [[s p] expr] (bind-p* [s p] expr))

(defmacro let-p
  "Haskell like do-notation macro that shortcuts the execution when one
  intermediate proposition is a failure. In this last case, it returns the
  failure itself.

  Examples:

  (let-p [a ((p odd?) 1)
          a* (+ a 2)
          b (* a* a*)]
    ((p odd?) b))
  ;; => 9

  (let-p [a ((p even?) 1)
          a* (+ a 2)
          b (* a* a*)]
    ((p odd?) b))
  ;; => #F[((p even?) 1)]

  See also: bind-p, app-p, p-&&
  "
  [bindings body-expr]
  (letfn [(-bind [expr binding]
            (let [[lhs rhs] binding]
              (bind-p* binding expr)))]
    (when bindings
      (let [rbindings (reverse (partition 2 bindings))]
        (reduce -bind body-expr rbindings)))))

