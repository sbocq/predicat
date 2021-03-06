(ns ^{:doc "The core Predicat library permits to create and compose predicate of
  type P for validating the inputs of a program. A predicate object P is a
  function object of one argument S that captures its quoted expression Q. It
  returns its subject S upon success, or otherwise a proposition failure object
  of type F. Failure objects reference the predicate object P and the subject S
  on which failed. The library contains macros (`p', `p<', `defp', `defpp') to
  create predicates by embedding plain Clojure functions or functions (`p-and',
  `p-or', `p-not', `p-some', ...) to compose existing predicates into new ones.
  Results, which are either a failure object or any other object, can be
  manipulated without nesting conditionnal statements in applicative or monadic
  forms (`app-p', `let-p'). Predicates composed from other predicates can be
  expanded by evaluating them as nullary function or by using one of the
  `p-expand*' function. Proposition failures can be inspected iteratively by
  evaluating them as nullary functions or by using one of the `explain-f*'
  functions."}  predicat.core)

(comment
  "
Glossary:

- A predicate object of type P captures its expression Q and the predicate
  function PF to which it compiles.

- A predicate function PF is a function of a subject S that return its argument S
  when successful or else a proposition failure F.

- A proposition failure object of type F captures the predicate object P and the
  subject S on which it fails.

Conventions:

- Functions suffixed by `-p' take a proposition result as argument.

- Functions prefixed by `p-' compose predicates.

- Functions suffixed by `-f' take a proposition failure as argument.

- Parameters named `q' denote a quoted expression.

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
  "If true, include primitive predicates while expanding failures (default:
  false)."
  false)

(defn- primitive-q?
  "Return true if the predicate expression Q is a primitive expression."
  [q] (and (not (symbol? q))         ;predicate symbol defined by user
           (= 'p (first q))))        ;primitive expressions start with 'p


;;;
;;; Predicate type P
;;;

(declare p->next-p)

(deftype P [q ops pf next-p]
  clojure.lang.IFn
  (invoke [this] (p->next-p this))      ;expand predicate
  (invoke [_ s] (pf s)))                ;apply predicate

(defn ^:no-doc ->P
  "Create a predicate object of type P. Its parameters are the (delayed)
  predicate expression Q,the predicate operands OPS (nil if none), the predicate
  function PF evaluated from Q, and the (delayed) predicate NEXT-P to which it
  expands (nil if none i.e. predicate is a primitive)."
  ([q ops pf] (P. q ops pf (delay nil)))
  ([q ops pf next-p] (P. q ops pf next-p)))

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
            (when (or *expand-to-primitives* (not (primitive-q? (p->q next-p))))
              next-p))
          p))

(defmethod print-method P [p ^java.io.Writer w]
  (.write w (str "#P[" (p->q p) "]")))

(defn p-expand-all
  "Return the vector of the expansions of predicate P.

  Example:

  > (p-expand-all (between? 1 2))
  ;; => [#P[(between? 1 2)] #P[(p-and (gte? 1) (lt? 2))]]
  "
  [p]
  {:pre [(instance? P p)]}
  (loop [acc [p], p p]
    (let [next-p (p->next-p p)]
      (if (= (p->q p) (p->q next-p)) acc (recur (conj acc next-p) next-p)))))

(defn p-expand-last
  "Return the last expansion of predicate P. "
  [p] (last (p-expand-all p)))

(defn p-explain
  "Print the expansions of predicate P."
  [p] (doseq [p (p-expand-all p)] (prn p)))


;;;
;;; Proposition failure type F
;;;

(declare iexpand-f)

(deftype F [p s next-f fs]
  clojure.lang.IFn
  (invoke [this] (iexpand-f this))      ;expand failure
  (invoke [this index] (iexpand-f this index))) ;expand nth sub-failure

(defn ^:no-doc ->F
  "Create a proposition failure object of type F. Its parameters are the
  predicate P that fails, the subject S that does not satisy P such that
  `(equal failure (p s))', the (delayed) failure NEXT-F to which this expression
  can be expanded (nil if none), and the vector of its sub-failures FS."
  ([p s] (->F p s (delay nil)))
  ([p s next-f] (->F p s next-f []))
  ([p s next-f fs] (F. p s next-f fs)))

(defn f->p
  "Return the predicate that failed for failure F."
  [f] (.p f))

(defn f->q
  "Return the quoted expression of the predicate that failed in failure F."
  [f] (p->q (f->p f)))

(defn f->pf
  "Return the predicate function of the predicate that failed in failure F."
  [f] (p->pf (f->p f)))

(defn f->s
  "Return the subject of failure F."
  [f] (.s f))

(defn f->next-f
  "Expand a failure F to the next most specific failure."
  [f] (or (when-let [next-f @(.next-f f)]
            (when (or
                   ;; Expand next-f even if it is primitive expression
                   *expand-to-primitives* (:expand (meta (f->pf f)))
                   ;; or expand to next-f if it is not a primitive expression
                   (not (primitive-q? (f->q next-f)))
                   ;; unless it narrows the subject
                   (not (= (f->s f) (f->s next-f))))
              next-f))
          f))

(defn f->fs
  "Return the vector of sub failures, if any."
  [f] (.fs f))

(defmethod print-method F [f ^java.io.Writer w]
  (.write w (str "#F[(" (f->q f) " " (with-out-str (pr (f->s f))) ")]")))

(defn- iexpand-f
  "Expand failure F interactively and dipslay multiple choices if any."
  ([f] (let [next-f (f->next-f f)]
         (when-let [fs (seq (f->fs next-f))]
           (when (next fs)
             (doseq [[i f*] (map-indexed vector fs)]
               (printf "%d. (%s %s)%n"
                       (inc i) (f->q f*) (with-out-str (pr (f->s f*)))))))
         next-f))
  ([f index] (nth (f->fs (f->next-f f)) (dec index) nil)))

(defn get-stack-f
  "Collect the consecutive (linear) expansions of a proposition failure F into a
  vector until it can't be expanded further. Expansions depth can be controlled
  with the dynamic variables *narrow-subject* and *expand-to-primitives*.

  Examples:

  > (get-stack-f ((between? 1 2) 3))
  ;; => [#F[((between? 1 2) 3)]
         #F[((p-and (gte? 1) (lt? 2)) 3)]
         #F[((lt? 2) 3)]]
  "
  [f]
  {:pre [(instance? F f)]}
  (loop [acc [f], f f]
    (let [next-f (or (let [next-f (f->next-f f)]
                       (when (or
                              ;; Expand next-f, even if subject is more specific
                              *narrow-subject* (:narrow (meta (f->pf f)))
                              ;; or expand only if the subject is preserved.
                              (= (f->s f) (f->s next-f)))
                         next-f))
                     f)]
      (if (and (= (f->q f) (f->q next-f)) (= (f->s f) (f->s next-f)))
        acc
        (recur (conj acc next-f) next-f)))))

(defn get-root-f
  "Return the last linear expansion of a proposition failure F or its nth
  subfailure."
  ([f] (last (get-stack-f f)))
  ([f index] (last (get-stack-f (f index)))))

(defn explain-f
  "Print the expansions of a proposition failure F, narrowing on its subject if
  possible."
  [f] (binding [*narrow-subject* true]
        (doseq [f (get-stack-f f)] (prn f))))


;;;
;;; Catamorphism for proposition results
;;;

(defmacro cata-p
  "For a proposition EXPR whose result is a failure, evaluate F-EXPR in a lexical
  scope where where F is bound to the failure. When it is a success, evaluate
  S-EXPR where S is bound to the success. If S and S-EXPR are omitted, return S
  in case of success.

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

(defn is-f?
  "Test if proposition result P is a failure. Return it if it is a failure,
  otherwise nil."
  [p] (cata-p p f f _ nil))


;;;
;;; Custom constructors with private helpers
;;;

(defn- scrub-fn
  "Clean up \"...__auto__...\" and \"...#\" symbols from simple expressions.

  Example:

  > (scrub-fn '(fn [a] (> a 1) #(> b %)))
  ;; => (fn [a] (> a 1) (fn* [c] (> b c))))
  "
  [form]
  (if (seq? form)
    (case (first form) (fn fn*)
          (let [[ps & body] (rest form)
                all-letters (map (comp str char) (range (int \a) (int\z)))
                [smap]
                (reduce (fn [[smap free :as state] sym]
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
                                    [(assoc smap (first e) (symbol (first free)))
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

(defn ^:no-doc p*
  "See p"
  [q f] (->P q nil (fn [s] (if (f s) s (->F (p* q f) s)))))

(defmacro p
  "Create a primitive predicate (of type P) from a function expression of a
  single argument FN-EXPR. This predicate will return a failure when the function
  returns nil or false.

  Example:

  > (p #(>= % 1))
  ;; => #P[(p (fn [a] (>= a 1)))]
  "
  ;; Macros capture quoted expression without substituting variables bound in the
  ;; lexical environment. We have to do it ourselves.
  [fn-expr] (let [q (list 'p (clojure.walk/prewalk scrub-fn fn-expr))
                  names (keys &env)
                  quoted (list 'quote names)]
              `(p* (delay (clojure.walk/prewalk-replace
                           (zipmap ~quoted ~(cons 'list names)) '~q))
                   ~fn-expr)))

(defn ^:no-doc p<*
  "See p<"
  [q fn-p] (->P q nil (fn [s] (cata-p ((fn-p s) s)
                                f (->F (p<* q fn-p) s (delay f))))))

(defmacro p<
  "Create a primitive predicate (of type P) from a function that returns a
  predicate that depends on the subject.

  Examples:

  > ((p< #(if (< % 10) (p even?) (p odd?))) 7)
  ;; => #F[((p< (fn [a] (if (< a 10) (p even?) (p odd?)))) 7)]
  > ((p< #(if (< % 10) (p even?) (p odd?))) 6)
  ;; => 6

  > ((p< #(if (< % 10) (p even?) (p odd?))) 17)
  ;; => 17
  > ((p< #(if (< % 10) (p even?) (p odd?))) 16)
  ;; => #F[((p< (fn [a] (if (< a 10) (p even?) (p odd?)))) 16)]
  "
  [fn-p-expr] (let [q (list 'p< (clojure.walk/prewalk scrub-fn fn-p-expr))
                    names (keys &env)
                    quoted (list 'quote names)]
                `(p<* (delay (clojure.walk/prewalk-replace
                              (zipmap ~quoted ~(cons 'list names)) '~q))
                      ~fn-p-expr)))

(defn ^:no-doc requote-p*
  [q p] (->P q nil (fn [s] (cata-p ((p->pf p) s)
                             f (->F (requote-p* q p) s (delay f))))
             (delay p)))

(defmacro defpp
  "Define a Parameterized Predicate. Bind a predicate expression
  P-EXPR (of type P) with free variables ARGS to a NAME.

  Example:

  > (defpp gte? [min] (p #(>= % min)))
  ;; => #'gte?
  "
  [name args p-expr]
  `(defn ~name ~args (requote-p* (delay (list '~name ~@args)) ~p-expr)))

(defmacro defp
  "Define a Predicate. Bind a predicate expression P-EXPR (of type P) to a NAME.

  Example:

  > (defp gte-10? (gte? 10))
  ;; => #'gte-10?
  "
  [name p-expr]
  `(def ~name (requote-p* (delay '~name) ~p-expr)))


;;;
;;; Custom queries to focus on a subject attribute
;;;

(deftype Q [q qf]
  clojure.lang.IFn
  (invoke [_ s] (qf s)))                ;apply

(defn ^:no-doc ->Q
  "Create a query object of type Q. Its parameters are a (delayed) expression Q,
  and a query function QF."
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
  ;; Same trick as for macro 'p
  [q-expr] (let [q (list 'q (clojure.walk/prewalk scrub-fn q-expr))
                 names (keys &env)
                 quoted (list 'quote names)]
             `(let [q# (delay (clojure.walk/prewalk-replace
                               (zipmap ~quoted ~(cons 'list names)) '~q))]
                (->Q q# ~q-expr))))

(defn ^:no-doc p-q
  "Return a new predicate that applies predicate P to the subject obtained by
  applying a QUERY to it main subject.

  Examples:

  > (defpq q-in [ks] (q #(get-in % ks)))
  ;; => #'q-in

  > ((p-q (q-in [:a :b]) (p odd?)) {:a {:b 1}})
  ;; => {:a {:b 1}}
  ;; same as:
  > ((q-in [:a :b] (p odd?)) {:a {:b 1}})
  ;; => {:a {:b 1}}

  > ((q-in [:a :b] (p even?)) {:a {:b 1}})
  ;; => #F[((q-in [:a :b] (p even?)) {:a {:b 1}})]

  > (get-root-f *1)
  ;; => #F[((q-in [:a :b] (p even?)) {:a {:b 1}})]

  > (binding [*narrow-subject* true]
      (get-root-f *1))
  ;; => #F[((p even?) 1)]
  "
  [query p]
  (->P (delay (seq (concat (q->q query) [(p->q p)])))
       [query]
       (with-meta
         #(cata-p ((p->pf p) ((q->qf query) %))
            f (->F (p-q query p) %
                   (delay
                    (let [next-f (f->next-f f)]
                      ;; Expand inner failure only if it preserves the subject.
                      (if (and (not (= (f->q f) (f->q next-f)))
                               (= (f->s f) (f->s next-f)))
                        ((p-q query (f->p next-f)) %)
                        f)))
                   [f])
            _ %)
         {:expand true})
       (delay (p-q query (p->next-p p)))))

(defmacro defpq
  "Define a Parameterized Query. Bind a query Q-EXPR (of type Q) with free
  variables ARGS to a NAME.

  Examples:

  > (defpq q-in [ks] (q #(get-in % ks)))
  ;; => #'q-in

  > ((q-in [:age] (p #(>= % 1))) {:age 1})
  ;; => {:age 1}
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

(defn- expand-failures
  "Expand a sequence of failures FS in such a manner that the resulting expanded
  failures have all the same subject."
  [fs] (let [next-fs (map f->next-f fs)]
         (if (apply = (map f->s next-fs))
           next-fs
           (let [s (f->s (first fs))]
             (reduce (fn [fs [f next-f]]
                       (conj fs (if (= s (f->s next-f)) next-f f)))
                     []
                     (map list fs next-fs))))))

(defn p-and
  "Return a new predicate that is the conjunction of the predicates P1, P2 ...
  PN.

  Examples:

  > ((p-and (between? 2 4) (p odd?)) 0)
  ;; => #F[((p-and (between? 2 4) (p odd?)) 0)]

  > (get-root-f *1)
  ;; => #F[((p-and (gte? 2) (p odd?)) 0)]

  > ((p-and (between? 2 4) (p odd?)) 1)
  ;; => #F[((p-and (between? 2 4) (p odd?)) 1)]

  > (get-root-f *1)
  ;; => #F[((gte? 2) 1)]

  > ((p-and (between? 2 4) (p odd?)) 2)
  ;; => #F[((p-and (between? 2 4) (p odd?)) 2)]

  > (get-root-f *1)
  ;; => #F[((p odd?) 2)]

  > ((p-and (between? 2 4) (p odd?)) 3)
  ;; => 3

  See also: p-&&, p-or, p-all
  "
  ([p] p)
  ([p1 p2 & pn]
   (let [ps (into [p1 p2] pn)]
     (->P (delay (cons 'p-and (map p->q ps)))
          ps
          (with-meta
            #(let [fs (reduce (fn [fs p] (cata-p ((p->pf p) %)
                                           f (conj fs f)
                                           _ fs))
                              []
                              ps)]
               (if (seq fs)
                 (->F (apply p-and ps) %
                      (delay
                       (if (next fs)
                         ;; multiple predicates failed
                         (let [fs* (expand-failures fs)]
                           ((apply p-and (map f->p fs*)) (f->s (first fs*))))
                         ;; single predicate failed, get rid of 'p-and op
                         (first fs)))
                      (vec fs))
                 %))
            ;; bypass *expand-to-primitive* directive e.g. (p-and (p foo)) must
            ;; be expanded to (p foo)
            {:expand true})
          (delay (apply p-and (map p->next-p ps)))))))

(defn p-&&
  "Create a conjunction from a sequence of predicates that short circuits the
  evaluation of the remaining propositions on the first failure.

  > ((p-&& (between? 2 4) (p odd?)) 0)
  ;; => #F[((p-&& (between? 2 4) (p odd?)) 0)]

  > (get-root-f *1)
  ;; => #F[((gte? 2) 1)]

  > ((p-&& (between? 2 4) (p odd?)) 2)
  ;; => #F[((p-&& (between? 2 4) (p odd?)) 2)]

  > (get-root-f *1)
  ;; => #F[((p odd?) 2)]

  > ((p-&& (between? 2 4) (p odd?)) 3)
  ;; => 3

  See also: p-and
  "
  [p1 p2 & pn]
  (let [ps (into [p1 p2] pn)]
    (->P (delay (cons 'p-&& (map p->q ps)))
         ps
         (with-meta
           #(if-let [f (some (fn [p] (is-f? (p %))) ps)]
              (->F (apply p-&& ps) % (delay f))
              %)
           {:expand true})
         (delay (apply p-&& (map p->next-p ps))))))

(defn p-or
  "Return a new predicate that is the disjunction of predicates P1, P2 ... PN.

  Examples:

  > ((p-or (between? 2 4) (p odd?)) 2)
  ;; => 2

  > ((p-or (between? 2 4) (p odd?)) 1)
  ;; => 1

  > ((p-or (between? 2 4) (p odd?)) 0)
  ;; => #F[((p-&& (between? 2 4) (p odd?)) 0)]

  (get-root-f *1)
  ;; => #F[((p-or (gte? 2) (p odd?)) 0)]

  See also: p-and, p-some
  "
  [p1 p2 & pn]
  (let [ps (into [p1 p2] pn)]
    (->P (delay (cons 'p-or (map p->q ps)))
         ps
         (with-meta
           #(if-let [fs (loop [fs [], ps* ps]
                          (if (seq ps*)
                            (cata-p ((p->pf (first ps*)) %)
                              f (recur (conj fs f) (rest ps*))
                              _ nil)
                            fs))]
              (->F (apply p-or ps) %
                   (delay (let [fs* (expand-failures fs)]
                            ((apply p-or (map f->p fs*)) (f->s (first fs*)))))
                   fs)
              %)
           {:expand true})
         (delay (apply p-or (map p->next-p ps))))))

(defn p-not
  "Lift a predicate P into a predicate that succeeds if P fails.

  Examples:

  > ((p-not (p-or (between? 2 4) (p odd?))) 2)
  ;; => #F[((p-not (p-or (between? 2 4) (p odd?))) 2)]

  > (get-root-f *1)
  ;; => #F[((p-or (p-not (gte? 2)) (p-not (lt? 4))) 2)]

  > ((p-not (p-or (between? 2 4) (p odd?))) 1)
  ;; => #F[((p-not (p-or (between? 2 4) (p odd?))) 1)]

  > (get-root-f *1)
  ;; => #F[((p-not (p odd?)) 1)]

  > ((p-not (p-or (between? 2 4) (p odd?))) 0)
  ;; => 0

  See also: p-no
  "
  [p] (->P (delay (list 'p-not (p->q p)))
           [p]
           #(cata-p ((p->pf p) %)
              f %
              _ (->F (p-not p) %
                     (delay (let [ops (p->ops p)]
                              ((case (first (p->q p))
                                 p-not (first ops)
                                 p-q (p-q (first ops) (p-not (second ops)))
                                 p-or (apply p-and (map p-not ops))
                                 p-and (apply p-or (map p-not ops))
                                 (p-not (p->next-p p)))
                               %)))))
           (delay (p-not (p->next-p p)))))


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

  > (get-root-f *1)
  ;; => #F[((p-all (p-and (gte? 2) (lt? 3))) [1 3 4])]

  > ((p-all (between? 2 5)) [1 2 3 4])
  ;; => #F[((p-all (between? 2 5)) [1])]

  > (get-root-f *1)
  ;; => #F[((gte? 2) 1)]

  > ((p-all (between? 2 5)) [2 3 4])
  ;; => [2 3 4]

  > ((p-all (between? 2 5)) [4 6 7])
  ;; => #F[((p-all (between? 2 5)) [4 6 7])]

  > (get-root-f *1)
  ;; => #F[((p-all (lt? 5)) [6 7])]
   "
  [p] (->P (delay (list 'p-all (p->q p)))
           [p]
           (with-meta
             #(if-let [fs (let [pf (p->pf p)]
                            (seq (keep (fn [s] (is-f? (pf s))) %)))]
                (let [ss (mapv f->s fs)]
                  (->F (p-all p) ss
                       (delay (if (next fs)
                                (let [fs* (map f->next-f fs)]
                                  (when (apply = (map f->q fs*))
                                    ((p-all (f->p (first fs*))) ss)))
                                (first fs)))))
                %)
             {:narrow true})
           (delay (p-all (p->next-p p)))))

(defn p-no
  "Lift a predicate P into a predicate that succeeds if none of the elements of a
  collection passed as its subject satisfy it.

  Examples:

  > ((p-no (p odd?)) [1 2])
  ;; => #F[((p-no (p odd?)) [1])]

  > (get-root-f *1)
  ;; => #F[((p-not (p odd?)) 1)]

  > ((p-no (p odd?)) [2 4])
  ;; => [2 4]

  See also: p-all
  "
  [p] (let [p* (p-all (p-not p))]
        (->P (delay (list 'p-no (p->q p)))
             [p]
             (with-meta
               #(cata-p ((p->pf p*) %)
                  f (let [ss (f->s f)]
                      (->F (p-no p) ss (delay (if (next ss)
                                                ((p-no (f->p f)) ss)
                                                (f->next-f f))))))
               {:narrow true})
             (.next-p p*))))

(defn p-some
  "Lift a predicate P into a predicate that succeeds if one of the elements of a
  collection passed as its subject satisfy it.

  Examples:

  > ((p-some (between? 2 3)) [1 2 3 4])
  ;; [1 2 3 4]

  > ((p-some (between? 0 1)) [1 2 3 4])
  ;; => #F[((p-some (between? 0 1)) [1 2 3 4])]

  > (get-root-f *1)
  ;; => #F[((p-some (lt? 1)) [1 2 3 4])]

  > ((p-some (between? 2 3)) [1 3 4])
  ;; => #F[((p-some (between? 2 3)) [1 3 4])]

  > (get-root-f *1)
  ;; => #F[((p-some (p-and (gte? 2) (lt? 3))) [1 3 4])]

  See also: p-all, p-some-not
  "
  [p] (->P (delay (list 'p-some (p->q p)))
           [p]
           #(if-let [fs (seq (let [pf (p->pf p)]
                               (loop [fs [], ss %]
                                 (if (seq ss)
                                   (cata-p (pf (first ss))
                                     f (recur (conj fs f) (rest ss))
                                     _ nil)
                                   fs))))]
              (->F (p-some p) %
                   (delay (if (next fs)
                            (let [fs* (map (comp f->next-f) fs)]
                              (when (apply = (map f->q fs*))
                                ((p-some (f->p (first fs*))) %)))
                            (first fs))))
              %)
           (delay (p-some (p->next-p p)))))

(defn p-some-not
  "Lift a predicate P into a predicate that succeeds if one of the elements of a
  collection passed as its subject does not satisfy it.

  Examples:

  > ((p-some-not (p odd?)) [1 2])
  ;; => [1 2]

  > ((p-some-not (p odd?)) [1 3])
  ;; => #F[((p-some-not (p odd?)) [1 3])]
  "
  [p] (let [p* (p-some (p-not p))]
        (->P (delay (list 'p-some-not (p->q p)))
             [p]
             (with-meta
               #(cata-p ((p->pf p*) %)
                  f (let [ss (f->s f)]
                      (->F (p-some-not p) ss (delay (if (next ss)
                                                      ((p-some-not p) ss)
                                                      (f->next-f f))))))
               {:narrow true})
             (.next-p p*))))

(defn chk-seq
  "[x s] -> x [s]. Take a sequence of proposition results and return it if there
  are only successes. Otherwise, turn it into a proposition failure for the
  vector of failed subjects.

  Examples:

  > (chk-seq [((p odd?) 1) ((p even?) 2)])
  ;; => [1 2]

  > (chk-seq [((p odd?) 1) ((p even?) 3)])
  ;; => #F[((q-nth 0 (p even?)) [3])]

  > (chk-seq [((p even?) 1) ((p even?) 3)])
  ;; => #F[((p-and (q-nth 0 (p even?)) (q-nth 1 (p even?))) [1 3])]

  See also: app-p, explode-f
  "
  [ps] (if-let [fs (seq (filter is-f? ps))]
         ((apply p-and (map-indexed q-nth (map f->p fs))) (mapv f->s fs))
         ps))

(defn explode-f
  "f [s] -> [f s]. Take a proposition failure for a vector of failed subjects
  and turn it into a vector of proposition failures.

  Examples:

  > (explode-f ((p-and (q-nth 0 (p even?)) (q-nth 1 (p even?))) [1 3]))
  ;; => [#F[((p even?) 1)] #F[((p even?) 3)]]

  > (explode-f ((p-all (between? 2 3)) [1 2 3 4]))
  ;; => [#F[((between? 2 3) 1)] #F[((between? 2 3) 3)] #F[((between? 2 3) 4)]]

  > (explode-f ((between? 2 3) 3))
  ;; => [#F[((between? 2 3) 3)]]

  See also: chk-seq
  "
  [f] (case (first (f->q f))
        p-all (mapv (first (p->ops (f->p f))) (f->s f))
        p-and (vec (map f->next-f (f->fs f)))
        [f]))


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
  ;; => #F[((q-nth 0 (p even?)) [3])]

  > (app-p + ((p even?) 1) ((p even?) 3))
  ;; => #F[((p-and (q-nth 0 (p even?)) (q-nth 1 (p even?))) [1 3])]

  See also: p-&&
  "
  [f & ps] (if (seq (rest ps))
             (cata-p (chk-seq ps) f* f* _ (apply f ps))
             (let [p (first ps)] (cata-p p f* f* _ (f p)))))


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
  "Macro similar to when-let, which shortcuts subsequent bindings when one
  intermediate value is a proposition failure. In this case, it returns the
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
