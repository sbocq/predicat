[![License](https://img.shields.io/badge/License-EPL%201.0-red.svg)](https://opensource.org/licenses/EPL-1.0)
[![Build Status](https://travis-ci.org/sbocq/predicat.svg?branch=master)](https://travis-ci.org/sbocq/predicat)

# Predicat

Predicat is a library to create and compose predicates with traceable failures.

This library meets the following design goals:

- Introduce little additional syntax. Predicates are defined using
  plain Clojure functions.

- Report self-describing failures. Failures report the failing expressions
  instead of some English strings defined by the end users.

- Permit to compose predicates. New predicates can be composed from existing
  predicates.

- Is applicable to the validation of values nested in arbitrary data
  structures. Predicates can be applied to the result of queries defined by the
  end user, which are then reported in failures to indicate where they occur.

## Install

Add the following dependency to your `project.clj` file:

    [predicat "0.1.1"]

## Usage

Here is a brief tutorial. See also the `example` directory for more examples.

### Part I. Create and compose predicates.

```clojure
;; A primitive predicate is a function object of type #P
(p #(>= % 1))
;; => #P[(p (fn [a] (>= a 1)))]

;; that returns its subject when successful
((p #(>= % 1)) 1)
;; => 1

;; or a failure of type #F that reports the expression that fails.
((p #(>= % 1)) 0)
;; => #F[((p (fn [a] (>= a 1))) 0)]

;; Here is how to define parameterized predicates and then compose them together.
(defpp gte? [min] (p #(>= % min)))
(defpp lt? [max] (p #(< % max)))
(defpp between? [min max] (p-and (gte? min) (lt? max)))

;; This application succeeds
((between? 7 77) 18)
;; => 18

;; This application fails
((between? 7 77) 78)
;; => #F[((between? 7 77) 78)

;; This is how you get to the root cause
(expand-root-f *1)
;; => #F[((lt? 77) 78)]                 ;too old!

;; and a full explanation
(explain-f *2)
#F[((between? 7 77) 78)]
#F[((p-and (gte? 7) (lt? 77)) 78)]
#F[((lt? 77) 78)]
;; => nil
```

See also `p-or`, `p-not`, `p-some`, ....

### Part II. Explore failures interactively on the REPL

```clojure
((p-and (between? 7 77) (p even?)) 5)
;; => #F[((p-and (between? 7 77) (p even?)) 5)]

;; Evaluating a failure interactively expands it, listing possible choices if any
(*1)
"1. (p-and (gte? 7) (lt? 77))"
"2. (p even?)"
;; => #F[((p-and (p-and (gte? 7) (lt? 77)) (p even?)) 5)]

;; Here we choos to expand only the first failing predicate in the and clause
(*1 1)
;; => #F[((gte? 7) 5)]

;; In general the interactive expansion will expand as much as explain-f.
((p-and (between? 7 77) (p even?)) 5)
;; => #F[((p-and (between? 7 77) (p even?)) 5)]
(*1)
"1. (p-and (gte? 7) (lt? 77))"
"2. (p even?)"
;; => #F[((p-and (p-and (gte? 7) (lt? 77)) (p even?)) 5)]

(*1)
"1. (gte? 7)"
"2. (p even?)"
;; => #F[((p-and (gte? 7) (p even?)) 5)]

(*1)
"1. (gte? 7)"
"2. (p even?)"
;; => #F[((p-and (gte? 7) (p even?)) 5)]
```

### Part III. Validate of data structures elements using queries.

```clojure
;; Here is how to define parameterized query to query nested map elements.
(defpq q-in [ks] (q #(get-in % ks)))

;; and a (not parametrized) query to check the length of some value
(defq q-count (q count))

;; Create a validation function to assert if the age is between 18 and 40
(defp check-age (q-in [:age] (between? 18 40)))

;; and another one to check that the password string contains at least 10 chars
(defp check-password (q-in [:password] (q-count (gte? 10))))

;; We compose them to check a profile
(defp check-profile (q-in [:profile] (p-and check-age check-password)))

;; Here is a successfull check
(check-profile {:profile {:name "Joe" :age 22 :password "12345678910"}})
;; => {:profile {:age 22, :password "12345678910" :name "Joe"}}

;; Here is one that fails
(check-profile {:profile {:name "Don" :age 22 :password "123456789"}})
;; => #F[(check-profile {:profile {:age 22, :password "12345678", :name "Don"}})]

;; because the password length is not greater or equal to 10 characters
(expand-root-f *1)
;; => #F[((q-in [:profile] (q-in [:password] (q-count (gte? 10)))) {:profile {:age 22, :password "12345678", :name "Don"}})]

;; The full explanation says it is only 8 characters long
(explain-f *2)
#F[(check-profile {:profile {:age 22, :password "12345678", :name "Don"}})]
#F[((q-in [:profile] (p-and check-age check-password)) {:profile {:age 22, :password "12345678", :name "Don"}})]
#F[((q-in [:profile] check-password) {:profile {:age 22, :password "12345678", :name "Don"}})]
#F[((q-in [:profile] (q-in [:password] (q-count (gte? 10)))) {:profile {:age 22, :password "12345678", :name "Don"}})]
#F[((q-in [:password] (q-count (gte? 10))) {:age 22, :password "12345678", :name "Don"})]
#F[((q-count (gte? 10)) "12345678")]
#F[((gte? 10) 8)]
;; => nil
```

### Part IV. Propagate failures without nesting conditional expressions.

Programs can let failures bubble up seamlessly to the top level without
conditional branches using `let-p` forms, which short-circuit the evaluation of
subsequent let bindings as soon as there is a failure. For example:

```clojure
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

```

Once it reaches the top-level, successes can be handled distinctly from failures
using `cata-p` (aka catamorphism on proposition results, which is a
generalisation of fold on lists to arbitrary data structures). For example:

```clojure
(cata-p ((p odd?) 1)
  f [:failure f]
  s [:success (inc s)])
;;=>  [:success 2]

(cata-p ((p even?) 1)
  f [:failure f]
  s [:success (inc s)])
;; => [:failure #F[((p even?) 1)]]
```

See also `bind-p` and `app-p`.

## License

Copyright © 2016 Sébastien Bocq

Distributed under the Eclipse Public License, the same as Clojure.