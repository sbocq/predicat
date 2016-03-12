(defproject predicat "0.2.0-snapshot"
  :description "A Clojure library to compose predicate/validation functions"
  :url "https://github.com/sbocq/predicat"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.6.0"]]
  :plugins [[lein-codox "0.9.4" :exclusions [org.clojure/clojure]]]
  :codox
  {:output-path "codox"
   :source-uri "http://github.com/sbocq/predicat/blob/{version}/{filepath}#L{line}"}
  :profiles {:1.7 {:dependencies [[org.clojure/clojure "1.7.0"]]}})
