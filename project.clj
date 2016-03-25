(defproject predicat "0.2.1"
  :description "A Clojure library to compose predicate/validation functions"
  :url "https://github.com/sbocq/predicat"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.6.0"]]
  :plugins [[lein-codox "0.9.4" :exclusions [org.clojure/clojure]]]
  :codox
  {:output-path "codox"
   :source-uri "http://github.com/sbocq/predicat/blob/v{version}/{filepath}#L{line}"}
  :profiles {:1.7 {:dependencies [[org.clojure/clojure "1.7.0"]]}
             :cloverage {:plugins [[lein-cloverage "1.0.6"]
                                   [lein-shell "0.5.0"]]
                         :aliases {"coveralls"
                                   ["do"
                                    ["cloverage" "--coveralls"]
                                    ["shell" "curl" "-F"
                                     "json_file=@target/coverage/coveralls.json"
                                     "https://coveralls.io/api/v1/jobs"]]}}})
