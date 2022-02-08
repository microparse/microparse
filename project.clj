(defproject c-fsm-byte-gen "0.1.0-SNAPSHOT"
  :description "byte-based FSM generator"
  :url "http://example.com/FIXME"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[org.clojure/clojure "1.10.1"]
                 [ubergraph "0.8.2"]
                 [com.taoensso/timbre "5.1.0"]
                 [metasoarous/oz "1.6.0-alpha31"]
                 [macroz/tangle "0.2.2"]
                 [jcf/dorothy "0.0.7-SNAPSHOT"]
                 [walmartlabs/datascope "0.1.1"]
                 [de.ubercode.clostache/clostache "1.4.0"]
                 [org.clojure/math.numeric-tower "0.0.4"]]
  :main c-fsm-byte-gen.core
  :plugins [[lein-auto "0.1.3"]]
  :repl-options {:init-ns c-fsm-byte-gen.core}
  :profiles {:paravim {:dependencies [[paravim "RELEASE"]]
                   :main paravim.start
                   ; on mac os, an additional jvm arg must be added
                   ; so opengl can work correctly
                   :jvm-opts ~(if (= "Mac OS X" (System/getProperty "os.name"))
                                ["-XstartOnFirstThread"] [])}})
