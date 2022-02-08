(ns c-fsm-byte-gen.core
  (:require [clojure.string :as str])
  (:require [clojure.pprint :as pp])
  (:require [tangle.core :as t])
  (:require [com.walmartlabs.datascope :as ds])
  (:require [taoensso.timbre :as timbre
             :refer [log  trace  debug  info  warn  error  fatal  report
                     logf tracef debugf infof warnf errorf fatalf reportf
                     spy get-env]]))

(def global-reg-cons-dict (atom {}))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn gen-tag
  "Generates a tag"
  [unit size dict desc
   & {:keys [ref-len-counter]}]
  {:type :tag
   :unit unit
   :dict dict
   :size size
   :ref-len-counter ref-len-counter
   :id (gensym "tag")
   :desc desc})

(defn gen-len
  "Generates a length"
  [unit endianness size desc
   & {:keys [min-size]}]
  {:type :length
   :unit unit
   :endianness endianness
   :id (gensym "len")
   :size size
   :min-size min-size
   :desc desc})

(defn gen-repeat
  "Generates a repeat construct"
  [unit repeat-times desc
   & {:keys [range-min range-max ref-len-counter]
      :or {range-min ##-Inf range-max ##Inf ref-len-counter nil}}]
  {:type :repeat
   :unit unit
   :repeat-times repeat-times
   :range-min range-min
   :range-max range-max
   :ref-len-counter ref-len-counter
   :id (gensym "repeat")
   :desc desc})

(defn gen-case
  "Generates a case construct"
  [grammar-cons case-dict
   & {:keys [ref-len-counter]
      :or {ref-len-counter nil}}]
  {:type :case
   :grammar-cons grammar-cons
   :ref-len-counter ref-len-counter
   :id (gensym "case")
   :case-dict case-dict})

(defn gen-start-counter "" [reg]
  {:type :counter :reg reg :id (gensym "counter")})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Grammar Definitions Begins Here
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def PDU
  (gen-tag
    :bit
    4
    {:ADV_IND         "0000"
     :ADV_DIRECT_IND  "0001"
     :ADV_NONCONN_IND "0010"
     :SCAN_REQ        "0011"
     :SCAN_RSP        "0100"
     :CONNECT_IND     "0101"
     :ADV_SCAN_IND    "0110"
     :ADV_EXT_IND     "0111"
     :AUX_CONNECT_RSP "1000"}
    "PDU"))

(def RFU   (gen-tag :bit 1 {:RFU_ON    "1" :RFU_OFF    "0"} "RFU"))
(def ChSel (gen-tag :bit 1 {:CHSEL_ON  "1" :CHSEL_OFF  "0"} "ChSel"))
(def TxAdd (gen-tag :bit 1 {:TX_ADD_ON "1" :TX_ADD_OFF "0"} "TxAdd"))
(def RxAdd (gen-tag :bit 1 {:RX_ADD_ON "1" :RX_ADD_OFF "0"} "RxAdd"))

(def repeat-bytes
  (gen-repeat :byte ##Inf "repeat * bytes"))

(def repeat-0-31-bytes
  (gen-repeat :byte ##Inf "repeat 0 31 bytes"
              :range-min 0
              :range-max 31))

(def ADV_IND [(gen-repeat :byte 6 "AdvA")
              repeat-0-31-bytes])

(def ADV_DIRECT_IND [(gen-repeat :byte 6 "AdvA")
                     (gen-repeat :byte 6 "Target A")])

(def ADV_NONCONN_IND [(gen-repeat :byte 6 "AdvA")
                      repeat-0-31-bytes])

(def SCAN_REQ [(gen-repeat :byte 6 "ScanA")
               (gen-repeat :byte 6 "AdvA")])

(def SCAN_RSP [(gen-repeat :byte 6 "AdvA")
               repeat-0-31-bytes])

(def LLDATA [(gen-repeat :byte 4 "AA")
             (gen-repeat :byte 3 "CRCInit")
             (gen-repeat :byte 1 "WinSize")
             (gen-repeat :byte 2 "WinOffset")
             (gen-repeat :byte 2 "Interval")
             (gen-repeat :byte 2 "Latency")
             (gen-repeat :byte 2 "Timeout")
             (gen-repeat :byte 5 "ChM")
             (gen-repeat :byte 5 "Hop")
             (gen-repeat :byte 3 "SCA")])

(def CONNECT_IND (concat [(gen-repeat :byte 6 "InitA")
                          (gen-repeat :byte 6 "AdvA")]
                       LLDATA))

(def ADV_SCAN_IND [(gen-repeat :byte 6 "AdvA")
                   repeat-0-31-bytes])

(def Extended-Header-Length
  (gen-len :bit :LSB 6 "Extended Header Length"))

(def AdvData
  (gen-repeat :byte ##Inf "repeat 0 - 254 bytes" :range-min 0 :range-max 254))

(def ExtendedHeader
  (gen-repeat :byte ##Inf "repeat 0 63 bytes" :range-min 0 :range-max 63))

(def Common-Extended-Advertising-Payload
  [Extended-Header-Length
   (gen-repeat :byte 2 "AdvMode")
   (gen-case Extended-Header-Length
             {:if (list 0 nil)
              :else ExtendedHeader})
  AdvData])

(def ADV_EXT_IND Common-Extended-Advertising-Payload)

(def AUX_CONNECT_RSP Common-Extended-Advertising-Payload)

(def payload-grammar
  (gen-case PDU
            {:ADV_IDV ADV_IND
             :ADV_DIRECT_IND  ADV_DIRECT_IND
             :ADV_NONCONN_IND ADV_NONCONN_IND
             :SCAN_REQ        SCAN_REQ
             :SCAN_RSP        SCAN_RSP
             :CONNECT_IND     CONNECT_IND
             :ADV_SCAN_IND    ADV_SCAN_IND
             :ADV_EXT_IND     ADV_EXT_IND
             :AUX_CONNECT_RSP AUX_CONNECT_RSP}))

(def len-field
  (gen-len :byte :LSB 2 "header"))

(def packet-grammar
  [PDU RFU ChSel TxAdd RxAdd len-field payload-grammar])

(def output-file-handle
  (clojure.java.io/writer "foo.txt"))

(defn gen-register "return a register name" []
  (gensym "reg"))

(defn convert-tag-to-c-code "doc-string" [tag-cons]
  "converts a tag construct to c code"
  (let [unit  (case (:unit tag-cons) :bit "BIT" :byte "BYTE")
        size (:size tag-cons)
        reg (gen-register)]
    (swap! global-reg-cons-dict conj {(:id tag-cons) reg})
    (str "// " (:desc tag-cons) " \n"
      "int " reg " = " "tag_cons(" unit ", " size ");")))

(defn convert-length-to-c-code "doc-string" [len-cons]
  (let [unit  (case (:unit len-cons) :bit "BIT" :byte "BYTE")
        endianness (case (:endianness len-cons) :LSB "LSB" :MSB "MSB")
        size (:size len-cons)
        reg (gen-register)]
    (swap! global-reg-cons-dict conj {(:id len-cons) reg})
    (str "int " reg " = "
         "len_cons(" unit ", "  endianness ", " size ");\n")))

(declare convert-cons-to-c-code)
(defn convert-range-inf-to-c "doc-string" [a]
  (case a ##Inf "INF" ##-Inf "NINF" a))

(defn convert-repeat-to-c-code "doc-string" [repeat-cons]
  (let [reg (gen-register)
        unit (clojure.string/upper-case (name (:unit repeat-cons)))]
    (str "// " (:desc repeat-cons) "\n"
      "parsed_result  " reg " = repeat_cons(" unit ", "
      (convert-range-inf-to-c (:repeat-times repeat-cons)) ", "
      (convert-range-inf-to-c (:range-min repeat-cons)) ", "
      (convert-range-inf-to-c (:range-max repeat-cons)) ");\n")))

(defn convert-tag-case-to-c-code "doc-string" [case-cons]
  (let [predicate-g (:grammar-cons case-cons)
        predicate-g-dict (:dict predicate-g)
        reg-name ((:id predicate-g) @global-reg-cons-dict)
        case-dict (:case-dict case-cons)
        generate-inner-case-code (fn [v]
                                   (apply str
                                     (interpose
                                       "\t"
                                       (map convert-cons-to-c-code v))))
        generate-case-code (fn [[k v]]
                             (let [case-val (k predicate-g-dict)
                                   code-statements (generate-inner-case-code v)]
                               (str "case 0b" case-val ": {\n\t"
                                    "// " (str k) "\n\t"
                                    code-statements
                                    " break;\n}\n")))
        generate-case-statements (map generate-case-code case-dict)
        case-statements (apply str generate-case-statements)]
    (str "switch (" reg-name ") { \n"
         case-statements
         "default:\n\t printf(\"ERROR: None matched case expression!\");\n }")))

(defn convert-len-case-to-c-code "" [case-cons]
  (let [predicate-g (:grammar-cons case-cons)
        reg-name ((:id predicate-g) @global-reg-cons-dict)
        case-dict (:case-dict case-cons)
        if-clause (:if case-dict)
        else-clause (:else case-dict)]
    (str "if (" reg-name " == " (first if-clause) ") {"
        (if (nil? (second if-clause)) ""
          (convert-cons-to-c-code (second if-clause)))
        "} else {\n"
        (apply str (convert-cons-to-c-code
                     (update-in else-clause
                                [:repeat-times]
                                (fn [x] reg-name))))
        "}\n")))

(defn convert-case-to-c-code "doc-string" [case-cons]
  (case (:type (:grammar-cons case-cons))
    :tag (convert-tag-case-to-c-code case-cons)
    :length (convert-len-case-to-c-code case-cons)))

(defn convert-cons-to-c-code "doc-string" [grammar-construct]
  (case (:type grammar-construct)
    :tag  (convert-tag-to-c-code grammar-construct)
    :length (convert-length-to-c-code grammar-construct)
    :repeat (convert-repeat-to-c-code grammar-construct)
    :case (convert-case-to-c-code grammar-construct)))

(defn generate-c-code
  "generates c code given a grammar"
  [grammar]
  (map convert-cons-to-c-code grammar))

;; A lang with following commands:
;; read tag, read len, start_len, repeat (for loop), if (r0 == "") { g0 } else {g1}

(def generated-code
  (apply str (interpose "\n" (generate-c-code packet-grammar))))

(defn -main
  "main func"
  []
  (println "Started...")
  (spit output-file-handle generated-code)
  (println "printing complete..."))
