(ns unmidjify.core
  (:gen-class)
  (:require [clojure.java.io :as io]
            [clojure.core.strint :refer [<<]]
            [clojure.tools.namespace :as ns]
            [clojure.core.match :refer [match]]
            [clojure.string :as str]
            [clojure.pprint]
            [clojure.zip :as zip]
            [bultitude.core :as bultitude]))


(defn third [lst]
  (last (take 3 lst)))

(defn regex? [token]
  (= (type token) java.util.regex.Pattern))


(defn re [token]
  (re-pattern token))

(defn  format-for-file  [forms]
  (reduce (fn [content form]
            (str content "\n\n"
                 (with-out-str
                   (clojure.pprint/write
                    form
                    :dispatch clojure.pprint/code-dispatch))))
          ""
          forms))


(defn list! [s]
  {:post [(list? %)]}
  (apply list s))

(def arrow-symbols #{'=> '=not=> '=deny=> '=contains=>})

(defn arrow? [[f1 f2 f3]]
  (contains? arrow-symbols f2))

(defn get-arrow [[f1 f2 f3 :as f]]
  (when (arrow? f)
    f2))

(defn translate-regex-arrow
  [[f1 f2 f3]]
  (match [f1 f2 f3]
    [actual '=> re] `(~'is-re ~re ~actual)
    [actual '=not=> re] `(~'is-not (~'re-find ~re ~actual))
    [actual '=deny=> re] `(~'is-not (~'re-find ~re ~actual))))

(defn translate-contains-arrow [[f1 f2 f3]]
  {:post [(do (assert % (<< "failed: ~{f1} ~{f2} ~{f3}")) true)]}
  (let [[_ contents & options] f3]
    (match [f1 f2 contents]
      [actual '=> (_ :guard string?)] `(~'is (~'=> ~f3 ~actual))
      [actual '=> (_ :guard map?)] `(~'is (~'submap? ~contents ~actual))
      [actual '=> (_ :guard regex?)] `(~'is (~'re-find ~contents ~actual))
      [actual '=not=> (_ :guard string?)] `(~'is-not (~'re-find ~(re contents) ~actual))
      [actual '=not=> (_ :guard regex?)] `(~'is-not (~'re-find ~contents ~actual))
      [actual arrow contents] `(~'is (~arrow ~f3 ~actual)))))

(defn form-is-fn?
  "Resolves a form, and returns truthy if it evaluates to a fn"
  [f]
  (when (symbol? f)
    (let [resolved (resolve f)]
      (and resolved (or (fn? resolved)
                        (and (var? resolved)
                             (fn? @resolved)))))))

(defn translate-normal-arrow [[f1 f2 f3]]
  (match [f1 f2 f3]
    [actual '=> true] `(~'is ~actual)
    [actual '=> 'truthy] `(~'is ~actual)
    [actual '=> 'anything] `(~'is (~'anything ~actual))
    [actual '=> false] `(~'is-not ~actual)
    [actual '=> 'falsey] `(~'is-not ~actual)
    [actual '=> (f :guard form-is-fn?)] `(~'is (~f ~actual))
    [actual '=> 0] `(~'is (~'zero? ~actual))
    [actual '=> nil] `(~'is (~'nil? ~actual))
    [actual '=> expected] `(~'is (~'= ~expected ~actual))
    [actual '=contains=> (expected :guard map?)] `(~'is (~'submap? ~expected ~actual))
    [actual '=not=> expected] `(~'is (~'not= ~expected ~actual))))

(defn translate-throws [[f1 f2 f3]]
  (let [exception-form (rest f3)]
    (condp = (count exception-form)
      0 `(~'is (~'thrown? Exception ~f1))
      1 `(~'is (~'thrown? ~@exception-form ~f1))
      2 `(~'is (~'thrown-with-msg? ~@exception-form ~f1))
      :else (assert false))))

(defn translate-arrow [[f1 f2 f3 :as f]]
  {:post [(do (assert % (<< "failed: ~{f1} ~{f2} ~{f3}")) true)]}
  (let [contains-form? (or (and (seq? f3) (= 'contains (first f3)))
                           (= '=contains=> f2))
        thrown? (and (list? f3)
                     (= 'throws (first f3)))]
    (cond
     (regex? f3) (translate-regex-arrow f)
     contains-form? (translate-contains-arrow f)
     thrown? (translate-throws f)
     :else (translate-normal-arrow f))))

(defn replace-arrow
  "If the head of the form is (foo) => (bar), return clojure.test
  equivalent. Returns either the updated form, or the original, if no
  match"
  [lst]
  (loop [ret []
         lst lst]
    (if (seq lst)
      (if (arrow? lst)
        (let [actual (first lst)
              expected (third lst)]
          (recur (conj ret (translate-arrow lst)) (drop 3 lst)))
        (recur (conj ret (first lst)) (rest lst)))
      (list! ret))))

(defn munge-name [name]
  (-> name
      (str/replace " " "-")
      (str/replace "." "")
      (str/replace "`" "")
      (str/replace "'" "")
      (str/replace "(" "")
      (str/replace ")" "")
      (str/replace "/" "")
      (str/replace "," "-")
      (str/replace "[" "")
      (str/replace "]" "")
      (str/replace #"^(\d+)" "_$1")
      (str/replace #"^:" "")
      (str/replace #"-+" "-")))


(defn replace-fact
  "If the form is (fact ...) replace w/ (deftest ...)"
  [form]
  (if (= 'fact (first form))
    (let [[fact name & body] form]
      (list! `(~'deftest ~(symbol (munge-name name)) ~@body)))
    form))

(defn replace-midje-sweet [form]
  (if (= 'midje.sweet form)
    'clojure.test
    form))

(defn replace-future-fact [form]
  (if (= 'future-fact (first form))
    `(~'comment ~(replace-fact `(~'fact ~@(rest form))))
    form))

(defn cast-coll
  "Convert one seq class into another. Use it to handle (into (empty list) '(1 2 3)) being dumb"
  [cls form]
  (condp = cls
    clojure.lang.PersistentList (list* form)
    clojure.lang.PersistentVector (vec form)))

(defn test-relative-path
  [absolute-path]
  (first
   (re-find #"/test(/.*)?$" absolute-path )))

(defn file-path-excluded?
  [excluded-paths file-path]
  (let [relative-file-path (test-relative-path file-path)]
    (not
     (empty?
      (filter
       (fn [excluded-path]
         (let [relative-excluded-path (test-relative-path excluded-path)]
           (re-find (re-pattern (str "^" relative-excluded-path)) relative-file-path)))
       excluded-paths)))))

(defn wrap-fact-body-in-let [let-bindings fact-form]
  (let [fact-content (drop 2 fact-form)]
    (list
     'fact
     (nth fact-form 1)
     (concat
      (list 'let let-bindings)
      fact-content))))

(defn push-outer-let-in-each-fact 
  [form]
  (let [let-bindings (nth form 1)
        let-body (filter
                  #(= (first %) 'fact)
                  (drop 2 form))
        let-wrapped-forms (map
                           #(wrap-fact-body-in-let let-bindings %)
                           let-body)]

    let-wrapped-forms))

(defn fact-in-let?
  [form]
  (and (= (first form) 'let)
       (some #(and (list? %)
                   (= (first %) 'fact))
             (drop 2 form))))


(defn fact-forms-wrapped-let
  [form opts]
  (if-not (file-path-excluded? (get opts :exclude-paths #{}) (opts :file-path))
    (push-outer-let-in-each-fact form)
    '(form)))


(defn munge-form [form opts]
  ;;(update-nested-facts form opts)
  (let [form (-> form
                 (replace-midje-sweet))
        form-class (class form)]
    (cond
     (or (list? form)
         (vector? form)) (-> form
                             (replace-fact)
                             (replace-future-fact)
                             (replace-arrow)
                             (->> (map #(munge-form % opts))
                                  (cast-coll form-class)))
     :else form)))


(defn walk [form opts]
  (munge-form form opts))

(defn read-seq [s]
  (read-string (str "(" s  "\n)")))

(defn ns-state-change-form?
  [form]
  (= 'namespace-state-changes
     (first form)))

(defn get-ns-forms [forms]
  (filter
   ns-state-change-form?
   forms))

(defn without-ns-forms [forms]
  (remove
   ns-state-change-form?
   forms))

(defn extract-ns-vectors
  [ns-forms]
  (map
   (fn [ns-form]
    (last ns-form))
   ns-forms))

(defn get-fixture-map
  [ns-forms]
  (reduce
   (fn [fixture-map curr-form]
     (assoc fixture-map (nth curr-form 0) (nth curr-form 2)))
   {}
   ns-forms))

(defn define-once-fixture
  [fixture-map]
  (let [fixture-code '(defn once-fixture [tests]
                        :before
                        (tests)
                        :after)]
    (replace {:before (fixture-map 'before) 
              :after (fixture-map 'after)} fixture-code)))

(defn define-each-fixture
  [fixture-map]
  (let [fixture-code '(defn each-fixture [tests])]
    (concat
     fixture-code
     [(clojure.walk/postwalk-replace {'?form '(tests)} (fixture-map 'around))])))

(defn add-fixture-code
  [forms & fixture-code]
  (concat (list (first forms))
          fixture-code
          (rest forms)))

(defn replace-ns-state-changes
  [forms]
  (let [fixture-map (->> forms
                         (get-ns-forms)
                         (extract-ns-vectors)
                         (apply concat)
                         (get-fixture-map))
        has-ns-forms (first (filter #(= (first %) 'namespace-state-changes) forms))]
    (-> forms
         (without-ns-forms)
         (#(if has-ns-forms
             (add-fixture-code
              %
              (define-once-fixture fixture-map)
              (define-each-fixture fixture-map)
              '(use-fixtures :once  once-fixture)
              '(use-fixtures :each  each-fixture))
             %)))))

(defn facts?
  [element]
  (and
   (seq? element)
   (= (first element) 'facts)))

(defn contains-facts-form?
  [form-list]
  (first
   (filter
    facts?
    form-list)))

(defn facts-content
  [facts-form]
  (drop 2 facts-form))

(defn replace-facts-with-content
  [item]
  (if (seq? item)
    (mapcat
     (fn [e]
       (if (facts? e)
         (facts-content (doall e))
         (list e)))
     item)
   item))

(defn open-all-facts
  [form-list]
  (clojure.walk/postwalk
   replace-facts-with-content 
   form-list))

(defn unbound-let-bound-fact
  [form-list opts]
  (let [fact-wrapped-let (->> form-list
                             (filter fact-in-let?)
                             (map #(fact-forms-wrapped-let % opts))
                             (apply concat))]
    (->>
     form-list
     (remove fact-in-let?)
     (#(concat %  fact-wrapped-let)))))

(defn extract-action [action-symbol actions]
  (last
   (first
    (filter
     #(and (= (first %) action-symbol)
           (= (nth % 1) :checks))
     actions))))

(defn with-state-changes-inside-out
  [[form-name actions facts-form :as form]]
  (if (= form-name 'with-state-changes)
    (let [before-action (extract-action 'before actions)
          after-action (extract-action 'after actions)]
     (clojure.walk/prewalk
      (fn [item]
        (if (and (list? item) (= 'fact (first item)))
          (concat (take 2 item) [before-action] (drop 2 item) [after-action])
          item))
      facts-form))
    form))

(defn transform [file opts]
  (-> file
      slurp
      (read-seq)
      (unbound-let-bound-fact opts)
      (list!)
      (walk opts)
      (replace-ns-state-changes)
      (#(map with-state-changes-inside-out %))
      (open-all-facts)
      (format-for-file)))

(defn midje? [file]
  (or (re-find #"midje.sweet" (slurp file))
      (re-find #"\(fact" (slurp file))))

(defn original-file? [file]
  (re-find #"cljtest" (.getAbsolutePath file)))

(defn- backup-copy-name [f]
  (str 
   (.getParent f)
   "/cljtest/"
   (.getName f)))

(defn- new-source-file [f content]
  (clojure.java.io/make-parents (backup-copy-name f))
  (spit (backup-copy-name f) content))

(defn- unmidjify-file [f opts]
  (-> f
      (transform (assoc opts :file-path (.getAbsolutePath f)))
      (->> (new-source-file f))))

(defn- unmidjify-dir [d opts]
  (let [files (->> (java.io.File. d)
                   (ns/find-clojure-sources-in-dir )
                   (filter midje?)
                   (filter original-file?))]
    (doseq [f files]
      (try
        (unmidjify-file f opts)
        (catch Throwable t
          (print t)
          (.printStackTrace t)
          (println "FAILED:" f))))))

(defn unmidjify
  "Checks if the path is a single file.
  If it is a directory then recursively looks for files containing a midje
  fact or an import for midje, sweet and replace the file(s) with their
  corresponding clojure.test semantics."
  [path & {:as opts}]
  (if-not (.exists (io/file path))
    (println (str path " : No such file or directory"))
    (if (.isDirectory (io/file path))
      (unmidjify-dir path (or opts {}))
      (unmidjify-file (java.io.File. path) (or opts {})))))







