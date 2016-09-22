(ns unmidjify.core
  (:require [clojure.java.io :as io]
            [clojure.core.strint :refer [<<]]
            [clojure.tools.namespace :as ns]
            [clojure.core.match :refer [match]]
            [clojure.string :as cs]
            [clojure.pprint]
            [clojure.zip :as zip]
            [bultitude.core :as bultitude]))


(defn third
  "Get third element of a sequence or return nil."
  [lst]
  (last (take 3 lst)))


(defn regex?
  "Check if the token is a regular expression or not"
  [token]
  (= (type token)
     java.util.regex.Pattern))


(defn  format-for-file
  "Pretty print all the forms and return as text."
  [forms]
  (clojure.string/join
   "\n"
   (map (fn [form]
          (with-out-str
            (clojure.pprint/pprint form)))
        forms)))


(def arrow-symbols #{'=> '=not=> '=deny=> '=contains=>})


(defn arrow?
  "Check if a form contains midje's arrow forms."
  [[f1 f2 f3]]
  (contains? arrow-symbols f2))


(defn get-arrow
  "If there is arrow in the form, return it otherwise return nil"
  [[f1 f2 f3 :as f]]
  (when (arrow? f)
    f2))


(defn translate-regex-arrow
  "Translate Midje's regex based arrow syntax to corresponding clojure.test syntax."
  [[f1 f2 f3]]
  (match [f1 f2 f3]
    [actual '=> re] `(~'is-re ~re ~actual)
    [actual '=not=> re] `(~'is (~'not (~'re-find ~re ~actual)))
    [actual '=deny=> re] `(~'is (~'not (~'re-find ~re ~actual)))))


(defn translate-contains-arrow
  "Translate Midje's 'contains' arrow syntaxt to a suitable
  clojure.test replacement."
  [[f1 f2 f3]]
  {:post [(do (assert % (<< "failed: ~{f1} ~{f2} ~{f3}")) true)]}
  (let [[_ contents & options] f3]
    (match [f1 f2 contents]
      [actual '=> (_ :guard string?)] `(~'is (~'=> ~f3 ~actual))
      [actual '=> (_ :guard map?)] `(~'is (~'submap? ~contents ~actual))
      [actual '=> (_ :guard regex?)] `(~'is (~'re-find ~contents ~actual))
      [actual '=not=> (_ :guard string?)] `(~'is (~'not (~'re-find ~(re-pattern contents) ~actual)))
      [actual '=not=> (_ :guard regex?)] `(~'is (~'not (~'re-find ~contents ~actual)))
      [actual arrow contents] `(~'is (~arrow ~f3 ~actual)))))


(defn form-is-anon-fn?
 [item]
 "Check if the item is an anonymous function"
 (and (list? item)
      (= (first item) 'fn)))


(defn form-is-fn?
  "Resolves a form, and returns truthy if it evaluates to a fn"
  [f]
  (fn? f)
  (if (symbol? f)
    (let [resolved (resolve f)]
      (and resolved (or (fn? resolved)
                        (and (var? resolved)
                             (fn? @resolved)))))
    (form-is-anon-fn? f)))


(defn translate-normal-arrow
  "Translate regular midje arrow syntax to clojure.test form."
  [[f1 f2 f3]]
  (match [f1 f2 f3]
    [actual '=> true] `(~'is ~actual)
    [actual '=> 'truthy] `(~'is ~actual)
    [actual '=> 'anything] `(~'is (~'anything ~actual))
    [actual '=> false] `(~'is (~'not ~actual))
    [actual '=> 'falsey] `(~'is (~'not ~actual))
    [actual '=> (f :guard form-is-fn?)] `(~'is (~f ~actual))
    [actual '=> 0] `(~'is (~'zero? ~actual))
    [actual '=> nil] `(~'is (~'nil? ~actual))
    [actual '=> expected] `(~'is (~'= ~expected ~actual))
    [actual '=contains=> (expected :guard map?)] `(~'is (~'submap? ~expected ~actual))
    [actual '=not=> expected] `(~'is (~'not= ~expected ~actual))))


(defn translate-throws
  "Translate Midje's throws to something else."
  [[f1 f2 f3]]
  (let [exception-form (rest f3)]
    (println exception-form)
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
      ret)))


(defn munge-name
  "Turn a string into a valid clojure identifier name"
  [name]
  (-> name
      (cs/replace " " "-")
      (cs/replace "\n" "")
      (cs/replace "." "")
      (cs/replace "`" "")
      (cs/replace "'" "")
      (cs/replace "(" "")
      (cs/replace ")" "")
      (cs/replace "/" "")
      (cs/replace "," "-")
      (cs/replace "[" "")
      (cs/replace "]" "")
      (cs/replace #"^(\d+)" "_$1")
      (cs/replace #"^:" "")
      (cs/replace #"-+" "-")
      (.toLowerCase)))


(defn replace-fact
  "If the form is (fact ...) replace w/ (deftest ...)"
  [form]
  (if (= 'fact (first form))
    (let [[fact name & body] form]
      `(~'deftest ~(symbol (munge-name name)) ~@body))
    form))


(defn replace-midje-sweet
  "Replace midje imports with clojure.test"
  [form]
  (if (= 'midje.sweet form)
    'clojure.test
    form))


(defn replace-future-fact
  "Replace future facts with commented deftest"
  [form]
  (if (= 'future-fact (first form))
    `(~'comment ~(replace-fact `(~'fact ~@(rest form))))
    form))


(defn test-relative-path
  "Relative path from the test directory"
  [absolute-path]
  (first
   (re-find #"/test(/.*)?$" absolute-path )))


(defn file-path-excluded?
  "Check of file-path is in the list of excluded-paths."
  [excluded-paths file-path]
  (let [relative-file-path (test-relative-path file-path)]
    (not
     (empty?
      (filter
       (fn [excluded-path]
         (let [relative-excluded-path (test-relative-path excluded-path)]
           (re-find (re-pattern (str "^" relative-excluded-path))
                    relative-file-path)))
       excluded-paths)))))


(defn wrap-deftest-body-in-let
  "Surround a given fact form with let bindings."
  [let-bindings deftest-form]
  (let [deftest-content (drop 2 deftest-form)]
    (list
     'deftest
     (nth deftest-form 1)
     (concat
      (list 'let let-bindings)
      deftest-content))))


(defn push-outer-let-in-each-deftest
  "Bring an outer let form and push it inside each fact form within."
  [form]
  (let [let-bindings (nth form 1)
        let-body (filter
                  #(= (first %) 'deftest)
                  (drop 2 form))
        let-wrapped-forms (map
                           #(wrap-deftest-body-in-let let-bindings %)
                           let-body)]
    let-wrapped-forms))


(defn deftest-in-let?
  "Checks if the form is a let form that contains a face form or not."
  [form]
  (and (= (first form) 'let)
       (some #(and (seq? %)
                   (= (first %) 'deftest))
             (drop 2 form))))


(defn vectorify-if
  "if is-vector is true, then convert seq to vector."
  [is-vector seq]
  (if is-vector
    (vec seq)
    seq))


(defn walk-form
  "Walk through the form recursively
  and replace inline midje code with clojure.test."
  [form opts]
  (let [form (-> form
                 (replace-midje-sweet))
        is-vector (vector? form)]
    (cond
      (or (seq? form)
          (vector? form)) (-> form
                              (replace-fact)
                              (replace-future-fact)
                              (replace-arrow)
                              (->> (map #(walk-form % opts))
                                   (vectorify-if is-vector)))
      :else form)))


(defn walk
  "Walk through though the form."
  [form opts]
  (walk-form form opts))


(defn read-seq
  "Read clojure source code as a list of form"
  [s]
  (read-string (str "(" s  "\n)")))


(defn ns-state-change-form?
  "Check if the form is namespace-state-change form."
  [form]
  (= 'namespace-state-changes
     (first form)))


(defn get-ns-forms
  "Filter out all namepace state changes forms"
  [forms]
  (filter
   ns-state-change-form?
   forms))


(defn without-ns-forms
  "Remove all namespace state changes forms"
  [forms]
  (remove
   ns-state-change-form?
   forms))


(defn extract-ns-vectors
  "Extract vectors that are part of namespace-state-changes form"
  [ns-forms]
  (map
   (fn [ns-form]
    (last ns-form))
   ns-forms))


(defn get-fixture-map
  "Get a fixture map."
  [ns-forms]
  (reduce
   (fn [fixture-map curr-form]
     (assoc fixture-map (nth curr-form 0) (nth curr-form 2)))
   {}
   ns-forms))


(defn define-once-fixture
  [fixture-map]
  "Define fixture that runs once."
  (let [fixture-code '(defn once-fixture [tests]
                        :before
                        (tests)
                        :after)]
    (replace {:before (fixture-map 'before)
              :after (fixture-map 'after)}
             fixture-code)))


(defn define-each-fixture
  "Define fixture that runs for each test."
  [fixture-map]
  (let [fixture-code '(defn each-fixture [tests])]
    (concat
     fixture-code
     [(clojure.walk/postwalk-replace
       {'?form '(tests)}
       (fixture-map 'around))])))


(defn add-fixture-code
  "Add fixture code to forms."
  [forms & fixture-code]
  (concat (list (first forms))
          fixture-code
          (rest forms)))


(defn replace-ns-state-changes
  "Replace namespace state changes with corresponding clojure.test fixtures"
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
  "Check if the form a facts form"
  [element]
  (and
   (seq? element)
   (= (first element) 'facts)))


(defn contains-facts-form?
  "Check if the form-list contains a facts form."
  [form-list]
  (first
   (filter
    facts?
    form-list)))


(defn facts-content
  "Get content within facts form"
  [facts-form]
  (drop 2 facts-form))


(defn replace-facts-with-content
  "Replace facts with it's content."
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
  "Open up all facts forms and bring the inner content out."
  [form-list]
  (clojure.walk/postwalk
   replace-facts-with-content 
   form-list))


(defn unbound-let-bound-test
  "Remove the let wrapping up the fact form and bring it inside of it."
  [form-list opts]
  (let [deftest-wrapped-let (->> form-list
                                 (filter deftest-in-let?)
                                 (mapcat #(push-outer-let-in-each-deftest %)))]
    (->>
     form-list
     (remove deftest-in-let?)
     (#(concat %  deftest-wrapped-let)))))


(defn extract-action
  "Extracts the specified code."
  [action-symbol actions]
  (last
   (first
    (filter
     #(and (= (first %) action-symbol)
           (= (nth % 1) :checks))
     actions))))


(defn with-state-changes-inside-out
  "Read 'before' and 'after' actions from midje's with-state-change form and
   wrap all fact forms with the code around them."
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


(defn open-with-state-changes
  "Open up with-state-changes changes form"
  [form-list]
  (map
   with-state-changes-inside-out
   form-list))


(defn transform-comment
  "Converts a single line comment into a string with tag like markup to
   preserve comments in a single line after reading and pretty printing."
  [source-code]
  (clojure.string/replace
   source-code #"\n\s*(;.+)"
   (fn [[fst & ignore]]
     (str "\"<COMMENT>"
          (cs/replace fst #"\"" {"\"" "__qt__"})
          "</COMMENT>\""))))


(defn recover-comment
  "Recover comment back from a format
  of \"<COMMENT>;; This is comment</COMMENT>\" back to it's original form. "
  [source-code]
  (clojure.string/replace
   source-code #"\"<COMMENT>\s*(.*)\s*</COMMENT>\""
   (fn [[fst sec]]
     (->> sec
          (#(cs/replace % #"__qt__" {"__qt__" "\""}))
          (re-find #";(.+)")
          (first)))))


(defn prefix-name-space
  "Insert 'cljtest' in name space and second last position."
  [form-list]
  (map
   (fn [form]
     (if (= (first form) 'ns)
       (let [[_  ns-name] form
             new-ns (-> ns-name
                        (name)
                        (cs/split #"\.")
                        (#(concat (butlast %)
                                  (list "cljtest")
                                  (list (last %))))
                        (#(cs/join "." %))
                        (symbol))]
         (replace {ns-name new-ns} form))
       form)) form-list))


(defn transform
  "Takes a file through series of transformations."
  [file opts]
  (-> file
      (slurp)
      (#(if (:keep-comments opts) (transform-comment %) %))
      (read-seq)
      (open-with-state-changes)
      (walk opts)
      (replace-ns-state-changes)
      (open-all-facts)
      (unbound-let-bound-test opts)
      (prefix-name-space)
      (format-for-file)
      (#(if (:keep-comments opts) (recover-comment %) %))))


(defn midje?
  "Check if the file contains midje related code or not."
  [file]
  (or (re-find #"midje.sweet" (slurp file))
      (re-find #"\(fact" (slurp file))))


(defn original-file?
  "Checks if the file is original source code or not."
  [file]
  (not
   (re-find #"cljtest" (.getAbsolutePath file))))


(defn- new-source-name
  "Returns a full-qualified name for the newly generated source file"
  [f]
  (str
   (.getParent f)
   "/cljtest/"
   (.getName f)))


(defn- new-source-file
  "Create a backup file for the source file.
   Spits the content out to a new file 
  and creates every directory and file that is not part of the path"
  [f content]
  (clojure.java.io/make-parents (new-source-name f))
  (spit (new-source-name f) content))


(defn- unmidjify-file
  "Convert a midje source file to clojure.test source file."
  [f opts]
  (-> f
      (transform (assoc opts :file-path (.getAbsolutePath f)))
      (->> (new-source-file f))))


(defn- unmidjify-dir
  "Recursively walk down a directory
  and unmidjify each file that contains midje forms."
  [d opts]
  (let [files (->> (java.io.File. d)
                   (ns/find-clojure-sources-in-dir)
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

