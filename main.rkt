#lang typed/racket
(define debug (ann (make-parameter #f) (Parameterof Boolean)))

(define (debug-eprintf [fmt : String] . args)
  (when (debug)
    (apply eprintf fmt args)))

(define-syntax-rule (debug-ctx expr)
  (parameterize ([debug #t])
    expr))

(define-type RuleProc (-> (Rel Term) (Listof (Rel Term)) (Listof (Rel Term))))
(define-type RelKind Boolean)

(struct (A) rel ([a : A] [b : A][kind : RelKind]) #:transparent #:type-name Rel)

(: make-rel (All (A) (-> A A [#:rel-kind RelKind] (Rel A))))
(define (make-rel a b #:rel-kind [rel-kind #f])
  (rel a b rel-kind))

(define-type Model (HashTable Term (Listof (U Integer (Pairof Integer Integer)))))

(struct term () #:type-name Term #:transparent)

(struct root term ([p : Term]
                   [q : Term])
  #:type-name Root
  #:transparent
  #:property prop:custom-write (λ ([me : Root] [port : Output-Port] [m : (U Boolean 0 1)])
                                 (fprintf port "[[~a ~a]]" (root-p me) (root-q me))))

(struct noun term ([name : String])
  #:type-name Noun
  #:transparent
  #:property prop:custom-write (λ ([me : Noun] [port : Output-Port] [m : (U Boolean 0 1)])
                                 (fprintf port "[[~a]]" (noun-name me))))

(struct self term ()
  #:type-name Self
  #:transparent
  #:property prop:custom-write (λ ([me : Self] [port : Output-Port] [m : (U Boolean 0 1)])
                                 (fprintf port "self")))
#;
(struct be-term term ([pnoun : Term])
  #:type-name BeTerm
  #:property prop:custom-write (λ ([me : term] [port : Output-Port] _)
                                 (fprintf port "<are ~a>" (be-term-pnoun me))))

(define-type VerbName (U 'see))

(struct verb term ([name : VerbName])
  #:type-name Verb
  #:transparent
  #:property prop:custom-write
  (λ ([me : Verb] [port : Output-Port] _)
    (fprintf port "[[~a]]" (verb-name me))))

;; (define-type ObjectTerm (U VerbPhrase Noun))

(struct verb-phrase term ([action : Verb]
                          [object : Term])
  #:type-name VerbPhrase
  #:transparent
  #:property prop:custom-write (λ ([me : VerbPhrase] [port : Output-Port] _)
                                 (fprintf port "~a ~a" (verb-phrase-action me) (verb-phrase-object me))))


(: parse (-> Any Term))
(define (parse s)
  (match s
    [`(,v all ,p) #:when (eq? v 'see) (verb-phrase (verb 'see) (parse p))]
    [`(,v self) #:when (eq? v 'see) (verb-phrase (verb 'see) (self))]
    [`,n #:when (symbol? n)
         (noun (symbol->string n))]))

(define (parse-root [s : Any]) : Root
  (match-define `(all ,p ,q) s)
  (root (parse p) (parse q)))

(: ->terms (-> Term (Listof Term)))
(define (->terms t)
  (cond
    [(root? t) (append (list t) (->terms (root-p t)) (->terms (root-q t)))]
    [(noun? t) (list t)]
    [(verb-phrase? t) (append (list t) (->terms (verb-phrase-object t)))]
    [(self? t) (list t)]
    [(term? t) (error '->terms "you are drunk")]))


(: ->rel (-> Term (rel Term)))
(define (->rel t)
  (cond
    [(noun? t) (make-rel t t)]
    [(root? t) (make-rel (root-p t) (root-q t))]
    [(verb-phrase? t) (make-rel t t)]
    [(self? t) (make-rel t t)]
    [else (error 'rc "you are drunk")]))

(: reflexive-clos (-> (Listof Term) (Listof (Rel Term))))
(define (reflexive-clos a)
  (map ->rel a))


(: barbara RuleProc)
(define (barbara x li-rel)
  (cond
    [(null? li-rel) null]
    [else 
     (define res (memf (lambda ([y : (Rel Term)]) : Boolean
                               (and (equal? (rel-b x)
                                            (rel-a y))
                                    (not (equal? (rel-b y)
                                                 (rel-a y)))))
                       li-rel))

     (cond
       [(null? res) null]
       [(list? res)
        (cons (make-rel (rel-a x) (rel-b (car res)))
              (barbara x (cdr res)))]
       [else null])]))


(: down RuleProc)
(define (down r1 li-rel)
  (define x (rel-a r1))
  (define y (rel-b r1))
  (filter-map (lambda ([r : (Rel Term)]) : (Option (Rel Term))
                      (define b (rel-b r))
                      (cond
                        [(and (verb-phrase? b) (equal? (verb-phrase-object b) y))
                         (make-rel (rel-a r) (verb-phrase (verb-phrase-action b) x))]
                        [else #f]))
              li-rel))


(: all-to-self RuleProc)
(define (all-to-self r1 li-rel)
  (filter-map (lambda ([r : (Rel Term)]) : (Option (Rel Term))
                      (define a (rel-a r))
                      (define b (rel-b r))
                      (cond
                        [(and (verb-phrase? b) (equal? (verb-phrase-object b) a))
                         (make-rel (rel-a r) (verb-phrase (verb-phrase-action b) (self)))]
                        [else #f]))
              li-rel))

(: apply-rule (-> (Listof (Rel Term)) RuleProc * (Listof (Rel Term))))
(define (apply-rule rtc . rule-procs)
  (for/fold : (Listof (Rel Term))
      ([rtc^ rtc])
      ([rp rule-procs])
    (let loop : (Listof (Rel Term))
         ([rtc^^ rtc^])
         (define rtc* (for/fold : (Listof (Rel Term))
                          ([rtc^^^ rtc^^])
                          ([i (in-list rtc^^)])
                        (remove-duplicates (append (rp i rtc^^^) rtc^^^))))
         (debug-eprintf "acc* is ~a~n" rtc*)
         (if (equal? rtc* rtc^^) rtc*
             (loop rtc*)))))
                            

(: derive2 (-> (Listof Term) Root Boolean))
(define (derive2 premises conclusion)
  (define li-rel (apply-rule (map ->rel premises) barbara down all-to-self))
  (define r (->rel conclusion))
  (cond
    [(member r li-rel equal?) #t]
    [else
     (print-model (make-counter-model premises li-rel))
     false]))

(define-type Element (U Natural (List Natural Natural)))

(define (basic-element-maker [tick! : (-> Natural)]) : Element
  (tick!))

(define (element-maker-for-self [tick! : (-> Natural)]) : Element
  (list (tick!) (tick!)))

(define (normalize-elements [l : (Listof Element)]) : (Listof Integer)
  (cond
    [(empty? l) empty]
    [(pair? l)
     (define c (car l))
     (cond
       [(list? c) (append c (normalize-elements (cdr l)))]
       [(number? c) (cons c (normalize-elements (cdr l)))])]
    [else (error 'normalize "your are drunk")]))

(define (element-product [p : (Pairof Element Element)]) : (Listof (Pairof Integer Integer))
  (cond
    [(and (number? (car p)) (number? (cdr p))) (list (cons (car p) (cdr p)))]
    [(and (list? (car p)) (list? (cdr p))) (list (cons (first (car p)) (first (cdr p)))
                                                 (cons (first (car p)) (second (cdr p)))
                                                 (cons (second (car p)) (first (cdr p)))
                                                 (cons (second (car p)) (second (cdr p))))]
    [else (error 'element-prod "your are drunk")]))

(define (contains-subterm? [t : Term] [tgt : Term]) : Boolean
  (cond
    [(equal? t tgt) #t]
    [else
     (match t
       [(root a b) (and (contains-subterm? a t)
                        (contains-subterm? b t))]
       [(verb-phrase a o)
        (and (contains-subterm? a t)
             (contains-subterm? o t))]
       [else #f])]))

(: make-counter-model (-> (Listof Term) (Listof (Rel Term)) Model))
(define (make-counter-model ts rtc)

  (define contains-self? (memf (lambda ([arg : Term]) : Boolean
                                       (contains-subterm? arg (self)))
                               ts))
  (define non-rts (filter (lambda ([x : Term]) : Boolean
                                  (and (not (root? x))
                                       #;(not (verb-phrase? x))
                                       #;(not (self? x))
                                       ))
                          (remove-duplicates ts)))
  (define (make-counter) : (-> Natural)
    (define n : Natural 0)
    (λ () : Natural
      (define old n)
      (set! n (add1 n))
      old))

  (define counter (make-counter))

  (define em (if contains-self? element-maker-for-self
                 basic-element-maker))
  (define di
    (for/hash : (HashTable Term Element)
        ([j : Term (in-list non-rts)])
      (values j (em counter))))

  (define ret (for/hash : Model
                  ([i : Term (in-list (hash-keys di))]
                   #:when (noun? i))
                (let ([ret (sort (for/list : (Listof Element)
                                     ([j : (Rel Term) (in-list rtc)]
                                      #:when (equal? (rel-b j) i))
                                   (hash-ref di (rel-a j)))
                                 (lambda ([a : Element] [b : Element]) : Boolean
                                         (match* (a b)
                                           [((? integer?) (? integer?)) (<= a b)]
                                           [((? list?) (? list?)) (and (<= (first a) (first b))
                                                                       (<= (second a) (second b)))]
                                           [(_ _) (error 'compare "you are drunk")])))])
                  (values i (normalize-elements ret)))))

  (define (lookup [t : Term]) : (Listof Element)
    (list (hash-ref di t)))

  (define (pair-self [a : Element]) : (Listof (Pairof Integer Integer))
    (cond
      [(list? a) (list (cons (first a) (first a))
                       (cons (second a) (second a)))]
      [else (error 'pair-self "you are drunk")]))
  
  (define action-set (remove-duplicates (append* (for/list : (Listof (Listof (Pairof Integer Integer)))
                                                     ([i : (Rel Term) (in-list rtc)]
                                                      #:when (verb-phrase? (rel-b i)))
                                                   (for/fold : (Listof (Pair Integer Integer))
                                                       ([acc : (Listof (Pair Integer Integer)) '()])
                                                       ([j (in-list (lookup (rel-a i)))])
                                                     (define obj (verb-phrase-object (rel-b i)))
                                                     (cond
                                                       [(self? obj)
                                                        (append (pair-self j) acc)]
                                                       [else
                                                        (for/fold : (Listof (Pair Integer Integer))
                                                            ([acc^ acc])
                                                            ([k (in-list (lookup obj))])
                                                          (append (element-product (cons j k)) acc^))]))))))
  (hash-set ret (verb 'see) action-set))

(: print-model (-> Model Void))
(define (print-model m)
  (define (stringify (i : (U Integer (Pairof Integer Integer)))) : String
    (cond
      [(number? i) (number->string i)]
      [(pair? i) (format "{~a, ~a}" (car i) (cdr i))]))
  (for ([([k : Term][l : (Listof (U Integer (Pairof Integer Integer)))]) (in-hash m)])
    (printf "~a : {~a}~n" k (string-join (map stringify l) ", "))))


(define-syntax-rule (derive premise ... conclusion)
  (derive2 (append (->terms (parse-root (quote premise))) ...)
           (parse-root (quote conclusion))))


(module+ test
  (require typed/rackunit)
  (check-equal? (parse '(see all ducks)) (verb-phrase (verb 'see) (noun "ducks")))
  (check-equal? (parse '(see all (see all ducks))) (verb-phrase (verb 'see) (verb-phrase (verb 'see) (noun "ducks"))))
  (let* ([raw-input '(all dogs (see all (see all ducks)))]
         [rt (parse-root raw-input)])
    (check-equal? rt (root (noun "dogs") (verb-phrase (verb 'see) (verb-phrase (verb 'see) (noun "ducks")))))
    (check-equal? (length (->terms rt)) 5))
  
  (let* ([input (parse-root '(all ducks birds))]
         [terms (->terms input)])
    (check-equal? (length terms) 3))

  (check-equal? (barbara (make-rel (noun "1") (noun "2"))
                         (list (make-rel (noun "1") (noun "1")) (make-rel (noun "2") (noun "2")) (make-rel (noun "2") (noun "3"))))
                (list (make-rel (noun "1") (noun "3"))))
  (check-equal? (barbara (make-rel (noun "3") (noun "1"))
                         (list (make-rel (noun "1") (noun "2"))
                               (make-rel (noun "1") (noun "1"))
                               (make-rel (noun "2") (noun "2"))
                               (make-rel (noun "3") (noun "1"))
                               (make-rel (noun "3") (noun "3"))
                               (make-rel (noun "2") (noun "2"))))
                (list (make-rel (noun "3") (noun "2"))))

  (let* ([PUPPIES (noun "puppies")]
         [DOGS (noun "dogs")]
         [CATS (noun "cats")]
         [SEE-DOGS (verb-phrase (verb 'see) DOGS)]
         [SEE-PUPPIES (verb-phrase (verb 'see) PUPPIES)])
    (check-equal? (down (make-rel PUPPIES DOGS)
                        (list (make-rel CATS SEE-DOGS)))
                  (list
                   (make-rel CATS SEE-PUPPIES))))
  
  (check-true (derive (all girls American)
                      (all students girls)
                      (all students American)))

  (check-true (derive (all girls American)
                       (all students girls)
                       (all children students)
                       (all children American)))

  (check-false (derive (all girls American)
                        (all students girls)
                        (all children students)
                        (all girls children)))
  (println "starting test verbs")
  
  (check-true
   (derive (all dogs (see all cats))
           (all (see all cats) (see all hawks))
           (all dogs (see all hawks))))

  (check-true (derive (all puppies dogs)
                      (all cats (see all dogs))
                      (all cats (see all puppies))))

  (check-true (derive (all puppies dogs)
                      (all ducks (see all dogs))
                      (all (see all dogs) birds)
                      (all ducks birds)))
  
  (check-true (derive (all puppies dogs)
                      (all ducks (see all dogs))
                      (all (see all dogs) birds)
                      (all birds (see all humans))
                      (all (see all dogs) (see all humans))))

  (check-false (derive (all puppies dogs)
                       (all ducks (see all dogs))
                       (all (see all dogs) (see all puppie))))

  (printf "huskies~n")
  (check-false (derive
               (all huskies dogs)
               (all huskies (see all cats))
               (all (see all cats) dogs)))

  ;; all see all dogs see themselves
  ;; all dogs see themselves
  ;; all see themselves see all hawks
  (printf "start testing self~n")
  (check-true (derive (all dogs (see all dogs))
                      (all dogs (see self))))

  (check-false (derive (all dogs (see self))
                       (all dogs (see all dogs))))
  (check-false (derive (all puppies dogs)
                       (all dogs (see self))
                       (all dogs (see all dogs)))))
