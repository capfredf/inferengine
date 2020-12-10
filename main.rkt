#lang typed/racket
(define debug (make-parameter (ann #f Boolean)))

(define (debug-eprintf [fmt : String] . args)
  (when (debug)
    (apply eprintf fmt args)))

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


(: barbara (All (A) (-> (Rel A) (Listof (Rel A)) (Listof (Rel A)))))
(define (barbara x li-rel)
  (cond
    [(null? li-rel) null]
    [else 
     (define res (memf (lambda ([y : (Rel A)]) : Boolean
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


;; (barbara (rel 1 2) (list (rel 1 1) (rel 2 2) (rel 2 3)))

(: make-rtc (-> (Listof Term) (Listof (Rel Term))))
(define (make-rtc li-t)
  (define w/rc (reflexive-clos li-t))
  (let loop ([acc w/rc])
    (define acc* (for/fold : (Listof (Rel Term))
                     ([acc w/rc])
                     ([i (in-list w/rc)])
                   (remove-duplicates (append (barbara i acc) acc))))
    (if (equal? acc acc*) acc*
        (loop acc*))))


(: down (-> (Rel Term) (Listof (Rel Term)) (Listof (Rel Term))))
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

(: apply-down (-> (Listof (Rel Term)) (Listof (Rel Term))))
(define (apply-down rtc)
  (define acc* (for/fold : (Listof (Rel Term))
                     ([acc rtc])
                     ([i (in-list rtc)])
                 (remove-duplicates (append (down i acc) acc))))
  (if (equal? acc* rtc) acc*
      (apply-down acc*)))


(: all-to-self (-> (Rel Term) (Listof (Rel Term)) (Listof (Rel Term))))
(define (all-to-self r1 li-rel)
  (filter-map (lambda ([r : (Rel Term)]) : (Option (Rel Term))
                      (define a (rel-a r))
                      (define b (rel-b r))
                      (cond
                        [(and (verb-phrase? b) (equal? (verb-phrase-object b) a))
                         (make-rel (rel-a r) (verb-phrase (verb-phrase-action b) (self)))]
                        [else #f]))
              li-rel))

(: apply-all-to-self (-> (Listof (Rel Term)) (Listof (Rel Term))))
(define (apply-all-to-self rtc)
  (define acc* (for/fold : (Listof (Rel Term))
                     ([acc rtc])
                     ([i (in-list rtc)])
                 (remove-duplicates (append (all-to-self i acc) acc))))
  (debug-eprintf "acc* is ~a" acc*)
  (if (equal? acc* rtc) acc*
      (apply-all-to-self acc*)))

(define-type RuleProc (-> (Rel Term) (Listof (Rel Term)) (Listof (Rel Term))))

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
         (debug-eprintf "acc* is ~a" rtc*)
         (if (equal? rtc* rtc^^) rtc*
             (loop rtc*)))))
                            

(: derive2 (-> (Listof Term) Root Boolean))
(define (derive2 premises conclusion)
  (define rtc (make-rtc premises))
  (define rtc^ (apply-rule (make-rtc premises) down all-to-self))
  (define r (->rel conclusion))
  (cond
    [(member r rtc^ equal?) #t]
    [else
     (when (debug)
       (printf "~a~n" rtc^))
     (print-model (make-counter-model premises rtc^))
     false]))


(: make-counter-model (-> (Listof Term) (Listof (Rel Term)) Model))
(define (make-counter-model ts rtc)
  (define non-rts (filter (lambda ([x : Term]) : Boolean
                                  (and (not (root? x))
                                       (not (verb-phrase? x))))
                          (remove-duplicates ts)))
  (define di
    (for/hash : (HashTable Term Integer)
        ([j : Term (in-list non-rts)]
         [i : Integer (in-naturals)])
      (values j i)))

  (define ret (for/hash : Model
                  ([i : Term (in-list (hash-keys di))])
                (let ([ret (sort (for/list : (Listof Integer)
                                     ([j : (Rel Term) (in-list rtc)]
                                      #:when (equal? (rel-b j) i))
                                   (hash-ref di (rel-a j)))
                                 <=)])
                  (values i ret))))
  ;; see dogs see cats
  (define (lookup [t : Term]) : (Listof Integer)
    (cond
      [(and (noun? t) (hash-ref di t #f)) => (lambda (v) (list v))]
      [(verb-phrase? t) (define ret (for/fold : (Listof Integer)
                                    ([acc : (Listof Integer) '()])
                                    ([i : (Rel Term) (in-list rtc)])
                                  #:final (equal? (rel-b i) t)
                                  (lookup (rel-a i))))
                    ret]
      [else (error 'hi "nothing found")]))
  
  (define action-set (remove-duplicates (append* (for/list : (Listof (Listof (Pairof Integer Integer)))
                                                     ([i : (Rel Term) (in-list rtc)]
                                                      #:when (verb-phrase? (rel-b i)))
                                                   (for*/list : (Listof (Pair Integer Integer))
                                                       ([j (in-list (lookup (rel-a i)))]
                                                        [k (in-list (lookup (verb-phrase-object (rel-b i))))])
                                                     (cons j k))))))
  (hash-set ret (verb 'see) action-set))

(: print-model (-> Model Void))
(define (print-model m)
  (define (stringify (i : (U Integer (Pairof Integer Integer)))) : String
    (cond
      [(number? i) (number->string i)]
      [(pair? i) (format "{~a, ~a}" (car i) (cdr i))]))
  (for ([([k : Term][l : (Listof (U Integer (Pairof Integer Integer)))]) (in-hash m)])
    (printf "~a : {~a}~n" k (string-join (map stringify l) ", "))))

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

  (check-equal? (barbara (make-rel 1 2) (list (make-rel 1 1) (make-rel 2 2) (make-rel 2 3)))
                (list (make-rel 1 3)))
  (check-equal? (barbara (make-rel 3 1) (list (make-rel 1 2) (make-rel 1 1) (make-rel 2 2) (make-rel 3 1) (make-rel 3 3) (make-rel 2 2)))
                (list (make-rel 3 2)))

  (let* ([PUPPIES (noun "puppies")]
         [DOGS (noun "dogs")]
         [CATS (noun "cats")]
         [SEE-DOGS (verb-phrase (verb 'see) DOGS)]
         [SEE-PUPPIES (verb-phrase (verb 'see) PUPPIES)])
    (check-equal? (down (make-rel PUPPIES DOGS)
                        (list (make-rel CATS SEE-DOGS)))
                  (list
                   (make-rel CATS SEE-PUPPIES))))
  
  (check-true (derive2 (append (->terms (parse-root '(all girls American)))
                               (->terms (parse-root '(all students girls))))
                       (parse-root '(all students American))))

  (check-true (derive2 (append (->terms (parse-root '(all girls American)))
                               (->terms (parse-root '(all students girls)))
                               (->terms (parse-root '(all children students))))
                       (parse-root '(all children American))))

  (check-false (derive2 (append (->terms (parse-root '(all girls American)))
                                (->terms (parse-root '(all students girls)))
                                (->terms (parse-root '(all children students))))
                        (parse-root '(all girls children))))
  (println "starting test verbs")
  
  (check-true
   (derive2 (append (->terms (parse-root '(all dogs (see all cats))))
                               (->terms (parse-root '(all (see all cats) (see all hawks)))))
                       (parse-root '(all dogs (see all hawks)))))

  (check-true (derive2 (append
                        (->terms (parse-root '(all puppies dogs)))
                        (->terms (parse-root '(all cats (see all dogs)))))
                       (parse-root '(all cats (see all puppies)))))

  (check-true (derive2 (append
                        (->terms (parse-root '(all puppies dogs)))
                        (->terms (parse-root '(all ducks (see all dogs))))
                        (->terms (parse-root '(all (see all dogs) birds))))
                       (parse-root '(all ducks birds))))
  
  (check-true (derive2 (append
                        (->terms (parse-root '(all puppies dogs)))
                        (->terms (parse-root '(all ducks (see all dogs))))
                        (->terms (parse-root '(all (see all dogs) birds)))
                        (->terms (parse-root '(all birds (see all humans)))))
                       (parse-root '(all (see all dogs) (see all humans)))))

  (check-false (derive2 (append
                         (->terms (parse-root '(all puppies dogs)))
                         (->terms (parse-root '(all ducks (see all dogs)))))
                        (parse-root '(all (see all dogs) (see all puppie)))))

  ;; all see all dogs see themselves
  ;; all dogs see themselves
  ;; all see themselves see all hawks
  (check-true (derive2 (append
                        (->terms (parse-root '(all dogs (see all dogs)))))
                       (parse-root '(all dogs (see self)))))
  
  (check-false (derive2 (append
                        (->terms (parse-root '(all dogs (see self)))))
                       (parse-root '(all dogs (see all dogs))))))
