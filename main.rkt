#lang typed/racket

(struct (A) a-rel ([a : A] [b : A]) #:transparent)
(define-type Rel (All (X) (Listof (a-rel X))))

(define-type Model (HashTable Term (Listof Integer)))

(struct term () #:type-name Term #:transparent)

(struct root-term term ([p : Term]
                        [q : Term])
  #:type-name RootTerm
  #:transparent
  #:property prop:custom-write (λ ([me : NounTerm] [port : Output-Port] _)
                                 (fprintf port "[[~a ~a]]" (root-term-p me) (root-term-q me))))

(struct noun-term term ([name : String])
  #:type-name NounTerm
  #:transparent
  #:property prop:custom-write (λ ([me : NounTerm] [port : Output-Port] _)
                                 (fprintf port "[[~a]]" (noun-term-name me))))

#;
(struct be-term term ([pnoun : Term])
  #:type-name BeTerm
  #:transparent
  #:property prop:custom-write (λ ([me : term] [port : Output-Port] _)
                                 (fprintf port "<are ~a>" (be-term-pnoun me))))

(define-type TransitiveVerb (U 'see))

(define-type ObjectTerm (U TVTerm NounTerm))

(struct tv-term term ([action : TransitiveVerb]
                      [object : Term])
  #:type-name TVTerm
  #:transparent
  #:property prop:custom-write (λ ([me : TVTerm] [port : Output-Port] _)
                                 (fprintf port "~a ~a" (tv-term-action me) (tv-term-object me))))




(: parse2 (-> Any Term))
(define (parse2 s)
  (match s
    [`,n #:when (symbol? n)
         (noun-term (symbol->string n))]))

(define (parse-root [s : Any]) : RootTerm
  (match-define `(all ,p ,q) s)
  (root-term (parse2 p) (parse2 q)))

(: ->terms (-> Term (Listof Term)))
(define (->terms t)
  (cond
    [(root-term? t) (append (list t) (->terms (root-term-p t)) (->terms (root-term-q t)))]
    [(noun-term? t) (list t)]
    [(term? t) (error '->terms "you are drunk")]))


(: ->rel (-> Term (a-rel Term)))
(define (->rel t)
  (cond
    [(noun-term? t) (a-rel t t)]
    [(root-term? t) (a-rel (root-term-p t) (root-term-q t))]
    [else (error 'rc "you are drunk")]))

(: reflexive-clos (-> (Listof Term) (Rel Term)))
(define (reflexive-clos a)
  (map ->rel a))


(: barbara (All (A) (-> (a-rel A) (Rel A) (Rel A))))
(define (barbara x rel)
  (cond
    [(null? rel) null]
    [else 
     (define res (memf (lambda ([y : (a-rel A)]) : Boolean
                               (and (equal? (a-rel-b x)
                                            (a-rel-a y))
                                    (not (equal? (a-rel-b y)
                                                 (a-rel-a y)))))
                       rel))

     (cond
       [(null? res) null]
       [(list? res)
        (cons (a-rel (a-rel-a x) (a-rel-b (car res)))
              (barbara x (cdr res)))]
       [else null])]))


;; (barbara (a-rel 1 2) (list (a-rel 1 1) (a-rel 2 2) (a-rel 2 3)))

(: generate-rtc (-> (Listof Term) (Rel Term)))
(define (generate-rtc li-t)
  (define w/rc (reflexive-clos li-t))
  (for/fold ([acc w/rc])
            ([i (in-list w/rc)])
    (remove-duplicates (append (barbara i acc) acc))))


(: derive2 (-> (Listof Term) RootTerm Boolean))
(define (derive2 premises conclusion)
  (define rtc (generate-rtc premises))
  (define r (a-rel (root-term-p conclusion)
                   (root-term-q conclusion)))
  (cond
    [(member r rtc) #t]
    [else
     (print-model (generate-counter-model premises))
     false]))


(: generate-counter-model (-> (Listof Term) Model))
(define (generate-counter-model ts)
  (define n 0)
  (define (count!) : Integer
    (let ([r n])
      (set! n (+ n 1))
      r))
  (define di
    (for/hash : (HashTable Term Integer)
        ([j : Term (in-list (remove-duplicates ts))]
         #:when (not (root-term? j)))
      (values j (count!))))
  (define rtc (generate-rtc ts))
  (for/hash : Model
      ([i : Term (in-list (hash-keys di))])
    (values i
            (sort (for/list : (Listof Integer)
                      ([j : (a-rel Term) (in-list rtc)]
                       #:when (equal? (a-rel-b j) i))
                    (hash-ref di (a-rel-a j)))
                  <=))))

(: print-model (-> Model Void))
(define (print-model m)
  (for ([([k : Term][l : (Listof Integer)]) (in-hash m)])
    (printf "~a : {~a}~n" k (string-join (map number->string l) ", "))))


(module+ test
    (require typed/rackunit)
    (let* ([input (parse-root '(all ducks birds))]
           [terms (->terms input)])
      (check-equal? (length terms) 3))

    (check-equal? (barbara (a-rel 1 2) (list (a-rel 1 1) (a-rel 2 2) (a-rel 2 3)))
                  (list (a-rel 1 3)))
    (check-equal? (barbara (a-rel 3 1) (list (a-rel 1 2) (a-rel 1 1) (a-rel 2 2) (a-rel 3 1) (a-rel 3 3) (a-rel 2 2)))
                  (list (a-rel 3 2)))

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
                          (parse-root '(all girls children)))))
