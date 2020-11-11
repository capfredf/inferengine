#lang typed/racket

(struct (A) a-rel ([a : A] [b : A]) #:transparent)
(define-type Rel (All (X) (Listof (a-rel X))))

(define-type Model (HashTable String (Listof String)))

;; (: generate-counter-model (-> Knowledge-Base Model))
;; (define (generate-counter-model kb)
;;   (define us (domain kb))
;;   (for/hash : (HashTable String (Listof String))
;;       ([i (in-list us)])
;;     (values (klass-name i)
;;             (for/list : (Listof String)
;;                   ([j (in-list us)]
;;                    #:when (member i (supersets j kb)))
;;               (klass-name j)))))


;; (: interp (-> Model (Option String) Void))
;; (define (interp model maybe-term)
;;   (unless maybe-term
;;     (for ([(key ele) (in-hash model)])
;;       (printf "[[~a]] : ~a~n" key ele))))


(struct term () #:type-name Term #:transparent)

(struct root-term term ([p : Term]
                        [q : Term])
  #:type-name RootTerm
  #:transparent
  #:property prop:custom-write (λ ([me : NounTerm] [port : Output-Port] _)
                                 (fprintf port "<~a ~a>" (root-term-p me) (root-term-q me))))

(struct noun-term term ([name : String])
  #:type-name NounTerm
  #:transparent
  #:property prop:custom-write (λ ([me : NounTerm] [port : Output-Port] _)
                                 (fprintf port "<~a>" (noun-term-name me))))

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



;; (ann (list (noun-term "students")) (Listof Term))
(noun-term "American")
;; #;
;; (define (update-kb stmt kb)
;;   (match-define (statement c1 c2) stmt)
;;   (if (member c2 (supersets c1 kb)) false
;;       (cons (kb-entry c1 c2 #t) kb)))

#;
(struct all-stmt2 ([c1 : klass] [c2 : klass])
  #:type-name AllStmt2
  #:transparent
  #:property prop:custom-write
  (lambda ([me : all-stmt2] [port : Output-Port] _)
    (fprintf port "All ~a ~a." (all-stmt-c1 me) (all-stmt-c2 me))))

;; (define-type Premise (Listof AllStmt2))

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

;; (: parse3 (-> Any (Listof NounTerm)))
;; (define (parse3 s)
;;   (cond
;;     #;
;;     [(list? s) (match-define `(all ,p ,q) s)
;;                (append (parse2 p) (parse2 q))]
;;     [(symbol? s) (list (noun-term s #;(symbol->string n)))]
;;     [else null]))

;; (: dummy (-> Any (Listof Term)))
;; (define (dummy s)
;;   (list (noun-term "students")))

(: reflexive-clos (-> (Listof Term) (Rel Term)))
(define (reflexive-clos a)
  (for/list ([i (in-list a)])
    (cond
      [(noun-term? i) (a-rel i i)]
      [(root-term? i) (a-rel (root-term-p i) (root-term-q i))]
      [else (error 'rc "you are drunk")])))


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
    [else false]))


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
    #;#;
    (define conclusion2 (parse "All girls are children" all-stmt))
    (check-false (derive kb1 (car conclusion2))))
