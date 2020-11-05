#lang typed/racket

(struct (A) a-rel ([a : A] [b : A]) #:transparent)
(define-type Rel (All (X) (Listof (a-rel X))))

(: r-section (All (A) (-> A (Rel A) (Listof A))))
(define (r-section a rel)
  (for/list ([p (in-list rel)]
             #:when (equal? (a-rel-a p) a))
    (a-rel-b p)))

(: r-compose (All (A) (-> (Rel A) (Rel A) (Rel A))))
(define (r-compose rel1 rel2)
  (remove-duplicates (for*/list : (Rel A)
                         ([p1 rel1]
                          [p2 rel2]
                          #:when (equal? (a-rel-b p1) (a-rel-a p2)))
                       (a-rel (a-rel-a p1) (a-rel-b p2)))))

;; rtc: reflexsive transitive closure
(: rtc (All (A) (-> (Listof A) (Rel A) (Rel A))))
(define (rtc l r)
  (define i : (Rel A) (map (lambda ([x : A]) (a-rel x x)) l))
  (lfp (lambda ([s : (Rel A)]) : (Rel A) (remove-duplicates (append s (r-compose r s)))) i))

(: lfp (All (A) (-> (-> (Rel A) (Rel A)) (Rel A) (Rel A))))
(define (lfp f x)
  (cond
    [(equal? (f x) x) x]
    [else (lfp f (f x))]))

(struct klass ([name : String])
  #:transparent
  #:property prop:custom-write (λ ([me : klass] [port : Output-Port] _)
                                 (fprintf port "~a" (klass-name me))))

;; ;; KB-Entry : states if c1 is included in c2
(struct kb-entry ([c1 : klass] [c2 : klass] [res : Boolean]) #:transparent #:type-name KBEntry)

(struct all-stmt ([c1 : klass] [c2 : klass])
  #:type-name AllStmt
  #:transparent
  #:property prop:custom-write
  (lambda ([me : all-stmt] [port : Output-Port] _)
    (fprintf port "All ~a are ~a." (all-stmt-c1 me) (all-stmt-c2 me))))

(define-type Knowledge-Base (Listof KBEntry))
(: subset-rel (-> Knowledge-Base (Rel klass)))
(define (subset-rel kb)
  (define r (for/list : (Rel klass) ([entry (in-list kb)]
                                 #:when (kb-entry-res entry))
              (a-rel (kb-entry-c1 entry) (kb-entry-c2 entry))))
  (rtc (domain kb) r))

(: domain (-> Knowledge-Base (Listof klass)))
(define (domain kb)
  (define facts (for/fold : (Listof klass )
                    ([acc null])
                    ([entry (in-list kb)])
                  (cons (kb-entry-c1 entry)
                        (cons (kb-entry-c2 entry)
                              acc))))
  (remove-duplicates facts))

(: supersets (-> klass Knowledge-Base (Listof klass)))
 (define (supersets kls kb)
   (r-section kls (subset-rel kb)))

(: derive (-> Knowledge-Base AllStmt (Option (Listof klass))))
(define (derive kb stmt)
  (match stmt
    [(all-stmt as bs) (member bs (supersets as kb))]))

;; #;
;; (define (update-kb stmt kb)
;;   (match-define (statement c1 c2) stmt)
;;   (if (member c2 (supersets c1 kb)) false
;;       (cons (kb-entry c1 c2 #t) kb)))

(: parse (All (X) (-> String (-> klass klass X) X)))
(define (parse s tof)
  (match (string-split s " ")
    [(list "All" n1 "are" n2) (tof (klass n1) (klass n2))]))

(module+ test
    (require typed/rackunit)
    (check-equal? (r-compose (list (a-rel 10 20) (a-rel 20 30)) (list (a-rel 20 30)))
                  (list (a-rel 10 30)))
    (check-equal? (rtc (list 1 2) (list (a-rel 2 1)))
                  (list (a-rel 1 1) (a-rel 2 2) (a-rel 2 1)))
    ;; smoke test
    ;; All girls are American
    ;; All students are girls
    ;; ------------------------- Barbara
    ;; All students are American
    (define (fact->premise [s : String]) : KBEntry
      (parse s (lambda ([a : klass] [b : klass]) (kb-entry a b #t))))
    
    (define kb1 (list (fact->premise "All girls are American")
                      (fact->premise "All students are girls")
                      (fact->premise "All children are students")))
        (define conclusion (parse "All c are American" all-stmt))
    #;
    (check-not-false (derive kb1 conclusion)))
