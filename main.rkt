#lang racket

(struct a-rel (a b) #:transparent)

(define (r-section a rel)
  (for/list ([p (in-list rel)]
             #:when (equal? (a-rel-a p) a))
    (a-rel-b p)))

(define (r-compose rel1 rel2)
  (remove-duplicates (for*/list ([p1 rel1]
                                [p2 rel2]
                                #:when (equal? (a-rel-b p1) (a-rel-a p2)))
                       (a-rel (a-rel-a p1) (a-rel-b p2)))))

;; rtc: reflexsive transitive closure
(define (rtc l r)
  (define i (map (lambda (x) (a-rel x x)) l))
  (lfp (lambda (s) (remove-duplicates (append s (r-compose r s)))) i))

;; least fixpoint
(define (lfp f x)
  (cond
    [(equal? (f x) x) x]
    [else (lfp f (f x))]))

(struct klass (name) #:transparent
  #:methods gen:custom-write [(define write-proc
                                (λ (me port _)
                                  (fprintf port (klass-name me))))])
(struct oppklass (name) #:transparent
  #:methods gen:custom-write [(define write-proc
                                (λ (me port _)
                                  (fprintf port "non-~a"(oppklass-name me))))])

(define (opp kls)
  (match kls
    [(klass name) (oppklass name)]
    [(oppklass name) (klass name)]))


;; KB-Entry : states if c1 is included in c2
(struct kb-entry (c1 c2 res) #:transparent)

(define (make-printer start mid end)
  (lambda (me port mode)
    (fprintf "~a ~a ~a ~a ~a" start (statement-c1 me) mid (statement-c2 me) end)))

(struct statement (c1 c2) #:transparent)
(struct all-stmt statement ()
  #:methods gen:custom-write [(define write-proc (make-printer "All" "are" "."))])


(define (subset-rel kb)
  (define r (for/list ([entry (in-list kb)]
                       #:when (kb-entry-res entry))
              (a-rel (kb-entry-c1 entry) (kb-entry-c2 entry))))
  (rtc (domain kb) r))

(define (domain kb)
  (define facts (for/fold ([acc null])
                          ([entry (in-list kb)])
                  (cons (kb-entry-c1 entry)
                        (cons (kb-entry-c2 entry)
                              acc))))
  (remove-duplicates facts))

(define (supersets kls kb)
  (r-section kls (subset-rel kb)))


(define (derive kb stmt)
  (match stmt
    [(all-stmt as bs) (member bs (supersets as kb))]))

(define (update-kb stmt kb)
  (match-define (statement c1 c2) stmt)
  (if (member c2 (supersets c1 kb)) false
      (cons (kb-entry c1 c2 #t) kb)))

(define (parse s tof)
  (match (string-split s " ")
    [(list "All" n1 "are" n2) (tof (klass n1) (klass n2))]))

(module+ test
    (require rackunit)
    (check-equal? (r-compose (list (a-rel 10 20) (a-rel 20 30)) (list (a-rel 20 30)))
                  (list (a-rel 10 30)))
    (check-equal? (rtc (list 1 2) (list (a-rel 2 1)))
                  (list (a-rel 1 1) (a-rel 2 2) (a-rel 2 1)))
    ;; smoke test
    ;; All girls are American
    ;; All students are girls
    ;; ------------------------- Barbara
    ;; All students are American
    (define fact->premise (lambda (s)
                            (parse s (lambda (a b) (kb-entry a b #t)))))
    
    (define kb1 (list (fact->premise "All girls are American")
                      (fact->premise "All students are girls")))
    (define conclusion (parse "All girls are American" all-stmt))
    (check-not-false (derive kb1 conclusion)))
