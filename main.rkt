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

;; (struct klass (name) #:transparent
;;   #:property prop:custom-write (λ (me port _)
;;                                  (fprintf port (klass-name me))))

;; ;; KB-Entry : states if c1 is included in c2
;; (struct kb-entry (c1 c2 res) #:transparent)

;; (define (make-printer start mid end)
;;   (lambda (me port mode)
;;     (fprintf "~a ~a ~a ~a ~a" start (statement-c1 me) mid (statement-c2 me) end)))

;; (struct statement (c1 c2) #:transparent)
;; (struct all-stmt statement ()
;;   #:methods gen:custom-write [(define write-proc (make-printer "All" "are" "."))])


;; (define (subset-rel kb)
;;   (define r (for/list ([entry (in-list kb)]
;;                        #:when (kb-entry-res entry))
;;               (a-rel (kb-entry-c1 entry) (kb-entry-c2 entry))))
;;   (rtc (domain kb) r))

;; (define (domain kb)
;;   (define facts (for/fold ([acc null])
;;                           ([entry (in-list kb)])
;;                   (cons (kb-entry-c1 entry)
;;                         (cons (kb-entry-c2 entry)
;;                               acc))))
;;   (remove-duplicates facts))

;; (define (supersets kls kb)
;;   (r-section kls (subset-rel kb)))


;; (define (derive kb stmt)
;;   (match stmt
;;     [(all-stmt as bs) (member bs (supersets as kb))]))

;; #;
;; (define (update-kb stmt kb)
;;   (match-define (statement c1 c2) stmt)
;;   (if (member c2 (supersets c1 kb)) false
;;       (cons (kb-entry c1 c2 #t) kb)))

;; (define (parse s tof)
;;   (match (string-split s " ")
;;     [(list "All" n1 "are" n2) (tof (klass n1) (klass n2))]))

(module+ test
    (require typed/rackunit)
    (check-equal? (r-compose (list (a-rel 10 20) (a-rel 20 30)) (list (a-rel 20 30)))
                  (list (a-rel 10 30)))
    (check-equal? (rtc (list 1 2) (list (a-rel 2 1)))
                  (list (a-rel 1 1) (a-rel 2 2) (a-rel 2 1)))
;;     ;; smoke test
;;     ;; All girls are American
;;     ;; All students are girls
;;     ;; ------------------------- Barbara
;;     ;; All students are American
;;     (define fact->premise (lambda (s)
;;                             (parse s (lambda (a b) (kb-entry a b #t)))))
    
;;     (define kb1 (list (fact->premise "All girls are American")
;;                       (fact->premise "All students are girls")
;;                       (fact->premise "All c are students")))
    ;;     (define conclusion (parse "All c are American" all-stmt))
    #;
    (check-not-false (derive kb1 conclusion)))
