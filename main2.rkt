#lang racket

(struct variable (name) #:transparent)

(struct formula () #:transparent)
(struct atom formula (name ts))
(struct eg formula (t1 t2))
(struct neg formula (fm))
(struct impl formula (fm1 fm2))
(struct equi formula (fm1 fm2))
(struct conj formula (fms))
(struct disj formula (fms))
(struct forall formula (var fm))
(struct exists formula (var fm))

(struct term () #:transparent)
(struct var-term term (variable) #:transparent)
(struct struct-term term (name ts))

(struct LF (formula term) #:transparent)


(struct sentence (np vp) #:transparent)
(struct np+ () #:transparent)
(struct np1 np+ (det cn))
(struct np2 np+ (det rcn))

(define (np? x)
  (or
   (ormap (λ (a) (equal? x a)) (list 'Snowhite 'Alice 'JonSnow))
   (np+? x)))


(define (det? x)
  (ormap (curry equal? x) (list 'Every)))

(define (cn? x)
  (ormap (curry equal? x) (list 'Girl 'Boy 'Princess 'Dwarf 'Giant 'Wizard 'Sward 'Dagger)))

(struct adjective () #:transparent)

(struct rcn () #:transparent)
(struct rcn1 rcn (cn vp))
(struct rcn2 rcn (cn np tv))
(struct rcn3 rcn (cn np tv))
(define (vp? x)
  (or
   (ormap (curry equal? x) (list 'Laughed))
   (tv? x)))

(struct tv () #:transparent)
(struct saw tv (np) #:transparent)


;; LF-sentence : (-> sentence LF)
(define (LF-sentence sent)
  (LF-np (sentence-np sent) (sentence-vp sent)))

;; LF-np : (-> np (-> (-> term LF) LF))
(define (LF-np np)
  (match np
    ['Snowhite (λ (p) (p (struct-term "SnowWhite" [])))]
    ['Alice (λ (p) (p (struct-term "Alice" [])))]
    ['JonSnow (λ (p) (p (struct-term "JonSnow" [])))]
    [(np1 det cn) ((LF-det det) (LF-cn cn))]
    [(np2 det rcn) ((LF-det det) (LF-rcn rcn))]))

;; LF-det : (-> Det (-> Term LF) (-> (-> Term LF) LF))
(define (LF-det x p)
  
  (cond
    [(equal? x 'Every)
     (λ (q)
       (define v (Variable (gensym 'x)))
       (forall v
               (impl (p (var-term v)))
               (impl (q (var-term v)))))]))
