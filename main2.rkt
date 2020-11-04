#lang racket

(struct variable (name idx) #:transparent)

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
(struct np+ (kind det n)) ;; if kind = 1 n is a CN; otherwise n is a RCN
(define (np? x)
  (or
   (ormap (λ (a) (equal? x a)) (list 'Snowhite 'Alice 'Dorothy 'Godilocks 'LittleMock 'Atreyu))
   (np+? x)))


(define (det? x)
  (ormap (curry equal? x) (list 'The 'Every 'Some 'No 'Most)))

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

