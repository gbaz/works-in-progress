#lang racket
(require racket/match)

; type formers
(define (type-nat) 'type-nat)
(define (type-unit) 'type-unit)
(struct type-and (x y))
(struct type-or  (x y))
(struct type-fun (dom codom))
; dependency
(struct type-pi  (var dom codom))
(struct type-sig (var dom codom))
(define (type-type) 'type) ;; inconsistent!

; value formers
(struct lam (var vt body))
(struct app (fun arg))
;cons and either we take ambiently

; dependency
(struct lam-pi (var vt body))
(struct sigma  (val vt snd))

(define (type? env t) 
  (match t
    ['type #t]
    ['type-nat #t]
    ['type-unit #t]
    [(type-and a b) (and (type? env a) (type? env b))]
    [(type-or  a b) (and (type? env a) (type? env b))]
    [(type-fun a b) (and (type? env a) (type? env b))]
    [(type-pi  var a b) (and (type? env a) (type? (cons (cons var a) env) b))]
    [(type-sig val a b) (and (type? env a) (type? (cons (cons val a) env) b))]
    [_ #f]
    ))
    
(define (hasType? env x t)
  (match x 
    [(app (lam fvar vt body) arg)
       (and (hasType? env arg vt)
            (hasType? (cons (cons fvar vt) env) body t))]
    ;dependency
    [(app (lam-pi fvar vt body) arg)
       (and (hasType? env arg vt)
            (hasType? (cons (cons fvar vt env)) body (subst fvar arg t)))]
    [(var vname) #:when (symbol? vname)
                 (eq? t (cdr (assoc vname env)))]
    [_ (match t
      ['type-nat (and (integer? x) (>= x 0))]
      ['type-unit (null? x)]
      [(type-and a b)
       (match x 
         [(cons y z) (and (hasType? env y a)
                          (hasType? env z b))])]
      [(type-or a b)
         (match x 
           [(cons 'l y) (hasType? env y a)]
           [(cons 'r z) (hasType? env z b)])]
      [(type-fun a b)
         (match x
          [(lam y yt z)    (and (eqType? env yt a)
                                (hasType? (cons (cons y a) env) z b))])]
      [(type-pi fvar a b)
         (match x
          [(lam-pi y yt z) (and (eqType? env yt a) (eq? fvar y)
                                (hasType? (cons (cons y a) env) z b))])]
      [(type-sig fvar a b)
         (match x
           [(sigma y yt z) (and (eqType? env yt a) (hasType? y a)
                                (hasType? env (subst fvar y z) b))])]
     )]
    ))

; substitution and reduction
(define (subst v arg body) 
  (reduce (match body
    [(type-and a b)     (type-and    (subst v arg a) (subst v arg b))]
    [(type-or  a b)     (type-or     (subst v arg a) (subst v arg b))]
    [(type-fun a b)     (type-fun    (subst v arg a) (subst v arg b))]
    [(type-pi  var a b) (type-pi var (subst v arg a) (subst v arg b))]

    [(cons a b)  (cons (subst v arg a) (subst v arg b))]
    [(list 'l a) ('l   (subst v arg a))]
    [(list 'r a) ('r   (subst v arg a))]

    [(var vname) #:when (eq? vname v) arg]
    [(var vname) #:when (symbol? vname) vname]
            
    ;; this should suffice to avoid capture
    [(lam var vt b)    (lam    var vt (if (eq? var v) b (subst v arg b)))]
    [(lam-pi var vt b) (lam-pi var vt (if (eq? var v) b (subst v arg b)))]
    [(app f a) (reduce (app (subst v arg f) (subst v arg a)))]
  )))

; strict
(define (reduce body) 
  (match body
    [(app (lam    var vt body) arg) (subst var (reduce arg) body)]
    [(app (lam-pi var vt body) arg) (subst var (reduce arg) body)]
    [(app fun arg) (reduce (app (reduce fun) (reduce arg)))]
    [_ body]
    ))

(define (eqType? env t1 t2) (eq? t1 t2))
(define (eqVal?  env typ v1 v2) (eq? v1 v2))
(define (getType env v1) (#f))

(define id-nat (lam 'x (type-nat) 'x))
(hasType? '() id-nat (type-fun (type-nat) (type-nat)))
(reduce (app id-nat 5))

(define id-forall (lam-pi 'x (type-type) (lam 'y 'x 'y)))
(hasType? '() id-forall (type-pi 'x (type-type) (type-fun 'x 'x)))

(reduce (app (app id-forall (type-nat)) 5))

;; todo -- prims
;; todo -- simplicial equality