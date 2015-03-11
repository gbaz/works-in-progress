#lang racket
(require racket/match)

; value formers
(struct lam (var vt body))
(struct app (fun arg))
; primitives
(struct prim (env typ body))
;;TODO new-prim alias with empty env.
; dependency
(struct lam-pi (var vt body))
(struct sigma  (val vt snd))

; type formers
(struct type-fun (dom codom))
; one basic type
(define (type-unit) 'type-unit)
; dependency
(struct type-pi  (var dom codom))
(struct type-sig (var dom codom))
(define (type-type) 'type) ;; inconsistent!

(define (cons-env nm typ val env)
  (cons (cons nm (cons typ val)) env))

(define (find-env nm env)
  (match (assoc nm env)
    [(cons a b) b]
    [_ #f]))

(define (type? env t) 
  (match t
    [(type-fun a b) (and (type? env a) (type? env b))]
    ['type-unit #t]

    [(type-pi  var a b) (and (type? env a) (type? (cons-env var a #f env) b))]
    [(type-sig val a b) (and (type? env a) (type? (cons-env val a #f env) b))]
    ['type #t]
    [_ (type?-additional env t)]
    ))

(define (hasType? env x t)
  (match x 
    [(app (lam fvar vt body) arg)
       (and (hasType? env arg vt)
            (hasType? (cons-env fvar vt arg env) body t))]
    [(prim primEnv typ body) (eqType? env typ t)]

    ;dependency
    [(app (lam-pi fvar vt body) arg)
       (and (hasType? env arg vt)
            (hasType? (cons-env fvar vt arg env)) body )]    
    [(var vname) #:when (symbol? vname)
                 (eqType? env t (car (find-env vname env)))]
    [_ (match t
      [(type-fun a b)
         (match x
          [(lam y yt z)    (and (eqType? env yt a)
                                (hasType? (cons-env y a #f env) z b))])]
      ['type-unit (null? x)]

      ;; todo do I need to substitute in the b? what?
      ;; todo use beta-eq? how?
      [(type-pi fvar a b)
         (match x
          [(lam-pi y yt z) (and (eqType? env yt a) (eq? fvar y)
                                (hasType? (cons-env y a #f env) z (reduce (cons-env y a #f env) b))
                               )])]
         [(type-sig fvar a b)
         (match x
           [(sigma y yt z) (and (eqType? env yt a) (hasType? y a)
                                (hasType? (cons-env fvar a y) (reduce b)))])]
      [_ (hasType?-additional env x t)]
     )]
    ))

; strict
;;TODO delete envs from everywhere...
;;OR pack into a primEnv if you hit a prim, and otherwise don't subst.
;; i.e. reducing a prim in an env just packs in the env..
(define (reduce env body) 
  (match body
    [(var vname) #:when (symbol? vname) (match (find-env vname env) [(cons a b) b] [_ body])]
    [(app (lam    var   vt  b) arg) (reduce env (subst env var (reduce env arg) b))] ;(reduce (cons-env var vt (reduce env arg) env) b)]
    [(app (lam-pi var   vt  b) arg) (reduce env (subst env var (reduce env arg) b))] ;(reduce (cons-env var vt (reduce env arg) env) b)]
    [(app (prim primEnv typ b) arg) (reduce env (b primEnv (reduce env arg)))]
    [(app fun arg) (if (symbol? fun)
                       (match (find-env fun env) [(cons a f) (reduce env (app f arg))] [_ body])
                       (reduce env (app (reduce env fun) arg)))]
    [_ body] ;;(reduce-additional body)]
    ))

(define (subst env v arg body) 
  (reduce env (match body
    [(type-fun a b)     (type-fun    (subst env v arg a) (subst env v arg b))]
    [(type-pi  var a b) (type-pi var (subst env v arg a) (subst env v arg b))]

    [(var vname) #:when (eq? vname v) arg]
    [(var vname) #:when (symbol? vname) vname]
    
    ;; this does not suffice to avoid capture -- what if we're subsituting something that is in the free vars of x?
    ;; we'll need to rename...
    [(lam var vt b)    (lam    var vt (if (eq? var v) b (subst env v arg b)))]
    [(lam-pi var vt b) (lam-pi var vt (if (eq? var v) b (subst env v arg b)))]
    [(app f a) (reduce env (app (subst v arg f) (subst env v arg a)))]
    [(prim primEnv typ b) (prim (cons-env v #f arg primEnv) typ b)]
    
    [_ (subst-additional env v arg body)]
  )))
;; extensions

(define type-judgments '())
(define (type?-additional env t) 
  (define (iter lst)
    (match lst
      [(list-rest p ps) (if (p env t) #t (iter ps))]
      [_ #f]
   ))
  (iter type-judgments))

(define hasType-judgments '())
(define (hasType?-additional env x t) 
  (define (iter lst)
    (match lst
      [(list-rest p ps) (if (p env x t) #t (iter ps))]
      [_ #f]
   ))
  (iter hasType-judgments))

(define subst-rules '())
(define (subst-additional env v arg body)
  (foldl (lambda (f acc)
           (f env v arg acc))
         body
         subst-rules
   ))

(define reduce-rules '())
(define (reduce-additional body)
  (foldl (lambda (f acc)
           (f acc))
         body
         reduce-rules
   ))

(define (new-form type-judgment hasType-judgment subst-fun reduce-fun)
  (set! type-judgments (cons type-judgment type-judgments))
  (set! hasType-judgments (cons hasType-judgment hasType-judgments))
  (set! subst-rules  (cons subst-fun subst-rules))
  (set! reduce-rules (cons reduce-fun reduce-rules)))

(struct type-and (x y))
(define and-intro
  (lam-pi 'a (type-type) (lam-pi 'b (type-type)
    (prim '()
          (type-fun 'a (type-fun 'b (type-and 'a 'b)))
          (lambda (a) (prim (type-fun 'b (type-and 'a 'b))
                           (lambda (b) (cons a b))))))))
(define and-elim-fst
  (lam-pi 'a (type-type) (lam-pi 'b (type-type) (prim '() (type-fun (type-and 'a 'b) 'a)
                                                      (lambda (env x) (car x))))))
(define and-elim-snd
  (lam-pi 'a (type-type) (lam-pi 'b (type-type) (prim '() (type-fun (type-and 'a 'b) 'a)
                                                      (lambda (env x) (cdr x))))))                     
(new-form 
 (lambda (env t)
   (match t 
     [(type-and a b) (and (type? env a) (type? env b))]
     [_ #f]))
 (lambda (env x t)
   (match t
     [(type-and a b)
      (match x 
        [(cons y z) (and (hasType? env y a)
                         (hasType? env z b))])]
     [_ #f]))
 (lambda (env v arg x)
   (match x
     [(cons a b) (cons (subst env v arg a) (subst env v arg b))]
     [_ x]))
 ;; todo substitution in types
 (lambda (x) x))

(struct type-or (x y))
(define or-intro-left
  (lam-pi 'a (type-type) (lam-pi 'b (type-type)
    (prim '() (type-fun 'a (type-or 'a 'b))
          (lambda (env x) (cons 'l x))))))
(define or-intro-right
  (lam-pi 'a (type-type) (lam-pi 'b (type-type)
    (prim '() (type-fun 'b (type-or 'a 'b))
          (lambda (env x) (cons 'r x))))))

(define or-elim
  (lam-pi 'a (type-type)
  (lam-pi 'b (type-type)
  (lam-pi 'c (type-type)
  (lam 'f (type-fun 'a 'c)
  (lam 'g (type-fun 'b 'c)
  (prim '() (type-fun (type-or 'a 'b) 'c)
        (lambda (env x) (if (eq? (car x) 'l)
                        (app (cdr (find-env 'f env)) (cdr x))
                        (app (cdr (find-env 'g env)) (cdr x)))))))))))
(new-form 
 (lambda (env t)
   (match t 
     [(type-or a b) (and (type? env a) (type? env b))]
     [_ #f]))
 (lambda (env x t)
   (match t
     [(type-or a b)
      (match x
        [(cons 'l y) (hasType? env y a)]
        [(cons 'r z) (hasType? env z b)])]
     [_ #f]))
 (lambda (env v arg x)
   (match x
    [(list 'l a) ('l   (subst env v arg a))]
    [(list 'r a) ('r   (subst env v arg a))]
    [_ x]))
 (lambda (x) x))

(define (type-nat) 'type-nat)
(new-form 
 (lambda (env t) (eqType? t 'type-nat))
 (lambda (env x t)
   (and (eqType? t 'type-nat) (integer? x) (>= x 0)))
 (lambda (env v arg x) x)
 (lambda (x) x))

(define (eqType? env t1 t2) (eq? t1 t2))
(define (eqVal?  env typ v1 v2) (eq? v1 v2))

(define id-nat (lam 'x (type-nat) 'x))
(hasType? '() id-nat (type-fun (type-nat) (type-nat)))
;(reduce '() (app id-nat 5))

(define id-forall (lam-pi 'x (type-type) (lam 'y 'x 'y)))
(hasType? '() id-forall (type-pi 'x (type-type) (type-fun 'x 'x)))
;(reduce '() (app (app id-forall (type-nat)) 5))

(define apps
  (lambda (fun . args)
    (foldl
     (lambda (arg acc) (app acc arg))
     fun
     args)))

(define and-intro-test (apps and-intro (type-nat) (type-nat) 2 4))
;(reduce '() and-intro-test)

(define and-elim-test (apps and-elim-fst (type-nat) (type-nat) and-intro-test))
;(reduce '() and-elim-test)

(define or-intro-test (apps or-intro-left (type-nat) (type-unit) 23))
(reduce '() or-intro-test)

(define or-elim-test (apps or-elim (type-nat) (type-unit) (type-nat)
                           (lam 'x (type-nat) 'x)
                           (lam 'y (type-unit) 15)
                           or-intro-test))
(reduce '() or-elim-test)

(define or-elim-test2 (apps or-elim (type-nat) (type-unit) (type-nat)
                           (lam 'x (type-nat) 'x)
                           (lam 'y (type-unit) 15)
                           (cons 'r '())))
(reduce '() or-elim-test2)


;; todo -- simplicial equality
;;todo -- any equality, simplicial types
;;todo -- example with bools