#lang racket
(require racket/match)

; value formers
(struct lam (var vt body))
(struct app (fun arg))
; primitives
(struct closure (env typ body))
(define (prim typ body) (closure '() typ body))
; dependency
(struct lam-pi (var vt body))

; type formers
(struct type-fun (dom codom))
; one basic type
(define (type-unit) 'type-unit)
; dependency
(struct type-pi  (var dom codom))
(define (type-type) 'type) ;; inconsistent!

(define (cons-env nm typ env)
  (cons (cons nm typ) env))

(define (find-env nm env)
  (match (assoc nm env)
    [(cons a b) b]
    [_ #f]))

(define (fresh-var nm env)
  (if (assoc nm env) (fresh-var (string-append (symbol->string nm) "'")) nm))

(define (type? env t) 
  (match t
    [(type-fun a b) (and (type? env a) (type? env b))]
    [(var vname) #:when (and (symbol? vname) (type? env (find-env vname env))) #t]
    ['type-unit #t]
    [(type-pi var a b) (and (type? env a)
                            (let* ([freshname (fresh-var var env)]
                                   [newenv (cons-env freshname a env)])
                                   (type? newenv (b freshname))))]
    ['type #t]
    [_ (type?-additional env t)]
    ))

; todo closures
(define (hasType? env x1 t)
  (let ([x (reduce env x1)])
    (or (and (symbol? x) (eqType? env t (find-env x env)))
        (match t
          [(type-fun a b)
           (match x
             [(lam vn vt body)
              (and (eqType? env vt a)
                   (let* ([freshname (fresh-var vn env)]
                          [newenv (cons-env freshname vt env)])
                     (hasType? newenv (body freshname) b)))])]
          [(var vname) #:when (and (symbol? vname) (find-env vname env))
                       (hasType? env x (find-env vname env))]
          ['type-unit (null? x)]
          [(type-pi fvar a b)
           (match x
             [(lam-pi vn vt body)
              (and (eqType? env vt a)
                   (let* ([freshname (fresh-var vn env)]
                          [newenv (cons-env freshname vt env)])
                     (hasType? newenv (body freshname) (reduce newenv (b freshname)))))])]
          ['type (type? env x)]
          [_ (hasType?-additional env x t)]))))
  
(define (reduce env body)
  (match body
    ; [(var vname) #:when (symbol? vname) (match (find-env vname env) [#f body] [x x])]
    [(app (lam     var     vt  b) arg) (reduce env (b (reduce env arg)))]
    [(app (lam-pi  var     vt  b) arg) (reduce env (b (reduce env arg)))]
    [(app (closure primEnv typ b) arg) (reduce env (b primEnv (reduce env arg)))]
    [(app fun arg) (if (symbol? fun)
                       (match (find-env fun env) [#f body] [f (reduce env (app f arg))])
                       (reduce env (app (reduce env fun) arg)))]
    [_ body] ;;(reduce-additional body)]
    ))

(define (eqType? env t1 t2) (eq? t1 t2))
(define (eqVal?  env typ v1 v2) (eq? v1 v2))

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

(displayln "id-unit: is type, has type")
(define id-unit (lam 'x (type-unit) (lambda (x) x)))
(define id-unit-type (type-fun (type-unit) (type-unit)))
(type?    '() id-unit-type)
(hasType? '() id-unit  id-unit-type)

(displayln "id-forall: is type, has type")
(define id-forall (lam-pi 'x (type-type) (lambda (x) (lam 'y x (lambda (y) y)))))
(define id-forall-type (type-pi 'tau (type-type) (lambda (tau) (type-fun tau tau))))
(type?    '() id-forall-type)
(hasType? '() id-forall id-forall-type)

(define apps
  (lambda (fun . args)
    (foldl (lambda (arg acc) (app acc arg)) fun args)))

(displayln "id-forall: application typechecks")
(hasType? '() (app id-forall (type-unit)) id-unit-type)
(hasType? '() (apps id-forall (type-unit) '()) (type-unit))


(displayln "k-comb: is type, has type")
(define k-comb (lam-pi 'a (type-type) (lambda (a) 
                (lam 'x a (lambda (x)
                  (lam-pi 'b (type-type) (lambda (b)
                    (lam 'y b (lambda (y)
                      x)))))))))
(define k-comb-type (type-pi 'a (type-type) (lambda (a)
                     (type-fun a
                       (type-pi 'b (type-type) (lambda (b)
                         (type-fun b a)))))))
(type?    '() k-comb-type)
(hasType? '() k-comb k-comb-type)

(struct sigma  (val vt snd))
(struct type-sig (var dom codom))

; todo macro for new lambda form

;     [(type-sig val a b) (and (type? env a) (type? (cons-env val a #f env) b))]
;      [(type-sig fvar a b)
;         (match x
;           [(sigma y yt z) (and (eqType? env yt a) (hasType? y a)
;                                (hasType? (cons-env fvar a y) (reduce b)))])]

;todo typeeq should use beta-eq