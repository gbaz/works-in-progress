#lang racket
(require racket/match)

; value formers
(struct lam (var vt body))
(struct app (fun arg))
(struct error (errstring))
; primitives
(struct closure (typ body))
; dependency
(struct lam-pi (var vt body))

; type formers
(struct type-fun (dom codom))
; one basic type
(define type-unit 'type-unit)
; dependency
(struct type-pi (var dom codom))
(define type-type 'type) ;; inconsistent!

(define (find-env nm env)
  (match (assoc nm env) [(cons a b) b] [_ #f]))

(define (cons-env nm typ env)
  (cons (cons nm typ) env))

(define (fresh-var nm env)
  (if (assoc nm env) (fresh-var (string->symbol (string-append (symbol->string nm) "'")) env) nm))

(define-syntax-rule (extend-env var vt env (newvar newenv) body)
  (let* ([newvar (fresh-var var env)]
         [newenv (cons-env newvar vt env)])
    body))

(define (type? env t) 
  (match t
    [(type-fun a b) (and (type? env a) (type? env b))]
    [(var vname) #:when (and (symbol? vname) (type? env (find-env vname env))) #t]
    ['type-unit #t]
    [(type-pi var a b)
     (and (type? env a) (extend-env var a env (newvar newenv) (type? newenv (b newvar))))]
    ['type #t]
    [_ (type?-additional env t)]
    ))

(define (hasType? env x1 t)
  (let ([x (reduce env x1)])
    (or (match x 
          [(closure typ body) (eqType? env typ t)]
          [(var vname) (and (symbol? vname) (eqType? env t (find-env x env)))]
          )
        (match t
          [(type-fun a b)
           (match x
             [(lam vn vt body)
              (and (eqType? env vt a)
                   (extend-env vn vt env (newvar newenv) (hasType? newenv (body newvar) b)))]
             [_ #f])]
          [(var vname) #:when (and (symbol? vname) (find-env vname env))
           (hasType? env x (find-env vname env))]
          ['type-unit (null? x)]
          [(type-pi fvar a b)
           (match x
             [(lam-pi vn vt body)
              (and (eqType? env vt a)
                   (extend-env vn vt env (newvar newenv) 
                     (hasType? newenv (body newvar) (reduce newenv (b newvar)))))]
             [_ #f])]
          ['type (type? env x)]
          [_ (hasType?-additional env x t)]))))
  
(define (reduce env body)
  (match body
    [(app (lam    var vt  b) arg) (let ([redarg (reduce env arg)]
                                        [redtyp (reduce env vt)])
                                    (if (hasType? env redarg redtyp) (reduce env (b redarg))
                                        (raise-arguments-error 'bad-type "bad type" "env" env "redarg" redarg "vt" vt)))]
    [(app (lam-pi var vt  b) arg) (let ([redarg (reduce env arg)])
                                    (if (hasType? env redarg vt) (reduce env (b redarg))
                                        (raise-arguments-error 'bad-pi "bad pi" "env" env "redarg" redarg "vt" vt)))]
    [(app (error s) arg) (error s)]
    [(app fun arg) (if (or (not fun) (symbol? fun))
                       (raise-arguments-error 'stuck "reduction stuck" "app" app "fun" fun "arg" arg)
                       (reduce env (app (reduce env fun) arg)))]
    [(closure typ b) (reduce env (b))]    
    [_ body]
    ))

(define (eqType? env t1 t2)
  (let ([t1v (reduce env t1)]
        [t2v (reduce env t2)])
    (match (cons t1v t2v)
      [(cons (type-fun a b) (type-fun a1 b1))
       (and (eqType? env a a1) (eqType? env b b1))]
      [(cons (type-pi v a b) (type-pi v1 a1 b1))
       (and (eqType? env a a1)
            (extend-env v a env (newvar newenv) 
               (eqType? newenv (b newvar) (b1 newvar))))]
      [(cons (var vname) (var vname1)) #:when (and (symbol? vname) (symbol? vname1))
         (eq? vname vname1)]
      [(cons '() '()) #t]
      [_ #f]
      )))

(define (eqVal? env typ v1 v2)
  (let ([v1v (reduce env v1)]
        [v2v (reduce env v2)])
    (match* (typ v1v v2v)
      [((type-fun a b) (lam x xt body) (lam y yt body2)) ;verify a = xt = yt
       (extend-env x xt env (newv newenv)
                   (eqVal? newenv b (body newv) (body2 newv)))]
      [((type-pi v a b) (lam-pi x xt body) (lam-pi y yt body2)) ;verify a = xt = yt
       (extend-env x xt env (newv newenv)
                   (eqVal? newenv (b newv) (body newv) (body2 newv)))]
      [('type-unit '() '()) #t]
      [('type-type a b) (eqType? env a b)]
      [('type-bool x y) (eq? x y)] ; todo pull this out, make equality extensible
      [(_ _ _) (raise-arguments-error 'not-eq "no equality at type" "env" env "type" typ "v1" v1v "v2" v2v)]
      )))

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

(define apps
  (lambda (fun . args)
    (foldl (lambda (arg acc) (app acc arg)) fun args)))

(define-syntax-rule (tlam  (x t) body) (lam     (quote x) t (lambda (x) body)))
(define-syntax-rule (pi    (x t) body) (lam-pi  (quote x) t (lambda (x) body)))
(define-syntax-rule (pi-ty (x t) body) (type-pi (quote x) t (lambda (x) body)))
(define-syntax-rule (close   t body) (closure t (lambda () body)))

(displayln "id-unit: is type, has type")
(define id-unit (tlam (x type-unit) x))
; (define id-unit (lam 'x type-unit (lambda (x) x)))
(define id-unit-type (type-fun type-unit type-unit))
(type?    '() id-unit-type)
(hasType? '() id-unit  id-unit-type)

(displayln "id-forall: is type, has type")
(define id-forall (pi (t type-type) (tlam (x t) x)))
; (define id-forall (lam-pi 'x type-type (lambda (x) (lam 'y x (lambda (y) y)))))
(define id-forall-type (pi-ty (tau type-type) (type-fun tau tau)))
; (define id-forall-type (type-pi 'tau type-type (lambda (tau) (type-fun tau tau))))
(type?    '() id-forall-type)
(hasType? '() id-forall id-forall-type)

(displayln "id-forall: application typechecks")
(hasType? '() (app id-forall type-unit) id-unit-type)
(hasType? '() (apps id-forall type-unit '()) type-unit)

(displayln "k-comb: is type, has type")
(define k-comb 
  (pi (a type-type) (tlam (x a) (pi (b type-type) (tlam (y b) x)))))
(define k-comb-type
  (pi-ty (a type-type) (type-fun a (pi-ty (b type-type) (type-fun b a)))))

(type?    '() k-comb-type)
(hasType? '() k-comb k-comb-type)

(displayln "checking rejection of bad signatures")
(hasType? '() k-comb id-forall-type)
(hasType? '() id-forall id-unit-type)

(define (new-form type-judgment hasType-judgment)
  (set! type-judgments (cons type-judgment type-judgments))
  (set! hasType-judgments (cons hasType-judgment hasType-judgments)))

; adding bool
(define type-bool 'type-bool)
(new-form 
 (lambda (env t) (eq? t 'type-bool))
 (lambda (env x t) (and (eq? t 'type-bool) (boolean? x)))
 )

; todo dependify bool-elim
(define bool-elim
  (pi (a type-type) (tlam (b type-bool) (tlam (x a) (tlam (y a) (close a (if b x y)))))))

(define bool-induct
  (pi (p (pi-ty (b type-bool) type-type))
      (tlam (x (app p #t))
            (tlam (y (app p #f))
                  (pi (bl type-bool)
                      (close (app p bl) (if bl x y)))))))

(displayln "functions on bool")
(define not-bool (tlam (x type-bool) (apps bool-elim type-bool x #f #t)))
(reduce '() (app not-bool #t))
(reduce '() (app not-bool #f))

(struct type-eq (type v1 v2))
(struct val-eq (v1 v2))
(new-form
 (lambda (env t) (match t [(type-eq type v1 v2) 
                           (and (hasType? env v1 type)
                                (hasType? env v2 type))] 
                   [_ #f])) 
 (lambda (env x t)
   (match t
     [(type-eq type v1 v2)
      (eqVal? env type v1 v2)]; we ignore x, admit reflection.
     [_ #f]))
 ) 

(displayln "playing with equality")

(define not-not-bool (tlam (x type-bool) (app not-bool (app not-bool x))))
(define id-bool (tlam (x type-bool) x))

(define not-not-is-id-equality (pi (x type-bool) (type-eq type-bool (app id-bool x) (app not-not-bool x))))

;(define (not-not-is-id-equality x) (type-eq type-bool (app id-bool x) (app not-not-bool x)))
; TODO FIX

(hasType? '() 'refl (app not-not-is-id-equality #t))

(define not-not-is-id-type (pi-ty (x type-bool) (app not-not-is-id-equality x)))
(type? '() not-not-is-id-type)


;; don't work, why? what's up with bool-induct?
(define not-not-is-id (pi (x type-bool) (apps bool-induct not-not-is-id-equality 'refl 'refl x)))
(hasType? '() not-not-is-id not-not-is-id-type)

; (hasType? '() 'refl (type-eq (type-fun type-bool type-bool) id-bool not-not-bool))


(struct sigma  (val vt snd))
(struct type-sig (var dom codom))

; todo macro for new lambda form

;     [(type-sig val a b) (and (type? env a) (type? (cons-env val a #f env) b))]
;      [(type-sig fvar a b)
;         (match x
;           [(sigma y yt z) (and (eqType? env yt a) (hasType? y a)
;                                (hasType? (cons-env fvar a y) (reduce b)))])]

;todo typeeq should use beta-eq