#lang racket
; HoTT MESS
; Homotopy Type Theory Mechanical Evaluator Specification and Simulator
; (c) Gershom Bazerman, 2015
; BSD(3) Licensed

(require racket/match)

; value formers
(struct lam-pi (var vt body) #:transparent)
(struct app (fun arg) #:transparent)
; primitives
(struct closure (typ body) #:transparent)
(struct trustme (typ body) #:transparent)

; type formers
(struct type-fun (dom codom) #:transparent)
; one basic type
(define type-unit 'type-unit)
; dependency
(struct type-pi (var dom codom) #:transparent)
(define type-type 'type) ;; inconsistent!

; contexts
(define (find-cxt nm cxt)
  (match (assoc nm cxt) [(cons a b) b] [_ #f]))

(define (fresh-var nm cxt)
  (if (assoc nm cxt) (fresh-var (string->symbol (string-append (symbol->string nm) "'")) cxt) nm))

(define-syntax-rule (extend-cxt var vt cxt (newvar newcxt) body)
  (let* ([newvar (fresh-var var cxt)]
         [newcxt (cons (cons newvar vt) cxt)])
    body))
          
; a reduction of a value in a context creates a term where "app" is not in the head position.
; this is "weak head normal form" call-by-name reduction
; we call a term in such a form "reduced" or simply a "value"
(define/match (reduce cxt body)
  ; To reduce an application of a function to an argument
  ; we confirm that the argument is compatible with the function
  ; and we produce the application of the function to the argument
  ; (if we omit the type check, we get nuprl semantics) 
  [(_ (app (lam-pi var vt  b) arg))   
   (if (hasType? cxt arg vt) (reduce cxt (b arg)) 
       (raise-arguments-error 'bad-type "bad type"
                              "cxt" cxt "arg" arg "vt" vt "app" (lam-pi var vt b)))]
  ; To reduce an application of a closure to an argument, we produce a closure
  ; whose type is the application of the closure type to the argument type
  ; and whose body is the application of the closure body to the argument
  [(_ (app (closure ty b) arg))
   (closure (app-type cxt (red-eval cxt ty) arg) (lambda (cxt) (app (b cxt) arg)))] 
  ; To reduce an application of anything else to an argument, we first reduce the thing itself
  ; and then attempt to again reduce the application of the result
  [(_ (app fun arg)) (if (or (not fun) (symbol? fun))
                         (raise-arguments-error 'stuck "reduction stuck"
                                                "fun" fun "arg" arg)
                         (reduce cxt (app (reduce cxt fun) arg)))]
  [(_ _) body])

; A red-eval of a term in a context creates a term where neither "app" nor "closure" are in the head position
; we call a term in such a form "evaluated" (or also, where evident, a "value").
(define (red-eval cxt x)
  (match (reduce cxt x)
    ; To red-eval a closure, we red-eval the application of the bbody of the closure to the context
    [(closure typ b) (red-eval cxt (b cxt))]
    [v v]))

; An application of a type to a term confirms the term is compatible with the type
; and if so, removes provides the new type that is the result of applying a term
; with the type to a term with the type of the argument
(define/match (app-type cxt fun arg)
  [(_ (type-fun a b) _)
   (if (hasType? cxt arg a) b
       (raise-arguments-error 'bad-type "bad type applying in closure" "cxt" cxt "fun" fun "arg" arg))]
  [(_ (type-pi a at b) _)
   (if (hasType? cxt arg a) (b arg)
       (raise-arguments-error 'bad-type "bad pi type applying in closure" "cxt" cxt "fun" fun "arg" arg))]
  [(_ _ _) (raise-arguments-error 'bad-type "can't apply non-function type in closure" "cxt" cxt "fun" fun "arg" arg)])

; In all the following, judgment may be read as "verification"
; and "to judge" may be read as "to verify," "to know" or "two confirm"

; We may judge that an evaluated term is a type by the following rules
(define (type? cxt t) 
  (match (red-eval cxt t)
    ; We know a value is a type if we know that it is tagged type-fun
    ; and furthermore we know that its domain is a type and its codomain is a type
    [(type-fun a b) (and (type? cxt a) (type? cxt b))]
    ; We know a value is a type if it has the symbol 'type-unit
    ['type-unit #t]
    ; We know a value is a type in a context if it is a symbol and that context assigns it a type of type
    [(? symbol? vname) #:when (eq? type-type (find-cxt vname cxt)) #t]
    ; We know a value is a type if we know that it is tagged type-pi
    ; and furthermore we know that its domain is a type and in a context where
    ; its domain is assigned the proper type, its body can send the domain to a type.
    [(type-pi var a b)
     (and (type? cxt a) (extend-cxt var a cxt (newvar newcxt) (type? newcxt (b newvar))))]
    ; We know a value is a type if it has the symbol 'type
    ['type #t]
    ; Or, we know a value is a type if any other rules let us make such a judgment
    [t1 (type?-additional cxt t1)]
    ))

; We may judge that a reduced value has an evaluated type by the following rules
(define (hasType? cxt x1 t1)
  (match* ((reduce cxt x1) (red-eval cxt t1))
    ; To know a closure is of a type is to know that the type of the closure is equal to the desired type
    [((closure typ b) t) (eqType? cxt typ t)]
    ; To know a primitive is of a type is to know the type claimed by the primitive is equal to the desired type
    [((trustme typ b) t) (eqType? cxt typ t)]
    ; To know that a symbol has a type in a context is to know that the context assigns the symbol a type equal to the desired type
    [((? symbol? x) t) #:when (eqType? cxt t (find-cxt x cxt)) #t]
    ; To know that a lambda has type function is to know that
    ; the domain of the function type is equal to the input type of the body and to know that
    ; in a context where the argument is assigned the proper domain type
    ; the body in turn has a type of the codomain of the function type
    [((lam-pi vn vt body) (type-fun a b))
     (and (eqType? cxt vt a)
          (extend-cxt vn vt cxt (newvar newcxt) (hasType? newcxt (body newvar) b)))]
    ; To know that a term has type unit is to know that it is the unit value
    [(x 'type-unit) (null? x)]
    ; To know that a lambda has type pi is to know that
    ; the domain of the function type is equal to the input type of the body and to know that
    ; in a context where the argument is assigned the proper domain type
    ; the body in turn has a type of the codomain of the function type, as viewed in the same context
    [((lam-pi vn vt body) (type-pi _ a b))
     (and (eqType? cxt vt a)
          (extend-cxt vn vt cxt (newvar newcxt) 
                      (hasType? newcxt (body newvar) (reduce newcxt (b newvar)))))]
    ; To know that a term has type type is to know that the term may be judged a type
    [(x 'type) (type? cxt x)]
    ; Or, to know that a term has any other type is to follow any additional rules
    ; on how we may judge the types of terms
    [(x t) (hasType?-additional cxt x t)]))

; We may judge that two evaluated values are equal as types by the following rules
(define (eqType? cxt t1 t2)
  (match* ((red-eval cxt t1) (red-eval cxt t2))
    ; To know two types tagged type-fun are equal is to know that
    ; they have terms equal as types in their domains and
    ; they have terms equal as types in their codomains
    [((type-fun a b) (type-fun a1 b1))
     (and (eqType? cxt a a1) (eqType? cxt b b1))]
    ; To know two types tagged type-pi are equal is to know that
    ; they have terms equal as types in their domains and
    ; in a context where their arguments are assigned the proper domain type
    ; then their codomains also equal as types
    [((type-pi v a b) (type-pi v1 a1 b1))
     (and (eqType? cxt a a1)
          (extend-cxt v a cxt (newvar newcxt) 
                      (eqType? newcxt (b newvar) (b1 newvar))))]
    ; To know two symbols are equal as types is to know that they are the same symbol
    [((? symbol? vname) (? symbol? vname1)) (eq? vname vname1)]
    ; Or to know any other two values are equal as types is to follow any
    ; additional rules on how we may judge the equality of terms as types
    [(a b) (and a b (or (eqType?-additional cxt a b)
                        (begin (printf "not equal\n ~a\n ~a\n cxt: ~a\n" a b cxt) #f)))]))

; We may judge that two evaluated values are equal at an evaluated type types by the following rules
(define (eqVal? cxt typ v1 v2)
  (match* ((red-eval cxt typ) (red-eval cxt v1) (red-eval cxt v2))
    ; To know two lambda terms are equal at a function type is to know that
    ; their domains are equal as types to the domain of the function type and
    ; in a context where their domains are assigned the proper input type
    ; then their bodies are equal at the type of the codomain
    [((type-fun a b) (lam-pi x xt body) (lam-pi y yt body2))
     (and (eqType? cxt a xt) (eqType? cxt a yt)
          (extend-cxt x xt cxt (newv newcxt)
                      (eqVal? newcxt b (body newv) (body2 newv))))]
    ; To know two lambda terms are equal at a pi type is to know that
    ; their domains are equal as types to the domain of the function type and
    ; in a context where their domains are assigned the proper input type
    ; then their bodies are equal at the type of the codomain, as viewed in the same context
    [((type-pi v a b) (lam-pi x xt body) (lam-pi y yt body2))
     (and (eqType? cxt a xt) (eqType? cxt a yt)
          (extend-cxt x xt cxt (newv newcxt)
                      (eqVal? newcxt (b newv) (body newv) (body2 newv))))]
    ; To know two values are equal at unit type
    ; requires knowing nothing else -- it is always known
    [('type-unit _ _) #t]
    ; To know two values are equal at type type is to know that they are equal as types
    [('type a b) (eqType? cxt a b)]
    ; To know two symbols are equal at any type is to know that they are equal as symbols
    [(_ (? symbol? x) (? symbol? y)) #:when (eq? x y) #t]
    ; To know two primitives are equal at any type is to know their types are equal and know that
    ; their bodies are equal by primitive recursive comparison
    [(_ (trustme t v) (trustme t1 v1)) (and (eqType? cxt t t1) (equal? v v1))] ;if all else fails use primitive equality
    ; Or to know any other two values are equal at any other type is to follow any
    ; additional rules on how we may judge the equality of terms at types
    [(rtyp x y) (eqVal?-additional cxt rtyp x y)]))

(define type-judgments '())
(define (type?-additional cxt t)
  (for/or ([p type-judgments]) (p cxt t)))

(define hasType-judgments '())
(define (hasType?-additional cxt x t)
  (for/or ([p hasType-judgments]) (p cxt x t)))

(define eqType-judgments '())
(define (eqType?-additional cxt t1 t2)
  (for/or ([p eqType-judgments]) (p cxt t1 t2)))

(define eqVal-judgments '())
(define (eqVal?-additional cxt typ v1 v2)
  (for/or ([p eqVal-judgments]) (p cxt typ v1 v2)))

(define apps
  (lambda (fun . args)
    (foldl (lambda (arg acc) (app acc arg)) fun args)))

(define-syntax-rule (lam   (x t) body) (lam-pi  (quote x) t (lambda (x) body)))
(define-syntax-rule (pi    (x t) body) (lam-pi  (quote x) t (lambda (x) body)))
(define-syntax-rule (pi-ty (x t) body) (type-pi (quote x) t (lambda (x) body)))
(define-syntax-rule (close    t  body) (closure t body))

(displayln "id-unit: is type, has type")
(define id-unit (lam (x type-unit) x))
; (define id-unit (lam 'x type-unit (lambda (x) x)))
(define id-unit-type (type-fun type-unit type-unit))
(type?    '() id-unit-type)
(hasType? '() id-unit  id-unit-type)

(displayln "id-forall: is type, has type")
(define id-forall (pi (t type-type) (lam (x t) x)))
; (define id-forall (lam 'x type-type (lambda (x) (lam 'y x (lambda (y) y)))))
(define id-forall-type (pi-ty (tau type-type) (type-fun tau tau)))
; (define id-forall-type (type-pi 'tau type-type (lambda (tau) (type-fun tau tau))))
(type?    '() id-forall-type)
(hasType? '() id-forall id-forall-type)

(displayln "id-forall: application typechecks")
(hasType? '() (app id-forall type-unit) id-unit-type)
(hasType? '() (apps id-forall type-unit '()) type-unit)

(displayln "k-comb: is type, has type")
(define k-comb 
  (pi (a type-type) (lam (x a) (pi (b type-type) (lam (y b) x)))))
(define k-comb-type
  (pi-ty (a type-type) (type-fun a (pi-ty (b type-type) (type-fun b a)))))

(type?    '() k-comb-type)
(hasType? '() k-comb k-comb-type)

(displayln "checking rejection of bad signatures")
(hasType? '() k-comb id-forall-type)
(hasType? '() id-forall id-unit-type)

; To introduce a new type is to
; extend the ways to know a value is a type
; give a way to know a value has that type
; extend the ways to know two values are equal as types
; give a way to know two values are equal at that type

(define (new-form type-judgment hasType-judgment eqType-judgment eqVal-judgment)
  (cond [type-judgment    (set! type-judgments    (cons type-judgment    type-judgments))])
  (cond [hasType-judgment (set! hasType-judgments (cons hasType-judgment hasType-judgments))])
  (cond [eqType-judgment  (set! eqType-judgments  (cons eqType-judgment  eqType-judgments))])
  (cond [eqVal-judgment   (set! eqVal-judgments   (cons eqVal-judgment   eqVal-judgments))])
  )

; a value is a space if it is
; a collection of basepoints and a sequence of higher paths

; a value is judged to be a type if it
; is a tag which corresponds to a space _or_
; is a product of such tags either as a function or a pair _or_
; it is a tag and a mapping of such tags to values judged as types (as a function or as a pair)
; is a tag and a pair of values and the index, in their type, of the path between them (an equality type)

; a value is of a space at a level if it is
; an index into that space at that level (atomic)
; function value: a space paired with a second space of points, of the same quantity as the first (a zero function space) _or_
; a value in one space and a value in another space

; two types are equal if... (require path unless trivial)

; two values are equal at a type if... 

; well typed shapes don't go wrong

; to apply
