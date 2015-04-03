#lang racket
; HoTT MESS
; Homotopy Type Theory Mechanical Evaluator Specification and Simulator
; (c) Gershom Bazerman, 2015
; BSD(3) Licensed

(require racket/match)

; a value is a basic space if it is
; a collection of basepoints and a sequence of higher paths
; conceptually (Objects : Int or Inf, Paths : (Count, Level -> (Count, Int -> (Int,Int))
; a path is two functions, one going one way on values, one going the other...

; a type is a tag denoting a space and denoting a level

; a value is a point in a space if it is a pair (Int, Int) with the first tag the level and the second the index

; a space can also be a function. A  function is a type tag, a level, and a function Int -> (Int,Int)
; with the two indicies being the level in the target type and the index of the new value

; an application is just a pair of a function and an argument as before


; a value is judged to be a type if it
; is a tag which corresponds to a space _or_
; is a product of such tags either as a function or a pair _or_
; it is a tag and a mapping of such tags to values judged as types (as a function or as a pair)
; is a tag and a pair of values and the index, in their type, of the path between them (an equality type)

; value formers
(struct lam-pi (var vt body pathbody) #:transparent)
(struct app-n (fun lvl arg) #:transparent)
; primitives
(struct closure (typ body) #:transparent)
(struct trustme (typ body) #:transparent)

; type formers
(struct type-fun (dom codom) #:transparent)
; one basic type
(define type-unit 'type-unit)
(define unit-val  0)
; dependency
(struct type-pi (var dom codom) #:transparent)
(define type-type 'type) ;; inconsistent!
;paths
(struct type-eq (type v1 v2) #:transparent)

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
  [(_ (app-n (lam-pi var vt b pb) 0 arg))
   (if (hasType? cxt arg vt) (reduce cxt (b arg))
       (raise-arguments-error 'bad-type "bad type"
                              "cxt" cxt "arg" arg "vt" vt "app" (lam-pi var vt b pb)))]
  [(_ (app-n (lam-pi var vt b pb) lvl arg))
   (if (hasType? cxt arg vt) (reduce cxt (pb lvl arg))
       (raise-arguments-error 'bad-type "bad type"
                              "cxt" cxt "arg" arg "vt" vt "app" (lam-pi var vt b pb)))]
  ; To reduce an application of a closure to an argument, we produce a closure
  ; whose type is the application of the closure type to the argument type
  ; and whose body is the application of the closure body to the argument
  [(_ (app-n (closure ty b) lvl arg))
   (closure (app-type cxt (red-eval cxt ty) lvl arg) (lambda (cxt) (app-n (b cxt) lvl arg)))] 
  ; To reduce an application of anything else to an argument, we first reduce the thing itself
  ; and then attempt to again reduce the application of the result
  [(_ (app-n fun lvl arg)) (if (or (not fun) (symbol? fun))
                               (raise-arguments-error 'stuck "reduction stuck"
                                                "fun" fun "arg" arg)
                               (reduce cxt (app-n (reduce cxt fun) lvl arg)))]
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
(define/match (app-type cxt fun lvl arg)
  [(_ (type-fun a b)   0 _)
   (if (hasType? cxt arg a) b
       (raise-arguments-error 'bad-type "bad type applying in closure" "cxt" cxt "fun" fun "arg" arg))]
  [(_ (type-fun a b)   n (type-eq argeq _ _))
   (app-type cxt fun (- n 1) argeq)]
  [(_ (type-pi a at b) 0 _)
   (if (hasType? cxt arg a) (b arg)
       (raise-arguments-error 'bad-type "bad pi type applying in closure" "cxt" cxt "fun" fun "arg" arg))]
  [(_ (type-pi a at b) n (type-eq argeq _ _))
   (app-type cxt fun (- n 1) argeq)]
  [(_ _ _ _) (raise-arguments-error 'bad-type "can't apply type in closure (fun and arg don't match)" "cxt" cxt "fun" fun "lvl" lvl "arg" arg)])

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
    ; We know a value is a type if it is an equality at a type TODO
    [(type-eq vt a b)
     (and (type? cxt vt) (hasType? cxt a vt) (hasType? cxt b vt))]
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
    [((lam-pi vn vt body pb) (type-fun a b))
     (and (eqType? cxt vt a)
          (extend-cxt vn vt cxt (newvar newcxt) (hasType? newcxt (body newvar) b)))]
    ; To know that a term has type unit is to know that it is the unit value
    [(x 'type-unit) (equal? x unit-val)]
    ; To know that a lambda has type pi is to know that
    ; the domain of the function type is equal to the input type of the body and to know that
    ; in a context where the argument is assigned the proper domain type
    ; the body in turn has a type of the codomain of the function type, as viewed in the same context
    ; todo match pathbodies?
    [((lam-pi vn vt body pb) (type-pi _ a b))
     (and (eqType? cxt vt a)
          (extend-cxt vn vt cxt (newvar newcxt) 
                      (hasType? newcxt (body newvar) (reduce newcxt (b newvar)))))]
    ; To know that a term has type type is to know that the term may be judged a type
    [(x 'type) (type? cxt x)]
    ; To know that a value has type-eq is to know that
    ; there is some mechanism by which the value validates the equality
    [(x (type-eq vt a b))
     (isPath? cxt x vt a b)]
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
    ; To know that two types tagged as equalities are equal as types is to know that
    ; the types they equate are equal as types and
    ; their first values are equal at that type and
    ; their second values are equal at that type
    [((type-eq vt a b) (type-eq vt1 a1 b1))
     (and (eqType? cxt vt vt1)
          (eqVal? cxt vt a a1)
          (eqVal? cxt vt1 b b1))]
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
    ; TODO match path bodies?
    [((type-fun a b) (lam-pi x xt body pb) (lam-pi y yt body2 pb2))
     (and (eqType? cxt a xt) (eqType? cxt a yt)
          (extend-cxt x xt cxt (newv newcxt)
                      (eqVal? newcxt b (body newv) (body2 newv))))]
    ; To know two lambda terms are equal at a pi type is to know that
    ; their domains are equal as types to the domain of the function type and
    ; in a context where their domains are assigned the proper input type
    ; then their bodies are equal at the type of the codomain, as viewed in the same context
    ; TODO match path bodies?
    [((type-pi v a b) (lam-pi x xt body pb) (lam-pi y yt body2 pb2))
     (and (eqType? cxt a xt) (eqType? cxt a yt)
          (extend-cxt x xt cxt (newv newcxt)
                      (eqVal? newcxt (b newv) (body newv) (body2 newv))))]
    ; To know two values are equal at unit type
    ; requires knowing nothing else -- it is always known
    [('type-unit _ _) #t]
    ; To know two values are equal at a given equality type
    ; is _REALLY_ hard -- they must take equal points to equal points
    ; and also take equal paths to equal paths, etc.
    [((type-eq vt a b) x y)
     (eqPaths? cxt vt a b x y)]
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


(define isPath-judgments '())
(define (isPath? cxt typ path v1 v2)
  (for/or ([p isPath-judgments]) (p cxt typ path v1 v2)))

(define eqPaths-judgments '())
(define (eqPaths? cxt typ v1 v2 p1 p2)
  (for/or ([p eqPaths-judgments]) (p cxt typ v1 v2 p1 p2)))

(define (add-isPath isPath-judgment)
  (set! isPath-judgments (cons isPath-judgment isPath-judgments)))
(define (add-eqPath eqPaths-judgment)
  (set! eqPaths-judgments (cons eqPaths-judgment eqPaths-judgments)))

(define const-pb (lambda (lvl p) 'refl))

(define-syntax-rule (lam   (x t) body) (lam-pi  (quote x) t (lambda (x) body) const-pb))
(define-syntax-rule (pi    (x t) body) (lam-pi  (quote x) t (lambda (x) body) const-pb))
(define-syntax-rule (pi-ty (x t) body) (type-pi (quote x) t (lambda (x) body)))
(define-syntax-rule (close    t  body) (closure t body))

(define-syntax-rule (app f x) (app-n f 0 x))

(define apps
  (lambda (fun . args)
    (foldl (lambda (arg acc) (app acc arg)) fun args)))

(define refl (pi (a type-type) (pi (x a) (close (type-eq a x x) (lambda (cxt) 'refl)))))


(add-isPath
 (match-lambda**
  [(cxt typ 'refl v1 v2)
   (eqVal? cxt typ v1 v2)]
  [(_ _ _ _ _) #f]))

(add-eqPath
 (match-lambda**
  [(cxt typ v1 v2 'refl 'refl)
   #t]
  [(_ _ _ _ _ _) #f]))

; S1

(new-form 
 (lambda (cxt t) (eq? t 'type-s1))
 (lambda (cxt x t) (and (eq? t 'type-s1) (eq? x 'base-s1)))
 #f
 (lambda (cxt t x y) (and  (eq? t 'type-bool) (eq? x y))))
 
(add-isPath
 (match-lambda**
  [(cxt 'type-s1 'loop-s1 v1 v2)
   #t]
  [(_ _ _ _ _) #f]))

(add-eqPath
 (match-lambda**
  [(cxt 'type-s1 t1 t2 'loop 'loop)
   #t]
  [(_ _ _ _ _ _) #f]))


(add-isPath
 (match-lambda**
  [(cxt typ () v1 v2) #f]
  [(cxt typ (cons p ps) v1 v2)
   (and (isPath? cxt typ p v1 'any)
        (isPath? cxt typ ps 'any v2))]
  [(_ _ _ _ _) #f]))

(add-isPath
 (match-lambda**
  [(cxt typ (inv p) v1 v2) (isPath? cxt typ p v2 v1)]))

; eqPath for cons and inv...

; turns the path into a function and applies it... somehow.
(define/match (apply-path p x)
  [(()) x]
  [('refl _) x]
  [('loop-s1 _) x]
  [(cons p ps) (apply-path ps (apply-path p x))]
  )

(define equal-induct
  (pi (a type-type)
  (pi (m a)
  (pi (n a)
  (pi (m-eq-n (type-eq a m n))

  (pi (c (pi-ty (x a) (pi-ty (y a) (type-fun (type-eq a x y) type-type))))
  (lam (f (pi-ty (z a) (apps c z z 'refl)))
; ignores m-eq-n
 (close (apps c m n m-eq-n) (lambda (cxt) (app f m))))))))))

;(close (apps c m n m-eq-n) 
;         (lambda (cxt)
;           (let [refl-eq-m-eq-n xxx]
;             (apply-path (app-n (apps c m n) 1 (m-eq-n-eq-refl)) (app f m))))))))))))
; doesn't work, need to app c to (m,n,m-eq-n-eq-refl)

(define transport
  (pi (a type-type)
  (pi (p (pi-ty (v a) type-type))
  (pi (x a)
  (pi (y a)
  (lam (x-eq-y (type-eq a x y))
  (lam (px (app p x))
; ignores x-eq-y
;  (close (app p y) (lambda (cxt) px)))))))))
  (close (app p y)
  (lambda (cxt) (apply-path (app-n (red-eval cxt p) 1 (red-eval cxt x-eq-y)) px))))))))))


; define explicit path-compose, path-inv, list of paths

; x - x-eq-y -> y 
; |             |
; p             p
; |             |
; v             v
; p x - ? --> p y

; fill x = y --> p x = p y

(define fill
  (pi (a type-type)
  (pi (p (pi-ty (v a) type-type))
  (pi (x a)
  (pi (y a)
  (lam (x-eq-y (type-eq a x y))
  (close (type-eq type-type (app p x) (app p y))
  (lambda (cxt) (app-n (red-eval cxt p) 1 (red-eval cxt x-eq-y))))))))))

;(define/match (app-to-path cxt f p)
;  [(_ (lam-pi v vt body pb) _) (pb 0 p)]
;  [(_ _ _) (raise-arguments-error 'app-path-failure "can't apply that to a path"
 ;                                 "cxt" cxt "f" f "p" p)])

;(define/match (fill-path cxt path fam)
;  [(cxt 'refl f) 'refl]
;  [(cxt 'loop-s1 f) (app-path cxt (red-eval cxt fam) 'loop-s1)])

; body doesn't just produce a value, but can produce paths...

; do ap
; do apd

; coe is equal -> equiv
; ua is equiv -> equal

; TODO compute paths
    



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
(hasType? '() (apps id-forall type-unit unit-val) type-unit)

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



; a value is of a space at a level if it is
; an index into that space at that level (atomic)
; function value: a space paired with a second space of points, of the same quantity as the first (a zero function space) _or_
; a value in one space and a value in another space

; two types are equal if... (require path unless trivial)

; two values are equal at a type if... 

; well typed shapes don't go wrong

; to apply
