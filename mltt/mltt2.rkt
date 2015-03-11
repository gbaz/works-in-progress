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
(struct type-sig (var dom codom))
(define (type-type) 'type) ;; inconsistent!






(struct sigma  (val vt snd))
