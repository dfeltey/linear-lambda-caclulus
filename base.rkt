#lang racket

(require
  (prefix-in r: racket)
  (for-syntax
   racket/match
   racket/dict
   racket/set
   syntax/parse
   racket/syntax
   syntax/id-table
   syntax/transformer)
  racket/stxparam)

(define-syntax-parameter Env #f)

(begin-for-syntax
  ;; Weird things happen if these aren't prefab
  (struct type () #:prefab)
  (struct & type (left right) #:prefab)
  (struct ⊗ type (left right) #:prefab)
  (struct ⊕ type (left right) #:prefab)
  (struct -o type (left right) #:prefab)
  (struct -> type (left right) #:prefab)
  (struct MUnit type () #:prefab)
  (struct AUnit type () #:prefab)
  (struct Void type () #:prefab)
  (struct Num type () #:prefab)
  (struct TypeError type (reason) #:prefab)
  
  (define-syntax-class ltype
    #:literals (& ⊗ ⊕ MUnit AUnit Void Num -o ->)
    (pattern
     (& left:ltype right:ltype)
     #:attr type (& (attribute left.type) (attribute right.type)))
    (pattern
     (⊗ left:ltype right:ltype)
     #:attr type (⊗ (attribute left.type) (attribute right.type)))
    (pattern
     (⊕ left:ltype right:ltype)
     #:attr type (⊕ (attribute left.type) (attribute right.type)))
    (pattern
     (-o left:ltype right:ltype)
     #:attr type (-o (attribute left.type) (attribute right.type)))
    (pattern
     (-> left:ltype right:ltype)
     #:attr type (-> (attribute left.type) (attribute right.type)))
    (pattern MUnit #:attr type (MUnit))
    (pattern AUnit #:attr type (AUnit))
    (pattern Void #:attr type (Void))
    (pattern Num #:attr type (Num)))

  (struct env (delta uses non-linear-uses) #:transparent)
  
  (define ll-ann-key 'TEST #;(gensym))

  ;; annotations
  (struct annotation (type delta slack uses non-linear-uses) #:transparent)

  (define (add-annotation stx ann)
    (syntax-property stx ll-ann-key ann))

  (define (get-annotation stx)
    (syntax-property stx ll-ann-key))

  (define (assert-type stx expected-ty)
    (define ann 
      (syntax-parse stx
        [e:annotated-expr
         (attribute e.annotation)]
        [_ (raise-syntax-error #f "no type for expression" stx)]))
    (match ann
      [(annotation ty _ _ _ _)
       (cond
         [(not expected-ty) ann]
         [(equal? expected-ty ty) ann]
         [else
          (raise-syntax-error
           #f 
           (format "type mismatch\nexpected: ~a\ngiven: ~a\n" expected-ty ty)
           stx)])]
      [_
       (raise-syntax-error #f "no type for expression" stx)]))
  
  (define (make-annotated-variable-transformer var type key linear?)
    (make-set!-transformer
     (syntax-parser #:literals (r:set!)
       [x:id
        (match-define (env delta uses non-linear-uses) (syntax-parameter-value #'Env))
        (define ann
          (annotation type
                      (if linear? (set-remove delta key) delta)
                      #f
                      (if linear?
                          (hash-update uses key (λ (l) (cons #'x l)) null)
                          uses)
                      (if (and linear? (not (set-member? delta key)))
                          (set-add non-linear-uses key)
                          non-linear-uses)))
        (add-annotation var ann)]
       #;[(r:set! x:id e)
          #`(r:set! #,(add-annotation var (annotation type (make-use #'x))) e)]
       [(x:id e ...)
        #`(my-app x e ...)])))

  ;; uses
  (define (empty-uses) (make-immutable-free-id-table))
  (define (make-use id)
    (make-immutable-free-id-table (list (cons id (list id)))))
  (define (add-use u id)
    (free-id-table-update u id (λ (old) (cons id old)) null))
  (define (merge-uses u1 u2)
    (for/fold ([u u1])
              ([(var uses) (in-dict u2)])
      (free-id-table-update u var (λ (old) (append uses old)) null)))
  (define (remove-use u id)
    (free-id-table-remove u id))

  ;; syntax classes
  (define-syntax-class annotated-expr
    #:literals (let-values #%expression)
    (pattern
     (~and lv
           (let-values ()
             e:annotated-expr))
     #:when (not (get-annotation #'lv))
     #:attr annotation (attribute e.annotation)
     #:attr inner (attribute e.inner))
    (pattern
     (~and lv
           (#%expression e:annotated-expr))
     #:when (not (get-annotation #'lv))
     #:attr annotation (attribute e.annotation)
     #:attr inner (attribute e.inner))
    (pattern
     expr
     #:attr annotation (get-annotation #'expr)
     #:attr inner #'expr))
  )

;; Type Syntax
(define-syntax (define-type-syntax stx)
  (syntax-parse stx
    [(_ type-name:id)
     (define type-sym (syntax-e #'type-name))
     (define error-message (format "illegal use of type `~a`" type-sym))
     #`(begin
         (define-syntax (type-name stx)
           (raise-syntax-error 'type-name #,error-message)))]))

(define-type-syntax &)
;; ideally want better symbols for these ...
(define-type-syntax ⊗)
(define-type-syntax ⊕)
(define-type-syntax MUnit)
(define-type-syntax AUnit)
(define-type-syntax Void)
(define-type-syntax -o)
(define-type-syntax ->)
(define-type-syntax Num)

;; Annotation syntax
(define-syntax (: stx)
  (raise-syntax-error ': "illegal use of `:`"))

;; TODO: use a syntax parameter to send information down
;; and syntax properties to propogate it back up ...

;; expressions
(define-syntax (lambda stx)
  (syntax-parse stx
    #:literals (:)
    [(_ ([x:id : t:ltype]) body)
     (define/with-syntax temp (generate-temporary))
     (define key (gensym))
     (define var-type (attribute t.type))
     (define the-env
       (match (syntax-parameter-value #'Env)
         [(env delta uses nl-uses)
          (env (set-add delta key) uses nl-uses)]))
     (define body/ann-var
       #`(r:lambda (temp)
           (let-syntax ([x (make-annotated-variable-transformer #'temp #,var-type '#,key #t)])
             (syntax-parameterize ([Env #,the-env]) body))))
     (define exp-body/ann-var (local-expand body/ann-var 'expression null))
     (match-define (annotation body-type delta* slack uses nl-uses)
       (syntax-parse exp-body/ann-var #:literals (r:#%plain-lambda)
         [(r:#%plain-lambda (v) e:annotated-expr)
          (attribute e.annotation)]))
     (when (set-member? nl-uses key)
       (define var-uses (hash-ref uses key))
       (raise-syntax-error #f
                           "non-linear use of linear variable"
                           #'x
                           #f
                           var-uses))
     (unless (or slack (not (set-member? delta* key)))
       (raise-syntax-error #f
                           "linear variable unused"
                           stx
                           #'x
                           (list #'body)))
     (add-annotation
      exp-body/ann-var
      (annotation
       (-o var-type body-type)
       (set-remove delta* key)
       slack
       (hash-remove uses key)
       nl-uses))]))

(define-syntax (my-app stx)
  (syntax-parse stx
    [(_ e1 e2)
     (define e1-exp (local-expand #'e1 'expression null))
     (match-define (annotation e1-type delta-e1 slack-e1 uses-e1 nl-uses-e1)
       (syntax-parse e1-exp 
         [e:annotated-expr
          (attribute e.annotation)]))
     (match e1-type
       [(-o left right)
        (define new-env (env delta-e1 uses-e1 nl-uses-e1))
        (define e2-exp
          (local-expand #`(syntax-parameterize ([Env #,new-env]) e2) 'expression null))
        (match-define (annotation e2-type delta-e2 slack-e2 uses-e2 nl-uses-e2)
          (assert-type e2-exp left))
        (add-annotation
         #`(r:#%app #,e1-exp #,e2-exp)
         (annotation right delta-e2 (or slack-e1 slack-e2) uses-e2 nl-uses-e2))]
       [(-> left right)
        (define new-env (env (set) uses-e1 nl-uses-e1))
        (define e2-exp
          (local-expand #`(syntax-parameterize ([Env #,new-env]) e2) 'expression null))
        (match-define (annotation e2-type delta-e2 slack-e2 uses-e2 nl-uses-e2)
          (assert-type e2-exp left))
        (add-annotation
         #`(r:#%app #,e1-exp #,e2-exp)
         (annotation right delta-e1 (or slack-e1 slack-e2) uses-e2 nl-uses-e2))]
       [_ (raise-syntax-error
           #f
           (format "type mismatch\nexpected a function type\nrecieved: ~a\n" e1-type)
           stx
           #'e1)])]))

(define (:pair x y)
  (λ () (values x y)))
(define (extract p) (p))

(define-syntax (pair stx)
  (syntax-parse stx
    [(_ e1 e2)
     (define e1-exp (local-expand #'e1 'expression null))
     (match-define (annotation e1-type delta-e1 slack-e1 uses-e1 nl-uses-e1) (assert-type e1-exp #f))
     (define new-env (env delta-e1 uses-e1 nl-uses-e1))
     (define e2-exp
       (local-expand #`(syntax-parameterize ([Env #,new-env]) e2) 'expression null))
     (match-define (annotation e2-type delta-e2 slack-e2 uses-e2 nl-uses-e2) (assert-type e2-exp #f))
     (add-annotation
      #`(:pair #,e1-exp #,e2-exp)
      (annotation (⊗ e1-type e2-type) delta-e2 (or slack-e1 slack-e2) uses-e2 nl-uses-e2))]))

(define-syntax (let-pair stx)
  (syntax-parse stx #:literals (pair)
    [(_ ([(pair x:id y:id) e-pair]) e-body)
     (define e-pair-exp (local-expand #'e-pair 'expression null))
     (match-define (annotation pair-type delta-pair slack-pair uses-pair nl-uses-pair)
       (assert-type e-pair-exp #f))
     (match pair-type
       [(⊗ left right)
        (define/with-syntax temp-x (generate-temporary))
        (define/with-syntax temp-y (generate-temporary))
        (define key-x (gensym))
        (define key-y (gensym))
        (define new-env (env (set-add (set-add delta-pair key-x) key-y) uses-pair nl-uses-pair))
        (define body/ann-var
          #`(r:let-values ([(temp-x temp-y) (extract #,e-pair-exp)])
           (let-syntax ([x (make-annotated-variable-transformer #'temp-x #,left '#,key-x #t)]
                        [y (make-annotated-variable-transformer #'temp-y #,right '#,key-y #t)])
             (syntax-parameterize ([Env #,new-env]) e-body))))
        (define lp-exp (local-expand body/ann-var 'expression null))
        (match-define (annotation body-type delta-body slack-body uses-body nl-uses-body)
          (syntax-parse lp-exp
            #:literals (r:let-values)
            [(r:let-values e-bindings e:annotated-expr)
             (attribute e.annotation)]))
        (when (set-member? nl-uses-body key-x)
          (define var-uses (hash-ref uses-body key-x))
          (raise-syntax-error #f
                              "non-linear use of linear variable"
                              #'x
                              #f
                              var-uses))
        (when (set-member? nl-uses-body key-y)
          (define var-uses (hash-ref uses-body key-y))
          (raise-syntax-error #f
                              "non-linear use of linear variable"
                              #'y
                              #f
                              var-uses))
        (unless (or slack-body (not (set-member? delta-body key-x)))
          (raise-syntax-error #f
                              "linear variable unused"
                              stx
                              #'x
                              (list #'e-body)))
        (unless (or slack-body (not (set-member? delta-body key-y)))
          (raise-syntax-error #f
                              "linear variable unused"
                              stx
                              #'y
                              (list #'e-body)))
        (add-annotation
         lp-exp
         (annotation
          body-type
          (set-remove (set-remove delta-body key-x) key-y)
          (or slack-pair slack-body)
          (hash-remove (hash-remove uses-body key-x) key-y)
          nl-uses-body))]
       [_
        (raise-syntax-error
         #f
           (format "type mismatch\nexpected a ⊗ type\nrecieved: ~a\n" pair-type)
           stx
           #'e-pair)])]))
     
     

(define-syntax (#%datum stx)
  (syntax-parse stx
    [(_ . n:number)
     (match-define (env delta uses nl-uses) (syntax-parameter-value #'Env))
     (add-annotation #'(r:#%datum . n) (annotation (Num) delta #f uses nl-uses))]))

(define-syntax (define/type stx)
  (syntax-parse stx
    [(_ x:id type:ltype e)
     #`(define-syntax x
         (make-set!-transformer
          (syntax-parser
            #:literals (r:set!)
            [x:id
             (match-define (env delta uses nl-uses) (syntax-parameter-value #'Env))
             (define ann
               (annotation #,(attribute type.type)
                           delta
                           #f
                           uses
                           nl-uses))
             (add-annotation #'e ann)]
            [(x:id y (... ...))
             #`(my-app x y (... ...))])))]))

(r:define curried:+ (r:lambda (x) (r:lambda (y) (r:+ x y))))
(define/type + (-o Num (-o Num Num)) curried:+)
(r:define curried:- (r:lambda (x) (r:lambda (y) (r:- x y))))
(define/type - (-o Num (-o Num Num)) curried:-)
(define/type sqr (-> Num Num) r:sqr)

(define-syntax (mod-beg stx)
  (syntax-parse stx
    [(_ e ...)
     (define the-env (env (set) (hash) (set)))
     #`(r:#%module-begin
        (syntax-parameterize ([Env #,the-env]) e) ...)]))

(define-syntax (run stx)
  (syntax-parse stx
    [(_ body ...)
     (define the-env (env (set) (hash) (set)))
     #`(syntax-parameterize ([Env #,the-env]) body ...)]))

(provide
 (rename-out [mod-beg #%module-begin]
             [my-app #%app]
             [lambda λ])
 Num
 ⊕ ⊗ -o ->
 :
 lambda
 pair
 let-pair
 #%datum
 +
 -
 sqr
 (except-out (all-from-out racket) #%app #%module-begin λ #%top-interaction))