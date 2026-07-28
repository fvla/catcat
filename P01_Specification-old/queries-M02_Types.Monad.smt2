; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :produce-unsat-cores true)
(set-option :model true)
(set-option :smt.case_split 3)
(set-option :smt.relevancy 2)
(set-option :rewriter.enable_der false)
(set-option :rewriter.sort_disjunctions false)
(set-option :pi.decompose_patterns false)
(set-option :smt.arith.solver 6)
(set-option :smt.random-seed 0)


(declare-sort FString)
(declare-fun FString_constr_id (FString) Int)

(declare-sort Term)
(declare-datatypes () ((Universe 
(Univ (ulevel Int)))))
(define-fun imax ((i Int) (j Int)) Int 
(ite (<= i 0) j 
(ite (<= j 0) i 
(ite (<= i j) j i)))) 
(define-fun U_zero () Universe (Univ 0))
(define-fun U_succ ((u Universe)) Universe
(Univ (+ (ulevel u) 1)))
(declare-fun U_max (Universe Universe) Universe) 
(assert (forall ((u1 Universe) (u2 Universe)) 
(! (= (U_max u1 u2)
(Univ (imax (ulevel u1) (ulevel u2))))
:pattern ((U_max u1 u2)))))
(assert (forall ((u Universe)) (>= (ulevel u) 0)))
(declare-fun U_unif (Int) Universe)
(declare-fun U_unknown () Universe)
(declare-fun Term_constr_id (Term) Int)
(declare-sort Dummy_sort)
(declare-fun Dummy_value () Dummy_sort)
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreType (Term) Term)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool
(HasTypeFuel MaxIFuel x t))
(declare-fun IsTotFun (Term) Bool)

                ;;fuel irrelevance
(assert (forall ((f Fuel) (x Term) (t Term))
(! (= (HasTypeFuel (SFuel f) x t)
(HasTypeZ x t))
:pattern ((HasTypeFuel (SFuel f) x t)))))
(declare-fun NoHoist (Term Bool) Bool)
;;no-hoist
(assert (forall ((dummy Term) (b Bool))
(! (= (NoHoist dummy b) b)
:pattern ((NoHoist dummy b)))))
(define-fun  IsTyped ((x Term)) Bool
(exists ((t Term)) (HasTypeZ x t)))
(declare-fun ApplyTF (Term Fuel) Term)
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Prec (Term Term) Bool)
(assert (forall ((x Term) (y Term) (z Term))
(! (implies (and (Prec x y) (Prec y z)) (Prec x z))
:pattern ((Prec x z) (Prec x y)))))
(assert (forall ((x Term) (y Term))
(implies (Prec x y)
(not (Prec y x)))))
(declare-fun Closure (Term) Term)
(declare-fun ConsTerm (Term Term) Term)
(declare-fun ConsFuel (Fuel Term) Term)
(declare-fun Tm_uvar (Int) Term)
(define-fun Reify ((x Term)) Term x)
(declare-fun Prims.precedes (Universe Universe Term Term Term Term) Term)
(declare-fun Range_const (Int) Term)
(declare-fun _mul (Int Int) Int)
(declare-fun _div (Int Int) Int)
(declare-fun _mod (Int Int) Int)
(declare-fun __uu__PartialApp () Term)
(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))
(declare-fun _rmul (Real Real) Real)
(declare-fun _rdiv (Real Real) Real)
(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))
(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))
(define-fun Unreachable () Bool false); <start constructor FString_const>
; Constructor
(declare-fun FString_const (Int) FString)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 0 (FString_constr_id (FString_const @u0)))
    :pattern ((FString_const @u0))
    :qid constructor_distinct_FString_const))
  :named constructor_distinct_FString_const))
; Projector
(declare-fun FString_const_proj_0 (FString) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (FString_const_proj_0 (FString_const @u0)) @u0)
    :pattern ((FString_const @u0))
    :qid projection_inverse_FString_const_proj_0))
  :named projection_inverse_FString_const_proj_0))
; Discriminator definition
(define-fun is-FString_const ((__@u0 FString)) Bool
 (and (= (FString_constr_id __@u0) 0) (= __@u0 (FString_const (FString_const_proj_0 __@u0)))))
; </end constructor FString_const>
; <start constructor Tm_type>
; Constructor
(declare-fun Tm_type (Universe) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Universe))
   (! (= 2 (Term_constr_id (Tm_type @u0)))
    :pattern ((Tm_type @u0))
    :qid constructor_distinct_Tm_type))
  :named constructor_distinct_Tm_type))
; Projector
(declare-fun Tm_type_0 (Term) Universe)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Universe))
   (! (= (Tm_type_0 (Tm_type @u0)) @u0) :pattern ((Tm_type @u0)) :qid projection_inverse_Tm_type_0))
  :named projection_inverse_Tm_type_0))
; Discriminator definition
(define-fun is-Tm_type ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 2) (= __@x0 (Tm_type (Tm_type_0 __@x0)))))
; </end constructor Tm_type>
; <start constructor Tm_arrow>
; Constructor
(declare-fun Tm_arrow (Int) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 3 (Term_constr_id (Tm_arrow @u0)))
    :pattern ((Tm_arrow @u0))
    :qid constructor_distinct_Tm_arrow))
  :named constructor_distinct_Tm_arrow))
; Projector
(declare-fun Tm_arrow_id (Term) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (Tm_arrow_id (Tm_arrow @u0)) @u0)
    :pattern ((Tm_arrow @u0))
    :qid projection_inverse_Tm_arrow_id))
  :named projection_inverse_Tm_arrow_id))
; Discriminator definition
(define-fun is-Tm_arrow ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 3) (= __@x0 (Tm_arrow (Tm_arrow_id __@x0)))))
; </end constructor Tm_arrow>
; <start constructor Tm_unit>
; Constructor
(declare-fun Tm_unit () Term)
; Constructor distinct
;;; Fact-ids: 
(assert (! (= 6 (Term_constr_id Tm_unit)) :named constructor_distinct_Tm_unit))
; Discriminator definition
(define-fun is-Tm_unit ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 6) (= __@x0 Tm_unit)))
; </end constructor Tm_unit>
; <start constructor BoxInt>
; Constructor
(declare-fun BoxInt (Int) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 7 (Term_constr_id (BoxInt @u0))) :pattern ((BoxInt @u0)) :qid constructor_distinct_BoxInt))
  :named constructor_distinct_BoxInt))
; Projector
(declare-fun BoxInt_proj_0 (Term) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (BoxInt_proj_0 (BoxInt @u0)) @u0)
    :pattern ((BoxInt @u0))
    :qid projection_inverse_BoxInt_proj_0))
  :named projection_inverse_BoxInt_proj_0))
; Discriminator definition
(define-fun is-BoxInt ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 7) (= __@x0 (BoxInt (BoxInt_proj_0 __@x0)))))
; </end constructor BoxInt>
; <start constructor BoxBool>
; Constructor
(declare-fun BoxBool (Bool) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Bool))
   (! (= 8 (Term_constr_id (BoxBool @u0)))
    :pattern ((BoxBool @u0))
    :qid constructor_distinct_BoxBool))
  :named constructor_distinct_BoxBool))
; Projector
(declare-fun BoxBool_proj_0 (Term) Bool)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Bool))
   (! (= (BoxBool_proj_0 (BoxBool @u0)) @u0)
    :pattern ((BoxBool @u0))
    :qid projection_inverse_BoxBool_proj_0))
  :named projection_inverse_BoxBool_proj_0))
; Discriminator definition
(define-fun is-BoxBool ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 8) (= __@x0 (BoxBool (BoxBool_proj_0 __@x0)))))
; </end constructor BoxBool>
; <start constructor BoxString>
; Constructor
(declare-fun BoxString (FString) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 FString))
   (! (= 9 (Term_constr_id (BoxString @u0)))
    :pattern ((BoxString @u0))
    :qid constructor_distinct_BoxString))
  :named constructor_distinct_BoxString))
; Projector
(declare-fun BoxString_proj_0 (Term) FString)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 FString))
   (! (= (BoxString_proj_0 (BoxString @u0)) @u0)
    :pattern ((BoxString @u0))
    :qid projection_inverse_BoxString_proj_0))
  :named projection_inverse_BoxString_proj_0))
; Discriminator definition
(define-fun is-BoxString ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 9) (= __@x0 (BoxString (BoxString_proj_0 __@x0)))))
; </end constructor BoxString>
; <start constructor BoxReal>
; Constructor
(declare-fun BoxReal (Real) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Real))
   (! (= 10 (Term_constr_id (BoxReal @u0)))
    :pattern ((BoxReal @u0))
    :qid constructor_distinct_BoxReal))
  :named constructor_distinct_BoxReal))
; Projector
(declare-fun BoxReal_proj_0 (Term) Real)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Real))
   (! (= (BoxReal_proj_0 (BoxReal @u0)) @u0)
    :pattern ((BoxReal @u0))
    :qid projection_inverse_BoxReal_proj_0))
  :named projection_inverse_BoxReal_proj_0))
; Discriminator definition
(define-fun is-BoxReal ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 10) (= __@x0 (BoxReal (BoxReal_proj_0 __@x0)))))
; </end constructor BoxReal>
; <start constructor LexCons>
; Constructor
(declare-fun LexCons (Term Term Term) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= 11 (Term_constr_id (LexCons @x0 @x1 @x2)))
    :pattern ((LexCons @x0 @x1 @x2))
    :qid constructor_distinct_LexCons))
  :named constructor_distinct_LexCons))
; Projector
(declare-fun LexCons_0 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_0 (LexCons @x0 @x1 @x2)) @x0)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_0))
  :named projection_inverse_LexCons_0))
; Projector
(declare-fun LexCons_1 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_1 (LexCons @x0 @x1 @x2)) @x1)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_1))
  :named projection_inverse_LexCons_1))
; Projector
(declare-fun LexCons_2 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_2 (LexCons @x0 @x1 @x2)) @x2)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_2))
  :named projection_inverse_LexCons_2))
; Discriminator definition
(define-fun is-LexCons ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 11)
  (= __@x0 (LexCons (LexCons_0 __@x0) (LexCons_1 __@x0) (LexCons_2 __@x0)))))
; </end constructor LexCons>
(declare-fun Prims.precedes@tok (Universe Universe) Term)
(assert
(forall ((u0 Universe) (u1 Universe) (@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
(! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT (Prims.precedes@tok u0 u1) @x0) @x1) @x2) @x3)
(Prims.precedes u0 u1 @x0 @x1 @x2 @x3))
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT (Prims.precedes@tok u0 u1) @x0) @x1) @x2) @x3)))))

(define-fun is-Prims.LexCons ((t Term)) Bool 
(is-LexCons t))
(declare-fun Prims.lex_t () Term)
(declare-fun LexTop () Term)
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))
(iff (Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))
(or (Valid (Prims.precedes u0 u1 t1 t2 x1 y1))
(and (= x1 y1)
(Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t x2 y2)))))))
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term) (e1 Term) (e2 Term))
(! (iff (Valid (Prims.precedes u0 u1 t1 t2 e1 e2))
(Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t e1 e2)))
:pattern (Prims.precedes u0 u1 t1 t2 e1 e2))))
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term))
(! (iff (Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t t1 t2)) 
(Prec t1 t2))
:pattern ((Prims.precedes u0 u1 Prims.lex_t Prims.lex_t t1 t2)))))
(assert (forall ((e Term) (t Term))
(! (implies (HasType e t)
(Valid t))
:pattern ((HasType e t)
(Valid t))
:qid __prelude_valid_intro)))
(assert (forall ((u Universe) (t Term))
(! (iff (HasType (Tm_type u) t)
(= t (Tm_type (U_succ u))))
:pattern ((HasType (Tm_type u) t)))))

(push) ;; push{1
(declare-fun FStar.List.Tot.Base.append (Universe Term Term Term) Term)
; Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.append.fuel_instrumented (Fuel Universe Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.op_At (Universe Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.op_At@tok (Universe) Term)
(declare-fun FStar.Range.range () Term)
; Constructor
(declare-fun FStar.Stubs.Tactics.Common.NotAListLiteral () Term)
; Constructor base
(declare-fun FStar.Stubs.Tactics.Common.NotAListLiteral@base () Term)
; Constructor
(declare-fun FStar.Stubs.Tactics.Common.SKIP () Term)
; Constructor base
(declare-fun FStar.Stubs.Tactics.Common.SKIP@base () Term)
; Constructor
(declare-fun FStar.Stubs.Tactics.Common.Stop () Term)
; Constructor base
(declare-fun FStar.Stubs.Tactics.Common.Stop@base () Term)
; Constructor
(declare-fun FStar.Tactics.V2.Derived.Goal_not_trivial () Term)
; Constructor base
(declare-fun FStar.Tactics.V2.Derived.Goal_not_trivial@base () Term)
(declare-fun Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34 (Term Term) Term)
(declare-fun Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d (Term) Term)
(declare-fun Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2 (Term) Term)
(declare-fun Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521 (Term Term) Term)
(declare-fun Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4 (Term) Term)
(declare-fun Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996 (Term) Term)
; Constructor
(declare-fun Prims.Cons (Universe Term Term Term) Term)
; Projector
(declare-fun Prims.Cons_@0 (Term) Universe)
; Projector
(declare-fun Prims.Cons_@a (Term) Term)
; Projector
(declare-fun Prims.Cons_@hd (Term) Term)
; Projector
(declare-fun Prims.Cons_@tl (Term) Term)
; Constructor
(declare-fun Prims.Nil (Universe Term) Term)
; Projector
(declare-fun Prims.Nil_@0 (Term) Universe)
; Projector
(declare-fun Prims.Nil_@a (Term) Term)
; Constructor
(declare-fun Prims.T () Term)
; data constructor proxy: Prims.T
(declare-fun Prims.T@tok () Term)
(declare-fun Prims.__cache_version_number__ () Term)
(declare-fun Prims.bool () Term)
(declare-fun Prims.eqtype () Term)
(declare-fun Prims.hasEq (Universe Term) Term)
(declare-fun Prims.int () Term)
(declare-fun Prims.l_True () Term)
; Constructor
(declare-fun Prims.list (Universe Term) Term)
; token
(declare-fun Prims.list@tok (Universe) Term)
(declare-fun Prims.logical () Term)
(declare-fun Prims.pure_post (Universe Term) Term)
(declare-fun Prims.pure_post_ (Universe Universe Term Term) Term)
(declare-fun Prims.pure_wp (Universe Term) Term)
(declare-fun Prims.squash (Universe Term) Term)
; Constructor
(declare-fun Prims.trivial () Term)
(declare-fun Prims.unit () Term)
(declare-fun Prims.uu___is_Cons (Universe Term Term) Term)
(declare-fun Prims.uu___is_Nil (Universe Term Term) Term)
(declare-fun Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae (Universe Term Term) Term)
(declare-fun Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17 (Universe) Term)
(declare-fun Tm_refine_2de20c066034c13bf76e9c0b94f4806c (Term) Term)
(declare-fun Tm_refine_9d6af3f3535473623f7aec2f0501897f () Term)
(declare-fun Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 (Universe Term Term) Term)
; Discriminator definition
(define-fun is-FStar.Stubs.Tactics.Common.NotAListLiteral ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 102) (= __@x0 FStar.Stubs.Tactics.Common.NotAListLiteral)))
; Discriminator definition
(define-fun is-FStar.Stubs.Tactics.Common.SKIP ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 117) (= __@x0 FStar.Stubs.Tactics.Common.SKIP)))
; Discriminator definition
(define-fun is-FStar.Stubs.Tactics.Common.Stop ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 121) (= __@x0 FStar.Stubs.Tactics.Common.Stop)))
; Discriminator definition
(define-fun is-FStar.Tactics.V2.Derived.Goal_not_trivial ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 112) (= __@x0 FStar.Tactics.V2.Derived.Goal_not_trivial)))
; Discriminator definition
(define-fun is-Prims.Cons ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 325)
  (=
   __@x0
   (Prims.Cons
    (Prims.Cons_@0 __@x0)
    (Prims.Cons_@a __@x0)
    (Prims.Cons_@hd __@x0)
    (Prims.Cons_@tl __@x0)))))
; Discriminator definition
(define-fun is-Prims.Nil ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 320) (= __@x0 (Prims.Nil (Prims.Nil_@0 __@x0) (Prims.Nil_@a __@x0)))))
; Discriminator definition
(define-fun is-Prims.T ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 122) (= __@x0 Prims.T)))
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.append; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(119,8-119,14); use=FStar.List.Tot.Base.fst(119,8-119,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (FStar.List.Tot.Base.append @u0 @x1 @x2 @x3)
     (FStar.List.Tot.Base.append.fuel_instrumented MaxFuel @u0 @x1 @x2 @x3))
    :pattern ((FStar.List.Tot.Base.append @u0 @x1 @x2 @x3))
    :qid @fuel_correspondence_FStar.List.Tot.Base.append.fuel_instrumented))
  :named @fuel_correspondence_FStar.List.Tot.Base.append.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.append; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(119,8-119,14); use=FStar.List.Tot.Base.fst(119,8-119,14)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (=
     (FStar.List.Tot.Base.append.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4)
     (FStar.List.Tot.Base.append.fuel_instrumented ZFuel @u1 @x2 @x3 @x4))
    :pattern ((FStar.List.Tot.Base.append.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4))
    :qid @fuel_irrelevance_FStar.List.Tot.Base.append.fuel_instrumented))
  :named @fuel_irrelevance_FStar.List.Tot.Base.append.fuel_instrumented))
; kick_partial_app
;;; Fact-ids: Name FStar.Tactics.V2.Derived.op_At; Namespace FStar.Tactics.V2.Derived
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (FStar.List.Tot.Base.op_At @u0 @x1 @x2 @x3)
     (ApplyTT (ApplyTT (ApplyTT (FStar.List.Tot.Base.op_At@tok @u0) @x1) @x2) @x3))
    :pattern ((FStar.List.Tot.Base.op_At @u0 @x1 @x2 @x3))
    :qid @kick_partial_app_dc46d6819cb5e79990c5638af5ac8b8f))
  :named @kick_partial_app_dc46d6819cb5e79990c5638af5ac8b8f))
; interpretation_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17
;;; Fact-ids: Name FStar.List.Tot.Base.rev_acc; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(107,13-107,48); use=FStar.List.Tot.Base.fst(108,8-108,15)
  (forall ((@x0 Term) (@u1 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17 @u1))
     (and
      ;; def=FStar.List.Tot.Base.fst(107,13-107,48); use=FStar.List.Tot.Base.fst(108,8-108,15)
      (forall ((@x2 Term) (@x3 Term) (@x4 Term))
       (! (implies
         (and
          (HasType @x2 (Tm_type @u1))
          (HasType @x3 (Prims.list @u1 @x2))
          (HasType @x4 (Prims.list @u1 @x2)))
         (HasType (ApplyTT (ApplyTT (ApplyTT @x0 @x2) @x3) @x4) (Prims.list @u1 @x2)))
        :pattern ((ApplyTT (ApplyTT (ApplyTT @x0 @x2) @x3) @x4))
        :qid FStar.List.Tot.Base_interpretation_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17.1))
      (IsTotFun @x0)
      ;; def=FStar.List.Tot.Base.fst(107,13-107,48); use=FStar.List.Tot.Base.fst(108,8-108,15)
      (forall ((@x2 Term))
       (! (implies (HasType @x2 (Tm_type @u1)) (IsTotFun (ApplyTT @x0 @x2)))
        :pattern ((ApplyTT @x0 @x2))
        :qid FStar.List.Tot.Base_interpretation_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17.2))
      ;; def=FStar.List.Tot.Base.fst(107,13-107,48); use=FStar.List.Tot.Base.fst(108,8-108,15)
      (forall ((@x2 Term) (@x3 Term))
       (! (implies
         (and (HasType @x2 (Tm_type @u1)) (HasType @x3 (Prims.list @u1 @x2)))
         (IsTotFun (ApplyTT (ApplyTT @x0 @x2) @x3)))
        :pattern ((ApplyTT (ApplyTT @x0 @x2) @x3))
        :qid FStar.List.Tot.Base_interpretation_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17.3))))
    :pattern ((HasTypeZ @x0 (Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17 @u1)))
    :qid FStar.List.Tot.Base_interpretation_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17))
  :named FStar.List.Tot.Base_interpretation_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17))
; pre-typing for functions
;;; Fact-ids: Name FStar.List.Tot.Base.rev_acc; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(107,13-107,48); use=FStar.List.Tot.Base.fst(108,8-108,15)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17 @u2))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17 @u2)))
    :qid FStar.List.Tot.Base_pre_typing_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17))
  :named FStar.List.Tot.Base_pre_typing_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17))
; interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@x0 Term) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u1 @x2 @x3))
     (and
      ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
      (forall ((@x4 Term))
       (! (implies
         (HasType @x4 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u1 @x2 @x3))
         (HasType (ApplyTT @x0 @x4) (Tm_type U_zero)))
        :pattern ((ApplyTT @x0 @x4))
        :qid Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u1 @x2 @x3)))
    :qid Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; pre-typing for functions
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u2 @x3 @x4))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u2 @x3 @x4)))
    :qid Prims_pre_typing_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named Prims_pre_typing_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; pretyping
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Universe) (@x3 Term))
   (! (implies (HasTypeFuel @u1 @x0 (Prims.list @u2 @x3)) (= (Prims.list @u2 @x3) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (Prims.list @u2 @x3)))
    :qid Prims_pretyping_da5ad05a41b0a8d46bda8000c9315425))
  :named Prims_pretyping_da5ad05a41b0a8d46bda8000c9315425))
; pretyping
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,5-99,12); use=Prims.fst(99,5-99,12)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.trivial) (= Prims.trivial (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.trivial))
    :qid Prims_pretyping_e8ffb7d227a1bbf69407a8d2ad2c4c83))
  :named Prims_pretyping_e8ffb7d227a1bbf69407a8d2ad2c4c83))
; pretyping
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! ;; def=Prims.fst(88,5-88,9); use=Prims.fst(88,5-88,9)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.bool) (= Prims.bool (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.bool))
    :qid Prims_pretyping_f537159ed795b314b4e58c260361ae86))
  :named Prims_pretyping_f537159ed795b314b4e58c260361ae86))
; pretyping
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! ;; def=Prims.fst(104,5-104,9); use=Prims.fst(104,5-104,9)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.unit) (= Prims.unit (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.unit))
    :qid Prims_pretyping_f8666440faa91836cc5a13998af863fc))
  :named Prims_pretyping_f8666440faa91836cc5a13998af863fc))
; Assumption: Prims.list__uu___haseq
;;; Fact-ids: Name Prims.list__uu___haseq; Namespace Prims
(assert
 (! (forall ((@u0 Universe))
   (! (forall ((@x1 Term))
     (! (implies
       (and (HasType @x1 (Tm_type @u0)) (Valid (Prims.hasEq @u0 @x1)))
       (Valid (Prims.hasEq @u0 (Prims.list @u0 @x1))))
      :pattern ((Prims.hasEq @u0 (Prims.list @u0 @x1)))
      :qid assumption_Prims.list__uu___haseq.1))
    :qid assumption_Prims.list__uu___haseq))
  :named assumption_Prims.list__uu___haseq))
; bool inversion
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.bool) (is-BoxBool @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.bool))
    :qid bool_inversion))
  :named bool_inversion))
; bool typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (forall ((@u0 Bool))
   (! (HasType (BoxBool @u0) Prims.bool) :pattern ((BoxBool @u0)) :qid bool_typing))
  :named bool_typing))
; Constructor base
;;; Fact-ids: Name FStar.Stubs.Tactics.Common.NotAListLiteral; Namespace FStar.Stubs.Tactics.Common
(assert
 (! (implies
   (is-FStar.Stubs.Tactics.Common.NotAListLiteral FStar.Stubs.Tactics.Common.NotAListLiteral)
   (= FStar.Stubs.Tactics.Common.NotAListLiteral FStar.Stubs.Tactics.Common.NotAListLiteral@base))
  :named constructor_base_FStar.Stubs.Tactics.Common.NotAListLiteral))
; Constructor base
;;; Fact-ids: Name FStar.Stubs.Tactics.Common.SKIP; Namespace FStar.Stubs.Tactics.Common
(assert
 (! (implies
   (is-FStar.Stubs.Tactics.Common.SKIP FStar.Stubs.Tactics.Common.SKIP)
   (= FStar.Stubs.Tactics.Common.SKIP FStar.Stubs.Tactics.Common.SKIP@base))
  :named constructor_base_FStar.Stubs.Tactics.Common.SKIP))
; Constructor base
;;; Fact-ids: Name FStar.Stubs.Tactics.Common.Stop; Namespace FStar.Stubs.Tactics.Common
(assert
 (! (implies
   (is-FStar.Stubs.Tactics.Common.Stop FStar.Stubs.Tactics.Common.Stop)
   (= FStar.Stubs.Tactics.Common.Stop FStar.Stubs.Tactics.Common.Stop@base))
  :named constructor_base_FStar.Stubs.Tactics.Common.Stop))
; Constructor base
;;; Fact-ids: Name FStar.Tactics.V2.Derived.Goal_not_trivial; Namespace FStar.Tactics.V2.Derived
(assert
 (! (implies
   (is-FStar.Tactics.V2.Derived.Goal_not_trivial FStar.Tactics.V2.Derived.Goal_not_trivial)
   (= FStar.Tactics.V2.Derived.Goal_not_trivial FStar.Tactics.V2.Derived.Goal_not_trivial@base))
  :named constructor_base_FStar.Tactics.V2.Derived.Goal_not_trivial))
; Constructor distinct
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= 325 (Term_constr_id (Prims.Cons @u0 @x1 @x2 @x3)))
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid constructor_distinct_Prims.Cons))
  :named constructor_distinct_Prims.Cons))
; Constructor distinct
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= 320 (Term_constr_id (Prims.Nil @u0 @x1)))
    :pattern ((Prims.Nil @u0 @x1))
    :qid constructor_distinct_Prims.Nil))
  :named constructor_distinct_Prims.Nil))
; Constructor distinct
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= 122 (Term_constr_id Prims.T)) :named constructor_distinct_Prims.T))
; Constructor distinct
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (= 107 (Term_constr_id Prims.bool)) :named constructor_distinct_Prims.bool))
; Constructor distinct
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= 313 (Term_constr_id (Prims.list @u0 @x1)))
    :pattern ((Prims.list @u0 @x1))
    :qid constructor_distinct_Prims.list))
  :named constructor_distinct_Prims.list))
; Constructor distinct
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= 116 (Term_constr_id Prims.trivial)) :named constructor_distinct_Prims.trivial))
; Constructor distinct
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (= 125 (Term_constr_id Prims.unit)) :named constructor_distinct_Prims.unit))
; data constructor typing elim
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x5))
     (and
      (HasTypeFuel @u0 @x5 (Tm_type @u1))
      (HasTypeFuel @u0 @x3 @x5)
      (HasTypeFuel @u0 @x4 (Prims.list @u1 @x5))))
    :pattern ((HasTypeFuel (SFuel @u0) (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x5)))
    :qid data_elim_Prims.Cons))
  :named data_elim_Prims.Cons))
; data constructor typing elim
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Nil @u1 @x2) (Prims.list @u1 @x3))
     (HasTypeFuel @u0 @x3 (Tm_type @u1)))
    :pattern ((HasTypeFuel (SFuel @u0) (Prims.Nil @u1 @x2) (Prims.list @u1 @x3)))
    :qid data_elim_Prims.Nil))
  :named data_elim_Prims.Nil))
; data constructor typing intro
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasTypeFuel @u0 @x2 (Tm_type @u1))
      (HasTypeFuel @u0 @x3 @x2)
      (HasTypeFuel @u0 @x4 (Prims.list @u1 @x2)))
     (HasTypeFuel @u0 (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x2)))
    :pattern ((HasTypeFuel @u0 (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x2)))
    :qid data_typing_intro_Prims.Cons@tok))
  :named data_typing_intro_Prims.Cons@tok))
; data constructor typing intro
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term))
   (! (implies
     (HasTypeFuel @u0 @x2 (Tm_type @u1))
     (HasTypeFuel @u0 (Prims.Nil @u1 @x2) (Prims.list @u1 @x2)))
    :pattern ((HasTypeFuel @u0 (Prims.Nil @u1 @x2) (Prims.list @u1 @x2)))
    :qid data_typing_intro_Prims.Nil@tok))
  :named data_typing_intro_Prims.Nil@tok))
; data constructor typing intro
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,17-99,18); use=Prims.fst(99,17-99,18)
  (forall ((@u0 Fuel))
   (! (HasTypeFuel @u0 Prims.T Prims.trivial)
    :pattern ((HasTypeFuel @u0 Prims.T Prims.trivial))
    :qid data_typing_intro_Prims.T@tok))
  :named data_typing_intro_Prims.T@tok))
; Discriminator equation
;;; Fact-ids: Name Prims.uu___is_Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= (Prims.uu___is_Cons @u0 @x1 @x2) (BoxBool (is-Prims.Cons @x2)))
    :pattern ((Prims.uu___is_Cons @u0 @x1 @x2))
    :qid disc_equation_Prims.Cons))
  :named disc_equation_Prims.Cons))
; Discriminator equation
;;; Fact-ids: Name Prims.uu___is_Nil; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= (Prims.uu___is_Nil @u0 @x1 @x2) (BoxBool (is-Prims.Nil @x2)))
    :pattern ((Prims.uu___is_Nil @u0 @x1 @x2))
    :qid disc_equation_Prims.Nil))
  :named disc_equation_Prims.Nil))
; equality for proxy
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= Prims.T@tok Prims.T) :named equality_tok_Prims.T@tok))
; Equation for FStar.List.Tot.Base.op_At
;;; Fact-ids: Name FStar.List.Tot.Base.op_At; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(124,4-124,9); use=FStar.List.Tot.Base.fst(124,4-124,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (FStar.List.Tot.Base.op_At @u0 @x1 @x2 @x3) (FStar.List.Tot.Base.append @u0 @x1 @x2 @x3))
    :pattern ((FStar.List.Tot.Base.op_At @u0 @x1 @x2 @x3))
    :qid equation_FStar.List.Tot.Base.op_At))
  :named equation_FStar.List.Tot.Base.op_At))
; Equation for Prims.eqtype
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (= Prims.eqtype Tm_refine_9d6af3f3535473623f7aec2f0501897f) :named equation_Prims.eqtype))
; Equation for Prims.l_True
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (= Prims.l_True (Prims.squash U_zero Prims.trivial)) :named equation_Prims.l_True))
; Equation for Prims.logical
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (= Prims.logical (Tm_type U_zero)) :named equation_Prims.logical))
; Equation for Prims.pure_post
;;; Fact-ids: Name Prims.pure_post; Namespace Prims
(assert
 (! ;; def=Prims.fst(324,4-324,13); use=Prims.fst(324,4-324,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.pure_post @u0 @x1) (Prims.pure_post_ @u0 U_zero @x1 Prims.l_True))
    :pattern ((Prims.pure_post @u0 @x1))
    :qid equation_Prims.pure_post))
  :named equation_Prims.pure_post))
; Equation for Prims.pure_post'
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,4-323,14); use=Prims.fst(323,4-323,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (= (Prims.pure_post_ @u0 @u1 @x2 @x3) (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x3 @x2))
    :pattern ((Prims.pure_post_ @u0 @u1 @x2 @x3))
    :qid equation_Prims.pure_post_))
  :named equation_Prims.pure_post_))
; Equation for Prims.squash
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,5-125,11); use=Prims.fst(125,5-125,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.squash @u0 @x1) (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x1))
    :pattern ((Prims.squash @u0 @x1))
    :qid equation_Prims.squash))
  :named equation_Prims.squash))
; Equation for fuel-instrumented recursive function: FStar.List.Tot.Base.append
;;; Fact-ids: Name FStar.List.Tot.Base.append; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(119,8-119,14); use=FStar.List.Tot.Base.fst(119,8-119,14)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x2 (Tm_type @u1))
      (HasType @x3 (Prims.list @u1 @x2))
      (HasType @x4 (Prims.list @u1 @x2)))
     (=
      (FStar.List.Tot.Base.append.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4)
      (let ((@lb5 @x3))
       (ite
        (is-Prims.Nil @lb5)
        @x4
        (ite
         (is-Prims.Cons @lb5)
         (Prims.Cons
          @u1
          @x2
          (Prims.Cons_@hd @lb5)
          (FStar.List.Tot.Base.append.fuel_instrumented @u0 @u1 @x2 (Prims.Cons_@tl @lb5) @x4))
         Tm_unit)))))
    :weight 0
    :pattern ((FStar.List.Tot.Base.append.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4))
    :qid equation_with_fuel_FStar.List.Tot.Base.append.fuel_instrumented))
  :named equation_with_fuel_FStar.List.Tot.Base.append.fuel_instrumented))
; fresh token
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! (forall ((@u0 Universe))
   (! (= 314 (Term_constr_id (Prims.list@tok @u0)))
    :pattern ((Prims.list@tok @u0))
    :qid fresh_token_Prims.list@tok))
  :named fresh_token_Prims.list@tok))
; inversion axiom
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) @x1 (Prims.list @u2 @x3))
     (or
      (and (is-Prims.Nil @x1) (= @u2 (Prims.Nil_@0 @x1)) (= @x3 (Prims.Nil_@a @x1)))
      (and (is-Prims.Cons @x1) (= @u2 (Prims.Cons_@0 @x1)) (= @x3 (Prims.Cons_@a @x1)))))
    :pattern ((HasTypeFuel (SFuel @u0) @x1 (Prims.list @u2 @x3)))
    :qid fuel_guarded_inversion_Prims.list))
  :named fuel_guarded_inversion_Prims.list))
; inversion axiom
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,5-99,12); use=Prims.fst(99,5-99,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.trivial) (is-Prims.T @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.trivial))
    :qid fuel_guarded_inversion_Prims.trivial))
  :named fuel_guarded_inversion_Prims.trivial))
; function token typing
;;; Fact-ids: Name FStar.List.Tot.Base.op_At; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(124,4-124,9); use=FStar.List.Tot.Base.fst(124,4-124,9)
  (forall ((@u0 Universe))
   (! (HasType (FStar.List.Tot.Base.op_At@tok @u0) (Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17 @u0))
    :pattern ((FStar.List.Tot.Base.op_At@tok @u0))
    :qid function_token_typing_FStar.List.Tot.Base.op_At))
  :named function_token_typing_FStar.List.Tot.Base.op_At))
; function token typing
;;; Fact-ids: Name Prims.__cache_version_number__; Namespace Prims
(assert
 (! (HasType Prims.__cache_version_number__ Prims.int)
  :named function_token_typing_Prims.__cache_version_number__))
; function token typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (HasType Prims.bool Prims.eqtype) :named function_token_typing_Prims.bool))
; function token typing
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Prims.eqtype (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.eqtype))
; function token typing
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (HasType Prims.l_True Prims.logical) :named function_token_typing_Prims.l_True))
; function token typing
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (HasType Prims.logical (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.logical))
; function token typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Prims.unit Prims.eqtype) :named function_token_typing_Prims.unit))
; haseq for Tm_refine_2de20c066034c13bf76e9c0b94f4806c
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0))))
    :qid haseqTm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named haseqTm_refine_2de20c066034c13bf76e9c0b94f4806c))
; haseq for Tm_refine_9d6af3f3535473623f7aec2f0501897f
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq (U_succ U_zero) Tm_refine_9d6af3f3535473623f7aec2f0501897f))
   (Valid (Prims.hasEq (U_succ U_zero) (Tm_type U_zero))))
  :named haseqTm_refine_9d6af3f3535473623f7aec2f0501897f))
; haseq for Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq @u0 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2)))
     (Valid (Prims.hasEq @u0 @x2)))
    :pattern ((Valid (Prims.hasEq @u0 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2))))
    :qid haseqTm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named haseqTm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! (and
   ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
   (forall ((@u0 Universe))
    (! (IsTotFun (Prims.list@tok @u0)) :pattern ((Prims.list@tok @u0)) :qid kinding_Prims.list@tok))
   ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
   (forall ((@u0 Universe) (@x1 Term))
    (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.list @u0 @x1) (Tm_type @u0)))
     :pattern ((Prims.list @u0 @x1))
     :qid kinding_Prims.list@tok.1)))
  :named kinding_Prims.list@tok))
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (HasType Prims.trivial (Tm_type U_zero)) :named kinding_Prims.trivial@tok))
; kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType
     (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x1 @x2)
     (Tm_type (U_max (U_succ U_zero) @u0)))
    :pattern
     ((HasType
       (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x1 @x2)
       (Tm_type (U_max (U_succ U_zero) @u0))))
    :qid kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; kinding_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17
;;; Fact-ids: Name FStar.List.Tot.Base.rev_acc; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(107,13-107,48); use=FStar.List.Tot.Base.fst(108,8-108,15)
  (forall ((@u0 Universe))
   (! (HasType (Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17 @u0) (Tm_type (U_succ @u0)))
    :pattern ((HasType (Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17 @u0) (Tm_type (U_succ @u0))))
    :qid kinding_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17))
  :named kinding_Tm_arrow_f008491dd128d51e4f4b5d8b7adfbe17))
; Lemma: FStar.List.Tot.Properties.append_l_nil
;;; Fact-ids: Name FStar.List.Tot.Properties.append_l_nil; Namespace FStar.List.Tot.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (Prims.list @u0 @x1)))
     ;; def=FStar.List.Tot.Properties.fsti(123,17-123,28); use=FStar.List.Tot.Properties.fsti(123,17-123,28)
     (= (FStar.List.Tot.Base.op_At @u0 @x1 @x2 (Prims.Nil @u0 @x1)) @x2))
    :pattern ((FStar.List.Tot.Base.op_At @u0 @x1 @x2 (Prims.Nil @u0 @x1)))
    :qid lemma_FStar.List.Tot.Properties.append_l_nil))
  :named lemma_FStar.List.Tot.Properties.append_l_nil))
; Lemma: FStar.List.Tot.Properties.precedes_append_cons_r
;;; Fact-ids: Name FStar.List.Tot.Properties.precedes_append_cons_r; Namespace FStar.List.Tot.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Prims.list @u0 @x1))
      (HasType @x3 @x1)
      (HasType @x4 (Prims.list @u0 @x1)))
     ;; def=FStar.List.Tot.Properties.fsti(754,11-754,37); use=FStar.List.Tot.Properties.fsti(754,11-754,37)
     (Valid
      ;; def=FStar.List.Tot.Properties.fsti(754,11-754,37); use=FStar.List.Tot.Properties.fsti(754,11-754,37)
      (Prims.precedes
       @u0
       @u0
       @x1
       (Prims.list @u0 @x1)
       @x3
       (FStar.List.Tot.Base.append.fuel_instrumented ZFuel @u0 @x1 @x2 (Prims.Cons @u0 @x1 @x3 @x4)))))
    :pattern
     ((Prims.precedes
       @u0
       @u0
       @x1
       (Prims.list @u0 @x1)
       @x3
       (FStar.List.Tot.Base.append.fuel_instrumented ZFuel @u0 @x1 @x2 (Prims.Cons @u0 @x1 @x3 @x4))))
    :qid lemma_FStar.List.Tot.Properties.precedes_append_cons_r))
  :named lemma_FStar.List.Tot.Properties.precedes_append_cons_r))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.Effect.tac; Namespace FStar.Tactics.Effect
(assert
 (! ;; def=FStar.Tactics.Effect.fsti(178,16-178,19); use=FStar.Tactics.Effect.fsti(178,22-178,32)
  (forall ((@u0 Universe) (@u1 Universe))
   (! ;; def=FStar.Tactics.Effect.fsti(178,16-178,19); use=FStar.Tactics.Effect.fsti(178,22-178,32)
    (forall ((@x2 Term) (@x3 Term))
     (! (implies
       (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
       (HasType (Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34 @x2 @x3) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34 @x2 @x3) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34))
  :named non_total_function_typing_Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.Effect.tac_repr; Namespace FStar.Tactics.Effect
(assert
 (! ;; def=FStar.Tactics.Effect.fsti(36,14-37,16); use=FStar.Tactics.Effect.fsti(37,2-37,24)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.Effect.fsti(36,14-37,16); use=FStar.Tactics.Effect.fsti(37,2-37,24)
    (forall ((@x1 Term))
     (! (implies
       (HasType @x1 (Tm_type @u0))
       (HasType (Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d @x1) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d @x1) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d))
  :named non_total_function_typing_Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.MApply.termable; Namespace FStar.Tactics.MApply; Name FStar.Tactics.MApply.Mktermable; Namespace FStar.Tactics.MApply
(assert
 (! ;; def=FStar.Tactics.MApply.fsti(10,16-11,25); use=FStar.Tactics.MApply.fsti(11,12-11,25)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.MApply.fsti(10,16-11,25); use=FStar.Tactics.MApply.fsti(11,12-11,25)
    (forall ((@x1 Term))
     (! (implies
       (HasType @x1 (Tm_type @u0))
       (HasType (Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2 @x1) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2 @x1) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2))
  :named non_total_function_typing_Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.Effect.lift_div_tac; Namespace FStar.Tactics.Effect
(assert
 (! ;; def=FStar.Tactics.Effect.fsti(138,18-138,48); use=FStar.Tactics.Effect.fsti(138,44-138,57)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.Effect.fsti(138,18-138,48); use=FStar.Tactics.Effect.fsti(138,44-138,57)
    (forall ((@x1 Term) (@x2 Term))
     (! (implies
       (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (Prims.pure_wp @u0 @x1)))
       (HasType (Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521 @x1 @x2) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521 @x1 @x2) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521))
  :named non_total_function_typing_Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.V2.Derived.op_Less_Bar_Greater; Namespace FStar.Tactics.V2.Derived
(assert
 (! ;; def=FStar.Tactics.V2.Derived.fst(474,13-476,27); use=FStar.Tactics.V2.Derived.fst(474,25-477,8)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.V2.Derived.fst(474,13-476,27); use=FStar.Tactics.V2.Derived.fst(474,25-477,8)
    (forall ((@x1 Term))
     (! (implies
       (HasType @x1 (Tm_type @u0))
       (HasType (Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4 @x1) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4 @x1) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4))
  :named non_total_function_typing_Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.V2.Derived.discard; Namespace FStar.Tactics.V2.Derived
(assert
 (! ;; def=FStar.Tactics.V2.Derived.fst(513,19-513,33); use=FStar.Tactics.V2.Derived.fst(513,19-513,33)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.V2.Derived.fst(513,19-513,33); use=FStar.Tactics.V2.Derived.fst(513,19-513,33)
    (forall ((@x1 Term))
     (! (implies
       (HasType @x1 (Tm_type @u0))
       (HasType (Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996 @x1) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996 @x1) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996))
  :named non_total_function_typing_Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996))
; kinding
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@u0 Universe))
   (! (is-Tm_arrow (PreType (Prims.list@tok @u0)))
    :pattern ((Prims.list@tok @u0))
    :qid pre_kinding_Prims.list@tok))
  :named pre_kinding_Prims.list@tok))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.Cons_@0 (Prims.Cons @u0 @x1 @x2 @x3)) @u0)
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid projection_inverse_Prims.Cons_@0))
  :named projection_inverse_Prims.Cons_@0))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.Cons_@a (Prims.Cons @u0 @x1 @x2 @x3)) @x1)
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid projection_inverse_Prims.Cons_@a))
  :named projection_inverse_Prims.Cons_@a))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.Cons_@hd (Prims.Cons @u0 @x1 @x2 @x3)) @x2)
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid projection_inverse_Prims.Cons_@hd))
  :named projection_inverse_Prims.Cons_@hd))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.Cons_@tl (Prims.Cons @u0 @x1 @x2 @x3)) @x3)
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid projection_inverse_Prims.Cons_@tl))
  :named projection_inverse_Prims.Cons_@tl))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.Nil_@0 (Prims.Nil @u0 @x1)) @u0)
    :pattern ((Prims.Nil @u0 @x1))
    :qid projection_inverse_Prims.Nil_@0))
  :named projection_inverse_Prims.Nil_@0))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.Nil_@a (Prims.Nil @u0 @x1)) @x1)
    :pattern ((Prims.Nil @u0 @x1))
    :qid projection_inverse_Prims.Nil_@a))
  :named projection_inverse_Prims.Nil_@a))
; refinement_interpretation
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Prims.fst(125,13-125,14); use=Prims.fst(125,40-125,41)
      (Valid
       ;; def=Prims.fst(125,13-125,14); use=Prims.fst(125,40-125,41)
       @x2)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2)))
    :qid refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
; refinement_interpretation
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! ;; def=Prims.fst(81,14-81,31); use=Prims.fst(81,14-81,31)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f)
     (and
      (HasTypeFuel @u0 @x1 (Tm_type U_zero))
      ;; def=Prims.fst(81,23-81,30); use=Prims.fst(81,23-81,30)
      (Valid
       ;; def=Prims.fst(81,23-81,30); use=Prims.fst(81,23-81,30)
       (Prims.hasEq U_zero @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f))
    :qid refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
  :named refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
; refinement_interpretation
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 @x4)
      ;; def=Prims.fst(323,18-323,21); use=Prims.fst(323,36-323,39)
      (Valid
       ;; def=Prims.fst(323,18-323,21); use=Prims.fst(323,36-323,39)
       @x3)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named refinement_interpretation_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
; refinement kinding
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named refinement_kinding_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
; refinement kinding
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Tm_refine_9d6af3f3535473623f7aec2f0501897f (Tm_type (U_succ U_zero)))
  :named refinement_kinding_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
; refinement kinding
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2) (Tm_type @u0))
    :pattern ((HasType (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2) (Tm_type @u0)))
    :qid refinement_kinding_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named refinement_kinding_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
; subterm ordering
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x5))
     (and
      (Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t @x3 (Prims.Cons @u1 @x2 @x3 @x4)))
      (Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t @x4 (Prims.Cons @u1 @x2 @x3 @x4)))))
    :pattern ((HasTypeFuel (SFuel @u0) (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x5)))
    :qid subterm_ordering_Prims.Cons))
  :named subterm_ordering_Prims.Cons))
; Typing correspondence of token to term
;;; Fact-ids: Name FStar.List.Tot.Base.append; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(119,8-119,14); use=FStar.List.Tot.Base.fst(119,8-119,14)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x2 (Tm_type @u1))
      (HasType @x3 (Prims.list @u1 @x2))
      (HasType @x4 (Prims.list @u1 @x2)))
     (HasType
      (FStar.List.Tot.Base.append.fuel_instrumented @u0 @u1 @x2 @x3 @x4)
      (Prims.list @u1 @x2)))
    :pattern ((FStar.List.Tot.Base.append.fuel_instrumented @u0 @u1 @x2 @x3 @x4))
    :qid token_correspondence_FStar.List.Tot.Base.append.fuel_instrumented))
  :named token_correspondence_FStar.List.Tot.Base.append.fuel_instrumented))
; Name-token correspondence
;;; Fact-ids: Name FStar.List.Tot.Base.op_At; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(124,4-124,9); use=FStar.List.Tot.Base.fst(124,4-124,9)
  (forall ((@u0 Universe))
   (! ;; def=FStar.List.Tot.Base.fst(124,4-124,9); use=FStar.List.Tot.Base.fst(124,4-124,9)
    (forall ((@x1 Term) (@x2 Term) (@x3 Term))
     (! (=
       (ApplyTT (ApplyTT (ApplyTT (FStar.List.Tot.Base.op_At@tok @u0) @x1) @x2) @x3)
       (FStar.List.Tot.Base.op_At @u0 @x1 @x2 @x3))
      :pattern ((ApplyTT (ApplyTT (ApplyTT (FStar.List.Tot.Base.op_At@tok @u0) @x1) @x2) @x3))
      :pattern ((FStar.List.Tot.Base.op_At @u0 @x1 @x2 @x3))
      :qid token_correspondence_FStar.List.Tot.Base.op_At.1))
    :pattern ((FStar.List.Tot.Base.op_At@tok @u0))
    :qid token_correspondence_FStar.List.Tot.Base.op_At))
  :named token_correspondence_FStar.List.Tot.Base.op_At))
; name-token correspondence
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (ApplyTT (Prims.list@tok @u0) @x1) (Prims.list @u0 @x1))
    :pattern ((ApplyTT (Prims.list@tok @u0) @x1))
    :pattern ((Prims.list @u0 @x1))
    :qid token_correspondence_Prims.list@tok))
  :named token_correspondence_Prims.list@tok))
; True interpretation
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert (! (Valid Prims.l_True) :named true_interp))
; free var typing
;;; Fact-ids: Name FStar.List.Tot.Base.append; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(119,8-119,14); use=FStar.List.Tot.Base.fst(119,8-119,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Prims.list @u0 @x1))
      (HasType @x3 (Prims.list @u0 @x1)))
     (HasType (FStar.List.Tot.Base.append @u0 @x1 @x2 @x3) (Prims.list @u0 @x1)))
    :pattern ((FStar.List.Tot.Base.append @u0 @x1 @x2 @x3))
    :qid typing_FStar.List.Tot.Base.append))
  :named typing_FStar.List.Tot.Base.append))
; free var typing
;;; Fact-ids: Name FStar.List.Tot.Base.op_At; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(124,4-124,9); use=FStar.List.Tot.Base.fst(124,4-124,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Prims.list @u0 @x1))
      (HasType @x3 (Prims.list @u0 @x1)))
     (HasType (FStar.List.Tot.Base.op_At @u0 @x1 @x2 @x3) (Prims.list @u0 @x1)))
    :pattern ((FStar.List.Tot.Base.op_At @u0 @x1 @x2 @x3))
    :qid typing_FStar.List.Tot.Base.op_At))
  :named typing_FStar.List.Tot.Base.op_At))
; free var typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (HasType Prims.bool Prims.eqtype) :named typing_Prims.bool))
; free var typing
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Prims.eqtype (Tm_type (U_succ U_zero))) :named typing_Prims.eqtype))
; free var typing
;;; Fact-ids: Name Prims.hasEq; Namespace Prims
(assert
 (! ;; def=Prims.fst(77,5-77,10); use=Prims.fst(77,5-77,10)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.hasEq @u0 @x1) (Tm_type U_zero)))
    :pattern ((Prims.hasEq @u0 @x1))
    :qid typing_Prims.hasEq))
  :named typing_Prims.hasEq))
; free var typing
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (HasType Prims.l_True Prims.logical) :named typing_Prims.l_True))
; free var typing
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (HasType Prims.logical (Tm_type (U_succ U_zero))) :named typing_Prims.logical))
; free var typing
;;; Fact-ids: Name Prims.pure_post; Namespace Prims
(assert
 (! ;; def=Prims.fst(324,4-324,13); use=Prims.fst(324,4-324,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies
     (HasType @x1 (Tm_type @u0))
     (HasType (Prims.pure_post @u0 @x1) (Tm_type (U_max (U_succ U_zero) @u0))))
    :pattern ((Prims.pure_post @u0 @x1))
    :qid typing_Prims.pure_post))
  :named typing_Prims.pure_post))
; free var typing
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,4-323,14); use=Prims.fst(323,4-323,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
     (HasType (Prims.pure_post_ @u0 @u1 @x2 @x3) (Tm_type (U_max (U_succ U_zero) @u0))))
    :pattern ((Prims.pure_post_ @u0 @u1 @x2 @x3))
    :qid typing_Prims.pure_post_))
  :named typing_Prims.pure_post_))
; free var typing
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,5-125,11); use=Prims.fst(125,5-125,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.squash @u0 @x1) (Tm_type U_zero)))
    :pattern ((Prims.squash @u0 @x1))
    :qid typing_Prims.squash))
  :named typing_Prims.squash))
; free var typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Prims.unit Prims.eqtype) :named typing_Prims.unit))
; free var typing
;;; Fact-ids: Name Prims.uu___is_Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (Prims.list @u0 @x1)))
     (HasType (Prims.uu___is_Cons @u0 @x1 @x2) Prims.bool))
    :pattern ((Prims.uu___is_Cons @u0 @x1 @x2))
    :qid typing_Prims.uu___is_Cons))
  :named typing_Prims.uu___is_Cons))
; free var typing
;;; Fact-ids: Name Prims.uu___is_Nil; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (Prims.list @u0 @x1)))
     (HasType (Prims.uu___is_Nil @u0 @x1 @x2) Prims.bool))
    :pattern ((Prims.uu___is_Nil @u0 @x1 @x2))
    :qid typing_Prims.uu___is_Nil))
  :named typing_Prims.uu___is_Nil))
; Range_const typing
;;; Fact-ids: Name FStar.Range.range; Namespace FStar.Range
(assert
 (! (HasTypeZ (Range_const 1) FStar.Range.range) :named typing_range_const))
; typing for data constructor proxy
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (HasType Prims.T@tok Prims.trivial) :named typing_tok_Prims.T@tok))
; unit inversion
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.unit) (= @x1 Tm_unit))
    :pattern ((HasTypeFuel @u0 @x1 Prims.unit))
    :qid unit_inversion))
  :named unit_inversion))
; unit typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Tm_unit Prims.unit) :named unit_typing))
(push) ;; push{2
; universe local constant
(declare-fun uu___441 () Universe)
; a : Type (Type)
(declare-fun x_f6d6e3dd362b864379d85995f884953b_1 () Term)
; binder_x_f6d6e3dd362b864379d85995f884953b_1
;;; Fact-ids: 
(assert
 (! (HasType x_f6d6e3dd362b864379d85995f884953b_1 (Tm_type uu___441))
  :named binder_x_f6d6e3dd362b864379d85995f884953b_1))
; xs : Prims.list a (Prims.list a)
(declare-fun x_21cade6fedb88e0cfbdb7b541f900859_2 () Term)
; binder_x_21cade6fedb88e0cfbdb7b541f900859_2
;;; Fact-ids: 
(assert
 (! (HasType
   x_21cade6fedb88e0cfbdb7b541f900859_2
   (Prims.list uu___441 x_f6d6e3dd362b864379d85995f884953b_1))
  :named binder_x_21cade6fedb88e0cfbdb7b541f900859_2))
; Uninterpreted function symbol for impure function
(declare-fun M02_Types.Monad.append_nil_right (Universe Term Term) Term)
; Uninterpreted name for impure function
(declare-fun M02_Types.Monad.append_nil_right@tok (Universe) Term)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (p: Prims.pure_post Prims.unit).
;   (forall (pure_result: Prims.unit). xs @ [] == xs ==> p pure_result) ==>
;   (forall (k: Prims.pure_post Prims.unit).
;       (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x) ==>
;       (~(Nil? xs) /\ ~(Cons? xs) ==> Prims.l_False) /\
;       (xs == [] ==> (forall (any_result: Prims.unit). k any_result)) /\
;       (~(Nil? xs) ==>
;         (forall (b: a) (b: Prims.list a).
;             xs == b :: b ==>
;             b << xs /\
;             (forall (any_result: Prims.list a).
;                 b == any_result ==>
;                 (forall (pure_result: Prims.unit). b @ [] == b ==> k pure_result)))))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec append_nil_right`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   ;; def=M02_Types.Monad.fst(27,4-29,34); use=M02_Types.Monad.fst(27,4-29,34)
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(27,4-29,34)
       (forall ((@x1 Term))
        (! (implies
          (and
           (or label_1 (HasType @x1 Prims.unit))
           ;; def=M02_Types.Monad.fst(26,12-26,27); use=M02_Types.Monad.fst(27,4-29,34)
           (or
            label_2
            ;; def=M02_Types.Monad.fst(26,12-26,27); use=M02_Types.Monad.fst(27,4-29,34)
            (=
             (FStar.List.Tot.Base.op_At
              uu___441
              x_f6d6e3dd362b864379d85995f884953b_1
              x_21cade6fedb88e0cfbdb7b541f900859_2
              (Prims.Nil uu___441 x_f6d6e3dd362b864379d85995f884953b_1))
             x_21cade6fedb88e0cfbdb7b541f900859_2)))
          ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(27,4-29,34)
          (Valid
           ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(27,4-29,34)
           (ApplyTT @x0 @x1)))
         :pattern
          (;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(27,4-29,34)
           (Valid
            ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(27,4-29,34)
            (ApplyTT @x0 @x1)))
         :qid @query.1)))
      ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(27,4-29,34)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 (Prims.pure_post U_zero Prims.unit))
          ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(27,4-29,34)
          (forall ((@x2 Term))
           (! (implies
             ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(27,4-29,34)
             (Valid
              ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(27,4-29,34)
              (ApplyTT @x0 @x2))
             ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(27,4-29,34)
             (Valid
              ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(27,4-29,34)
              (ApplyTT @x1 @x2)))
            :weight 0
            :pattern ((ApplyTT @x1 @x2))
            :qid @query.3)))
         ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(27,4-29,34)
         (and
          (implies
           ;; def=M02_Types.Monad.fst(25,36-25,38); use=M02_Types.Monad.fst(27,10-27,12)
           (and
            ;; def=M02_Types.Monad.fst(25,36-25,38); use=M02_Types.Monad.fst(27,10-27,12)
            (not
             ;; def=M02_Types.Monad.fst(25,36-25,38); use=M02_Types.Monad.fst(27,10-27,12)
             (BoxBool_proj_0
              (Prims.uu___is_Nil
               uu___441
               x_f6d6e3dd362b864379d85995f884953b_1
               x_21cade6fedb88e0cfbdb7b541f900859_2)))
            ;; def=M02_Types.Monad.fst(25,36-25,38); use=M02_Types.Monad.fst(27,10-27,12)
            (not
             ;; def=M02_Types.Monad.fst(25,36-25,38); use=M02_Types.Monad.fst(27,10-27,12)
             (BoxBool_proj_0
              (Prims.uu___is_Cons
               uu___441
               x_f6d6e3dd362b864379d85995f884953b_1
               x_21cade6fedb88e0cfbdb7b541f900859_2))))
           label_3)
          (implies
           ;; def=M02_Types.Monad.fst(25,36-28,8); use=M02_Types.Monad.fst(27,10-28,8)
           (=
            x_21cade6fedb88e0cfbdb7b541f900859_2
            (Prims.Nil uu___441 x_f6d6e3dd362b864379d85995f884953b_1))
           ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(27,4-29,34)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 Prims.unit)
              ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(27,4-29,34)
              (Valid
               ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(27,4-29,34)
               (ApplyTT @x1 @x2)))
             :qid @query.4)))
          (implies
           ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(27,4-29,34)
           (not
            ;; def=M02_Types.Monad.fst(25,36-25,38); use=M02_Types.Monad.fst(27,10-27,12)
            (BoxBool_proj_0
             (Prims.uu___is_Nil
              uu___441
              x_f6d6e3dd362b864379d85995f884953b_1
              x_21cade6fedb88e0cfbdb7b541f900859_2)))
           ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(27,4-29,34)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 x_f6d6e3dd362b864379d85995f884953b_1)
              ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(27,4-29,34)
              (forall ((@x3 Term))
               (! (implies
                 (and
                  (HasType @x3 (Prims.list uu___441 x_f6d6e3dd362b864379d85995f884953b_1))
                  ;; def=M02_Types.Monad.fst(25,36-29,11); use=M02_Types.Monad.fst(27,10-29,11)
                  (=
                   x_21cade6fedb88e0cfbdb7b541f900859_2
                   (Prims.Cons uu___441 x_f6d6e3dd362b864379d85995f884953b_1 @x2 @x3)))
                 ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(27,4-29,34)
                 (and
                  ;; def=M02_Types.Monad.fst(27,4-29,34); use=M02_Types.Monad.fst(29,32-29,34)
                  (or
                   label_4
                   ;; def=M02_Types.Monad.fst(27,4-29,34); use=M02_Types.Monad.fst(29,32-29,34)
                   (Valid
                    ;; def=M02_Types.Monad.fst(27,4-29,34); use=M02_Types.Monad.fst(29,32-29,34)
                    (Prims.precedes
                     uu___441
                     uu___441
                     (Prims.list uu___441 x_f6d6e3dd362b864379d85995f884953b_1)
                     (Prims.list uu___441 x_f6d6e3dd362b864379d85995f884953b_1)
                     @x3
                     x_21cade6fedb88e0cfbdb7b541f900859_2)))
                  ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(27,4-29,34)
                  (forall ((@x4 Term))
                   (! (implies
                     (and
                      (HasType @x4 (Prims.list uu___441 x_f6d6e3dd362b864379d85995f884953b_1))
                      ;; def=M02_Types.Monad.fst(25,36-29,11); use=M02_Types.Monad.fst(27,4-29,34)
                      (= @x3 @x4))
                     ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(29,15-29,31)
                     (forall ((@x5 Term))
                      (! (implies
                        (and
                         (HasType @x5 Prims.unit)
                         ;; def=M02_Types.Monad.fst(26,12-26,27); use=M02_Types.Monad.fst(29,15-29,31)
                         (=
                          (FStar.List.Tot.Base.op_At
                           uu___441
                           x_f6d6e3dd362b864379d85995f884953b_1
                           @x3
                           (Prims.Nil uu___441 x_f6d6e3dd362b864379d85995f884953b_1))
                          @x3))
                        ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(29,15-29,31)
                        (Valid
                         ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(29,15-29,31)
                         (ApplyTT @x1 @x5)))
                       :qid @query.8)))
                    :qid @query.7))))
                :qid @query.6)))
             :qid @query.5)))))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.append_nil_right, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(declare-fun FStar.List.Tot.Base.concatMap (Universe Universe Term Term Term Term) Term)
; Fuel-instrumented function name
(declare-fun
 FStar.List.Tot.Base.concatMap.fuel_instrumented
 (Fuel Universe Universe Term Term Term Term)
 Term)
(declare-fun Tm_arrow_830e60c453fadc3a1c96c0feaf194486 (Term Universe Term Universe) Term)
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(176,8-176,17); use=FStar.List.Tot.Base.fst(176,8-176,17)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (=
     (FStar.List.Tot.Base.concatMap @u0 @u1 @x2 @x3 @x4 @x5)
     (FStar.List.Tot.Base.concatMap.fuel_instrumented MaxFuel @u0 @u1 @x2 @x3 @x4 @x5))
    :pattern ((FStar.List.Tot.Base.concatMap @u0 @u1 @x2 @x3 @x4 @x5))
    :qid @fuel_correspondence_FStar.List.Tot.Base.concatMap.fuel_instrumented))
  :named @fuel_correspondence_FStar.List.Tot.Base.concatMap.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(176,8-176,17); use=FStar.List.Tot.Base.fst(176,8-176,17)
  (forall ((@u0 Fuel) (@u1 Universe) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (=
     (FStar.List.Tot.Base.concatMap.fuel_instrumented (SFuel @u0) @u1 @u2 @x3 @x4 @x5 @x6)
     (FStar.List.Tot.Base.concatMap.fuel_instrumented ZFuel @u1 @u2 @x3 @x4 @x5 @x6))
    :pattern ((FStar.List.Tot.Base.concatMap.fuel_instrumented (SFuel @u0) @u1 @u2 @x3 @x4 @x5 @x6))
    :qid @fuel_irrelevance_FStar.List.Tot.Base.concatMap.fuel_instrumented))
  :named @fuel_irrelevance_FStar.List.Tot.Base.concatMap.fuel_instrumented))
; interpretation_Tm_arrow_830e60c453fadc3a1c96c0feaf194486
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(175,26-176,19); use=FStar.List.Tot.Base.fst(176,8-176,19)
  (forall ((@x0 Term) (@x1 Term) (@u2 Universe) (@x3 Term) (@u4 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x1 @u2 @x3 @u4))
     (and
      ;; def=FStar.List.Tot.Base.fst(175,26-176,19); use=FStar.List.Tot.Base.fst(176,8-176,19)
      (forall ((@x5 Term))
       (! (implies (HasType @x5 @x1) (HasType (ApplyTT @x0 @x5) (Prims.list @u2 @x3)))
        :pattern ((ApplyTT @x0 @x5))
        :qid FStar.List.Tot.Base_interpretation_Tm_arrow_830e60c453fadc3a1c96c0feaf194486.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x1 @u2 @x3 @u4)))
    :qid FStar.List.Tot.Base_interpretation_Tm_arrow_830e60c453fadc3a1c96c0feaf194486))
  :named FStar.List.Tot.Base_interpretation_Tm_arrow_830e60c453fadc3a1c96c0feaf194486))
; pre-typing for functions
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(175,26-176,19); use=FStar.List.Tot.Base.fst(176,8-176,19)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@u3 Universe) (@x4 Term) (@u5 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x2 @u3 @x4 @u5))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x2 @u3 @x4 @u5)))
    :qid FStar.List.Tot.Base_pre_typing_Tm_arrow_830e60c453fadc3a1c96c0feaf194486))
  :named FStar.List.Tot.Base_pre_typing_Tm_arrow_830e60c453fadc3a1c96c0feaf194486))
; Equation for fuel-instrumented recursive function: FStar.List.Tot.Base.concatMap
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(176,8-176,17); use=FStar.List.Tot.Base.fst(176,8-176,17)
  (forall ((@u0 Fuel) (@u1 Universe) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (implies
     (and
      (HasType @x3 (Tm_type @u1))
      (HasType @x4 (Tm_type @u2))
      (HasType @x5 (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x3 @u2 @x4 @u1))
      (HasType @x6 (Prims.list @u1 @x3)))
     (=
      (FStar.List.Tot.Base.concatMap.fuel_instrumented (SFuel @u0) @u1 @u2 @x3 @x4 @x5 @x6)
      (let ((@lb7 @x6))
       (ite
        (is-Prims.Nil @lb7)
        (Prims.Nil @u2 @x4)
        (ite
         (is-Prims.Cons @lb7)
         (FStar.List.Tot.Base.append
          @u2
          @x4
          (ApplyTT @x5 (Prims.Cons_@hd @lb7))
          (FStar.List.Tot.Base.concatMap.fuel_instrumented
           @u0
           @u1
           @u2
           @x3
           @x4
           @x5
           (Prims.Cons_@tl @lb7)))
         Tm_unit)))))
    :weight 0
    :pattern ((FStar.List.Tot.Base.concatMap.fuel_instrumented (SFuel @u0) @u1 @u2 @x3 @x4 @x5 @x6))
    :qid equation_with_fuel_FStar.List.Tot.Base.concatMap.fuel_instrumented))
  :named equation_with_fuel_FStar.List.Tot.Base.concatMap.fuel_instrumented))
; kinding_Tm_arrow_830e60c453fadc3a1c96c0feaf194486
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(175,26-176,19); use=FStar.List.Tot.Base.fst(176,8-176,19)
  (forall ((@x0 Term) (@u1 Universe) (@x2 Term) (@u3 Universe))
   (! (HasType (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x0 @u1 @x2 @u3) (Tm_type (U_max @u1 @u3)))
    :pattern
     ((HasType (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x0 @u1 @x2 @u3) (Tm_type (U_max @u1 @u3))))
    :qid kinding_Tm_arrow_830e60c453fadc3a1c96c0feaf194486))
  :named kinding_Tm_arrow_830e60c453fadc3a1c96c0feaf194486))
; Typing correspondence of token to term
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(176,8-176,17); use=FStar.List.Tot.Base.fst(176,8-176,17)
  (forall ((@u0 Fuel) (@u1 Universe) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (implies
     (and
      (HasType @x3 (Tm_type @u1))
      (HasType @x4 (Tm_type @u2))
      (HasType @x5 (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x3 @u2 @x4 @u1))
      (HasType @x6 (Prims.list @u1 @x3)))
     (HasType
      (FStar.List.Tot.Base.concatMap.fuel_instrumented @u0 @u1 @u2 @x3 @x4 @x5 @x6)
      (Prims.list @u2 @x4)))
    :pattern ((FStar.List.Tot.Base.concatMap.fuel_instrumented @u0 @u1 @u2 @x3 @x4 @x5 @x6))
    :qid token_correspondence_FStar.List.Tot.Base.concatMap.fuel_instrumented))
  :named token_correspondence_FStar.List.Tot.Base.concatMap.fuel_instrumented))
; free var typing
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(176,8-176,17); use=FStar.List.Tot.Base.fst(176,8-176,17)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (and
      (HasType @x2 (Tm_type @u0))
      (HasType @x3 (Tm_type @u1))
      (HasType @x4 (Tm_arrow_830e60c453fadc3a1c96c0feaf194486 @x2 @u1 @x3 @u0))
      (HasType @x5 (Prims.list @u0 @x2)))
     (HasType (FStar.List.Tot.Base.concatMap @u0 @u1 @x2 @x3 @x4 @x5) (Prims.list @u1 @x3)))
    :pattern ((FStar.List.Tot.Base.concatMap @u0 @u1 @x2 @x3 @x4 @x5))
    :qid typing_FStar.List.Tot.Base.concatMap))
  :named typing_FStar.List.Tot.Base.concatMap))
(push) ;; push{2
; universe local constant
(declare-fun uu___523 () Universe)
; a : Type (Type)
(declare-fun x_1df73c8043d65092ff6c7956162b704a_1 () Term)
; binder_x_1df73c8043d65092ff6c7956162b704a_1
;;; Fact-ids: 
(assert
 (! (HasType x_1df73c8043d65092ff6c7956162b704a_1 (Tm_type uu___523))
  :named binder_x_1df73c8043d65092ff6c7956162b704a_1))
; xs : Prims.list a (Prims.list a)
(declare-fun x_58fd26403d5f1d8aa429226dab62bc6a_2 () Term)
; binder_x_58fd26403d5f1d8aa429226dab62bc6a_2
;;; Fact-ids: 
(assert
 (! (HasType
   x_58fd26403d5f1d8aa429226dab62bc6a_2
   (Prims.list uu___523 x_1df73c8043d65092ff6c7956162b704a_1))
  :named binder_x_58fd26403d5f1d8aa429226dab62bc6a_2))
; Uninterpreted function symbol for impure function
(declare-fun M02_Types.Monad.concatMap_return (Universe Term Term) Term)
; Uninterpreted name for impure function
(declare-fun M02_Types.Monad.concatMap_return@tok (Universe) Term)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
; x: a -> Prims.list a
(declare-fun Tm_arrow_fdafca60b26997323f38c79f2d69a44e (Universe) Term)
; kinding_Tm_arrow_fdafca60b26997323f38c79f2d69a44e
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(31,27-31,28); use=M02_Types.Monad.fst(31,44-35,31)
  (forall ((@u0 Universe))
   (! (HasType (Tm_arrow_fdafca60b26997323f38c79f2d69a44e @u0) (Tm_type @u0))
    :pattern ((HasType (Tm_arrow_fdafca60b26997323f38c79f2d69a44e @u0) (Tm_type @u0)))
    :qid kinding_Tm_arrow_fdafca60b26997323f38c79f2d69a44e))
  :named kinding_Tm_arrow_fdafca60b26997323f38c79f2d69a44e))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(31,27-31,28); use=M02_Types.Monad.fst(31,44-35,31)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_fdafca60b26997323f38c79f2d69a44e @u2))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_fdafca60b26997323f38c79f2d69a44e @u2)))
    :qid M02_Types.Monad_pre_typing_Tm_arrow_fdafca60b26997323f38c79f2d69a44e))
  :named M02_Types.Monad_pre_typing_Tm_arrow_fdafca60b26997323f38c79f2d69a44e))
; interpretation_Tm_arrow_fdafca60b26997323f38c79f2d69a44e
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(31,27-31,28); use=M02_Types.Monad.fst(31,44-35,31)
  (forall ((@x0 Term) (@u1 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_fdafca60b26997323f38c79f2d69a44e @u1))
     (and
      ;; def=M02_Types.Monad.fst(31,27-31,28); use=M02_Types.Monad.fst(31,44-35,31)
      (forall ((@x2 Term))
       (! (implies
         (HasType @x2 x_1df73c8043d65092ff6c7956162b704a_1)
         (HasType (ApplyTT @x0 @x2) (Prims.list @u1 x_1df73c8043d65092ff6c7956162b704a_1)))
        :pattern ((ApplyTT @x0 @x2))
        :qid M02_Types.Monad_interpretation_Tm_arrow_fdafca60b26997323f38c79f2d69a44e.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_fdafca60b26997323f38c79f2d69a44e @u1)))
    :qid M02_Types.Monad_interpretation_Tm_arrow_fdafca60b26997323f38c79f2d69a44e))
  :named M02_Types.Monad_interpretation_Tm_arrow_fdafca60b26997323f38c79f2d69a44e))
(declare-fun Tm_abs_ce203169880f12f3056f409c7972746f (Universe) Term)
; typing_Tm_abs_ce203169880f12f3056f409c7972746f
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(32,33-32,36); use=M02_Types.Monad.fst(35,15-35,31)
  (forall ((@u0 Universe))
   (! (HasType
     (Tm_abs_ce203169880f12f3056f409c7972746f @u0)
     (Tm_arrow_fdafca60b26997323f38c79f2d69a44e @u0))
    :pattern ((Tm_abs_ce203169880f12f3056f409c7972746f @u0))
    :qid typing_Tm_abs_ce203169880f12f3056f409c7972746f))
  :named typing_Tm_abs_ce203169880f12f3056f409c7972746f))
; interpretation_Tm_abs_ce203169880f12f3056f409c7972746f
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(32,33-32,36); use=M02_Types.Monad.fst(35,15-35,31)
  (forall ((@x0 Term) (@u1 Universe))
   (! (=
     (ApplyTT (Tm_abs_ce203169880f12f3056f409c7972746f @u1) @x0)
     (Prims.Cons
      @u1
      x_1df73c8043d65092ff6c7956162b704a_1
      @x0
      (Prims.Nil @u1 x_1df73c8043d65092ff6c7956162b704a_1)))
    :pattern ((ApplyTT (Tm_abs_ce203169880f12f3056f409c7972746f @u1) @x0))
    :qid interpretation_Tm_abs_ce203169880f12f3056f409c7972746f))
  :named interpretation_Tm_abs_ce203169880f12f3056f409c7972746f))


; Encoding query formula : forall (p: Prims.pure_post Prims.unit).
;   (forall (pure_result: Prims.unit).
;       FStar.List.Tot.Base.concatMap (fun x -> [x]) xs == xs ==> p pure_result) ==>
;   (forall (k: Prims.pure_post Prims.unit).
;       (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x) ==>
;       (~(Nil? xs) /\ ~(Cons? xs) ==> Prims.l_False) /\
;       (xs == [] ==> (forall (any_result: Prims.unit). k any_result)) /\
;       (~(Nil? xs) ==>
;         (forall (b: a) (b: Prims.list a).
;             xs == b :: b ==>
;             b << xs /\
;             (forall (any_result: Prims.list a).
;                 b == any_result ==>
;                 (forall (pure_result: Prims.unit).
;                     FStar.List.Tot.Base.concatMap (fun x -> [x]) b == b ==> k pure_result)))))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec concatMap_return`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   ;; def=M02_Types.Monad.fst(33,4-35,34); use=M02_Types.Monad.fst(33,4-35,34)
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(33,4-35,34)
       (forall ((@x1 Term))
        (! (implies
          (and
           (or label_1 (HasType @x1 Prims.unit))
           ;; def=M02_Types.Monad.fst(32,12-32,47); use=M02_Types.Monad.fst(33,4-35,34)
           (or
            label_2
            ;; def=M02_Types.Monad.fst(32,12-32,47); use=M02_Types.Monad.fst(33,4-35,34)
            (=
             (FStar.List.Tot.Base.concatMap
              uu___523
              uu___523
              x_1df73c8043d65092ff6c7956162b704a_1
              x_1df73c8043d65092ff6c7956162b704a_1
              (Tm_abs_ce203169880f12f3056f409c7972746f uu___523)
              x_58fd26403d5f1d8aa429226dab62bc6a_2)
             x_58fd26403d5f1d8aa429226dab62bc6a_2)))
          ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(33,4-35,34)
          (Valid
           ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(33,4-35,34)
           (ApplyTT @x0 @x1)))
         :pattern
          (;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(33,4-35,34)
           (Valid
            ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(33,4-35,34)
            (ApplyTT @x0 @x1)))
         :qid @query.1)))
      ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(33,4-35,34)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 (Prims.pure_post U_zero Prims.unit))
          ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(33,4-35,34)
          (forall ((@x2 Term))
           (! (implies
             ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(33,4-35,34)
             (Valid
              ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(33,4-35,34)
              (ApplyTT @x0 @x2))
             ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(33,4-35,34)
             (Valid
              ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(33,4-35,34)
              (ApplyTT @x1 @x2)))
            :weight 0
            :pattern ((ApplyTT @x1 @x2))
            :qid @query.3)))
         ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(33,4-35,34)
         (and
          (implies
           ;; def=M02_Types.Monad.fst(31,36-31,38); use=M02_Types.Monad.fst(33,10-33,12)
           (and
            ;; def=M02_Types.Monad.fst(31,36-31,38); use=M02_Types.Monad.fst(33,10-33,12)
            (not
             ;; def=M02_Types.Monad.fst(31,36-31,38); use=M02_Types.Monad.fst(33,10-33,12)
             (BoxBool_proj_0
              (Prims.uu___is_Nil
               uu___523
               x_1df73c8043d65092ff6c7956162b704a_1
               x_58fd26403d5f1d8aa429226dab62bc6a_2)))
            ;; def=M02_Types.Monad.fst(31,36-31,38); use=M02_Types.Monad.fst(33,10-33,12)
            (not
             ;; def=M02_Types.Monad.fst(31,36-31,38); use=M02_Types.Monad.fst(33,10-33,12)
             (BoxBool_proj_0
              (Prims.uu___is_Cons
               uu___523
               x_1df73c8043d65092ff6c7956162b704a_1
               x_58fd26403d5f1d8aa429226dab62bc6a_2))))
           label_3)
          (implies
           ;; def=M02_Types.Monad.fst(31,36-34,8); use=M02_Types.Monad.fst(33,10-34,8)
           (=
            x_58fd26403d5f1d8aa429226dab62bc6a_2
            (Prims.Nil uu___523 x_1df73c8043d65092ff6c7956162b704a_1))
           ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(33,4-35,34)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 Prims.unit)
              ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(33,4-35,34)
              (Valid
               ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(33,4-35,34)
               (ApplyTT @x1 @x2)))
             :qid @query.4)))
          (implies
           ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(33,4-35,34)
           (not
            ;; def=M02_Types.Monad.fst(31,36-31,38); use=M02_Types.Monad.fst(33,10-33,12)
            (BoxBool_proj_0
             (Prims.uu___is_Nil
              uu___523
              x_1df73c8043d65092ff6c7956162b704a_1
              x_58fd26403d5f1d8aa429226dab62bc6a_2)))
           ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(33,4-35,34)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 x_1df73c8043d65092ff6c7956162b704a_1)
              ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(33,4-35,34)
              (forall ((@x3 Term))
               (! (implies
                 (and
                  (HasType @x3 (Prims.list uu___523 x_1df73c8043d65092ff6c7956162b704a_1))
                  ;; def=M02_Types.Monad.fst(31,36-35,11); use=M02_Types.Monad.fst(33,10-35,11)
                  (=
                   x_58fd26403d5f1d8aa429226dab62bc6a_2
                   (Prims.Cons uu___523 x_1df73c8043d65092ff6c7956162b704a_1 @x2 @x3)))
                 ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(33,4-35,34)
                 (and
                  ;; def=M02_Types.Monad.fst(33,4-35,34); use=M02_Types.Monad.fst(35,32-35,34)
                  (or
                   label_4
                   ;; def=M02_Types.Monad.fst(33,4-35,34); use=M02_Types.Monad.fst(35,32-35,34)
                   (Valid
                    ;; def=M02_Types.Monad.fst(33,4-35,34); use=M02_Types.Monad.fst(35,32-35,34)
                    (Prims.precedes
                     uu___523
                     uu___523
                     (Prims.list uu___523 x_1df73c8043d65092ff6c7956162b704a_1)
                     (Prims.list uu___523 x_1df73c8043d65092ff6c7956162b704a_1)
                     @x3
                     x_58fd26403d5f1d8aa429226dab62bc6a_2)))
                  ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(33,4-35,34)
                  (forall ((@x4 Term))
                   (! (implies
                     (and
                      (HasType @x4 (Prims.list uu___523 x_1df73c8043d65092ff6c7956162b704a_1))
                      ;; def=M02_Types.Monad.fst(31,36-35,11); use=M02_Types.Monad.fst(33,4-35,34)
                      (= @x3 @x4))
                     ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(35,15-35,31)
                     (forall ((@x5 Term))
                      (! (implies
                        (and
                         (HasType @x5 Prims.unit)
                         ;; def=M02_Types.Monad.fst(32,12-32,47); use=M02_Types.Monad.fst(35,15-35,31)
                         (=
                          (FStar.List.Tot.Base.concatMap
                           uu___523
                           uu___523
                           x_1df73c8043d65092ff6c7956162b704a_1
                           x_1df73c8043d65092ff6c7956162b704a_1
                           (Tm_abs_ce203169880f12f3056f409c7972746f uu___523)
                           @x3)
                          @x3))
                        ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(35,15-35,31)
                        (Valid
                         ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(35,15-35,31)
                         (ApplyTT @x1 @x5)))
                       :qid @query.8)))
                    :qid @query.7))))
                :qid @query.6)))
             :qid @query.5)))))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.concatMap_return, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(declare-fun Prims.op_Equals_Equals_Equals (Universe Term Term Term Term) Term)
; Equation for Prims.op_Equals_Equals_Equals
;;; Fact-ids: Name Prims.op_Equals_Equals_Equals; Namespace Prims
(assert
 (! ;; def=Prims.fst(506,6-506,9); use=Prims.fst(506,6-506,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (=
     (Valid (Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4))
     ;; def=Prims.fst(506,52-506,68); use=Prims.fst(506,52-506,68)
     (and
      ;; def=Prims.fst(506,52-506,58); use=Prims.fst(506,52-506,58)
      (= @x1 @x2)
      ;; def=Prims.fst(506,62-506,68); use=Prims.fst(506,62-506,68)
      (= @x3 @x4)))
    :pattern ((Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4))
    :qid equation_Prims.op_Equals_Equals_Equals))
  :named equation_Prims.op_Equals_Equals_Equals))
; free var typing
;;; Fact-ids: Name Prims.op_Equals_Equals_Equals; Namespace Prims
(assert
 (! ;; def=Prims.fst(506,6-506,9); use=Prims.fst(506,6-506,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_type @u0))
      (HasType @x3 @x1)
      (HasType @x4 @x2))
     (HasType (Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4) Prims.logical))
    :pattern ((Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4))
    :qid typing_Prims.op_Equals_Equals_Equals))
  :named typing_Prims.op_Equals_Equals_Equals))
(push) ;; push{2
; universe local constant
(declare-fun uu___969 () Universe)
; a : Type (Type)
(declare-fun x_ee8597c08478dd72d93699fbdf1fd60e_1 () Term)
; binder_x_ee8597c08478dd72d93699fbdf1fd60e_1
;;; Fact-ids: 
(assert
 (! (HasType x_ee8597c08478dd72d93699fbdf1fd60e_1 (Tm_type uu___969))
  :named binder_x_ee8597c08478dd72d93699fbdf1fd60e_1))
; xs : Prims.list a (Prims.list a)
(declare-fun x_480c6d02be79c5e13227ac553f0b18e2_2 () Term)
; binder_x_480c6d02be79c5e13227ac553f0b18e2_2
;;; Fact-ids: 
(assert
 (! (HasType
   x_480c6d02be79c5e13227ac553f0b18e2_2
   (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1))
  :named binder_x_480c6d02be79c5e13227ac553f0b18e2_2))
; ys : Prims.list a (Prims.list a)
(declare-fun x_480c6d02be79c5e13227ac553f0b18e2_3 () Term)
; binder_x_480c6d02be79c5e13227ac553f0b18e2_3
;;; Fact-ids: 
(assert
 (! (HasType
   x_480c6d02be79c5e13227ac553f0b18e2_3
   (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1))
  :named binder_x_480c6d02be79c5e13227ac553f0b18e2_3))
; zs : Prims.list a (Prims.list a)
(declare-fun x_480c6d02be79c5e13227ac553f0b18e2_4 () Term)
; binder_x_480c6d02be79c5e13227ac553f0b18e2_4
;;; Fact-ids: 
(assert
 (! (HasType
   x_480c6d02be79c5e13227ac553f0b18e2_4
   (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1))
  :named binder_x_480c6d02be79c5e13227ac553f0b18e2_4))
; Uninterpreted function symbol for impure function
(declare-fun M02_Types.Monad.append_assoc (Universe Term Term Term Term) Term)
; Uninterpreted name for impure function
(declare-fun M02_Types.Monad.append_assoc@tok (Universe) Term)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (p: Prims.pure_post Prims.unit).
;   (forall (pure_result: Prims.unit). (xs @ ys) @ zs == xs @ ys @ zs ==> p pure_result) ==>
;   (forall (k: Prims.pure_post Prims.unit).
;       (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x) ==>
;       (~(Nil? xs) /\ ~(Cons? xs) ==> Prims.l_False) /\
;       (xs == [] ==> (forall (any_result: Prims.unit). k any_result)) /\
;       (~(Nil? xs) ==>
;         (forall (b: a) (b: Prims.list a).
;             xs == b :: b ==>
;             (b << xs \/ b === xs /\ (ys << ys \/ zs << zs)) /\
;             (forall (any_result: Prims.list a).
;                 zs == any_result ==>
;                 (forall (pure_result: Prims.unit). (b @ ys) @ zs == b @ ys @ zs ==> k pure_result)))
;       ))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec append_assoc`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   ;; def=M02_Types.Monad.fst(40,4-42,39); use=M02_Types.Monad.fst(40,4-42,39)
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(40,4-42,39)
       (forall ((@x1 Term))
        (! (implies
          (and
           (or label_1 (HasType @x1 Prims.unit))
           ;; def=M02_Types.Monad.fst(39,12-39,46); use=M02_Types.Monad.fst(40,4-42,39)
           (or
            label_2
            ;; def=M02_Types.Monad.fst(39,12-39,46); use=M02_Types.Monad.fst(40,4-42,39)
            (=
             (FStar.List.Tot.Base.op_At
              uu___969
              x_ee8597c08478dd72d93699fbdf1fd60e_1
              (FStar.List.Tot.Base.op_At
               uu___969
               x_ee8597c08478dd72d93699fbdf1fd60e_1
               x_480c6d02be79c5e13227ac553f0b18e2_2
               x_480c6d02be79c5e13227ac553f0b18e2_3)
              x_480c6d02be79c5e13227ac553f0b18e2_4)
             (FStar.List.Tot.Base.op_At
              uu___969
              x_ee8597c08478dd72d93699fbdf1fd60e_1
              x_480c6d02be79c5e13227ac553f0b18e2_2
              (FStar.List.Tot.Base.op_At
               uu___969
               x_ee8597c08478dd72d93699fbdf1fd60e_1
               x_480c6d02be79c5e13227ac553f0b18e2_3
               x_480c6d02be79c5e13227ac553f0b18e2_4)))))
          ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(40,4-42,39)
          (Valid
           ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(40,4-42,39)
           (ApplyTT @x0 @x1)))
         :pattern
          (;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(40,4-42,39)
           (Valid
            ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(40,4-42,39)
            (ApplyTT @x0 @x1)))
         :qid @query.1)))
      ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(40,4-42,39)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 (Prims.pure_post U_zero Prims.unit))
          ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(40,4-42,39)
          (forall ((@x2 Term))
           (! (implies
             ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(40,4-42,39)
             (Valid
              ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(40,4-42,39)
              (ApplyTT @x0 @x2))
             ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(40,4-42,39)
             (Valid
              ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(40,4-42,39)
              (ApplyTT @x1 @x2)))
            :weight 0
            :pattern ((ApplyTT @x1 @x2))
            :qid @query.3)))
         ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(40,4-42,39)
         (and
          (implies
           ;; def=M02_Types.Monad.fst(38,32-38,34); use=M02_Types.Monad.fst(40,10-40,12)
           (and
            ;; def=M02_Types.Monad.fst(38,32-38,34); use=M02_Types.Monad.fst(40,10-40,12)
            (not
             ;; def=M02_Types.Monad.fst(38,32-38,34); use=M02_Types.Monad.fst(40,10-40,12)
             (BoxBool_proj_0
              (Prims.uu___is_Nil
               uu___969
               x_ee8597c08478dd72d93699fbdf1fd60e_1
               x_480c6d02be79c5e13227ac553f0b18e2_2)))
            ;; def=M02_Types.Monad.fst(38,32-38,34); use=M02_Types.Monad.fst(40,10-40,12)
            (not
             ;; def=M02_Types.Monad.fst(38,32-38,34); use=M02_Types.Monad.fst(40,10-40,12)
             (BoxBool_proj_0
              (Prims.uu___is_Cons
               uu___969
               x_ee8597c08478dd72d93699fbdf1fd60e_1
               x_480c6d02be79c5e13227ac553f0b18e2_2))))
           label_3)
          (implies
           ;; def=M02_Types.Monad.fst(38,32-41,8); use=M02_Types.Monad.fst(40,10-41,8)
           (=
            x_480c6d02be79c5e13227ac553f0b18e2_2
            (Prims.Nil uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1))
           ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(40,4-42,39)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 Prims.unit)
              ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(40,4-42,39)
              (Valid
               ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(40,4-42,39)
               (ApplyTT @x1 @x2)))
             :qid @query.4)))
          (implies
           ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(40,4-42,39)
           (not
            ;; def=M02_Types.Monad.fst(38,32-38,34); use=M02_Types.Monad.fst(40,10-40,12)
            (BoxBool_proj_0
             (Prims.uu___is_Nil
              uu___969
              x_ee8597c08478dd72d93699fbdf1fd60e_1
              x_480c6d02be79c5e13227ac553f0b18e2_2)))
           ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(40,4-42,39)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 x_ee8597c08478dd72d93699fbdf1fd60e_1)
              ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(40,4-42,39)
              (forall ((@x3 Term))
               (! (implies
                 (and
                  (HasType @x3 (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1))
                  ;; def=M02_Types.Monad.fst(38,32-42,14); use=M02_Types.Monad.fst(40,10-42,14)
                  (=
                   x_480c6d02be79c5e13227ac553f0b18e2_2
                   (Prims.Cons uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1 @x2 @x3)))
                 ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(40,4-42,39)
                 (and
                  ;; def=M02_Types.Monad.fst(38,32-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                  (or
                   label_4
                   ;; def=M02_Types.Monad.fst(40,4-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                   (Valid
                    ;; def=M02_Types.Monad.fst(40,4-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                    (Prims.precedes
                     uu___969
                     uu___969
                     (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1)
                     (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1)
                     @x3
                     x_480c6d02be79c5e13227ac553f0b18e2_2))
                   ;; def=M02_Types.Monad.fst(38,32-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                   (and
                    ;; def=M02_Types.Monad.fst(38,32-38,34); use=M02_Types.Monad.fst(42,37-42,39)
                    (Valid
                     ;; def=M02_Types.Monad.fst(38,32-38,34); use=M02_Types.Monad.fst(42,37-42,39)
                     (Prims.op_Equals_Equals_Equals
                      uu___969
                      (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1)
                      (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1)
                      @x3
                      x_480c6d02be79c5e13227ac553f0b18e2_2))
                    ;; def=M02_Types.Monad.fst(38,35-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                    (or
                     ;; def=M02_Types.Monad.fst(40,4-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                     (Valid
                      ;; def=M02_Types.Monad.fst(40,4-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                      (Prims.precedes
                       uu___969
                       uu___969
                       (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1)
                       (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1)
                       x_480c6d02be79c5e13227ac553f0b18e2_3
                       x_480c6d02be79c5e13227ac553f0b18e2_3))
                     ;; def=M02_Types.Monad.fst(40,4-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                     (Valid
                      ;; def=M02_Types.Monad.fst(40,4-42,39); use=M02_Types.Monad.fst(42,37-42,39)
                      (Prims.precedes
                       uu___969
                       uu___969
                       (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1)
                       (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1)
                       x_480c6d02be79c5e13227ac553f0b18e2_4
                       x_480c6d02be79c5e13227ac553f0b18e2_4)))))
                  ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(40,4-42,39)
                  (forall ((@x4 Term))
                   (! (implies
                     (and
                      (HasType @x4 (Prims.list uu___969 x_ee8597c08478dd72d93699fbdf1fd60e_1))
                      ;; def=M02_Types.Monad.fst(38,38-38,40); use=M02_Types.Monad.fst(40,4-42,39)
                      (= x_480c6d02be79c5e13227ac553f0b18e2_4 @x4))
                     ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(42,18-42,30)
                     (forall ((@x5 Term))
                      (! (implies
                        (and
                         (HasType @x5 Prims.unit)
                         ;; def=M02_Types.Monad.fst(39,12-39,46); use=M02_Types.Monad.fst(42,18-42,30)
                         (=
                          (FStar.List.Tot.Base.op_At
                           uu___969
                           x_ee8597c08478dd72d93699fbdf1fd60e_1
                           (FStar.List.Tot.Base.op_At
                            uu___969
                            x_ee8597c08478dd72d93699fbdf1fd60e_1
                            @x3
                            x_480c6d02be79c5e13227ac553f0b18e2_3)
                           x_480c6d02be79c5e13227ac553f0b18e2_4)
                          (FStar.List.Tot.Base.op_At
                           uu___969
                           x_ee8597c08478dd72d93699fbdf1fd60e_1
                           @x3
                           (FStar.List.Tot.Base.op_At
                            uu___969
                            x_ee8597c08478dd72d93699fbdf1fd60e_1
                            x_480c6d02be79c5e13227ac553f0b18e2_3
                            x_480c6d02be79c5e13227ac553f0b18e2_4))))
                        ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(42,18-42,30)
                        (Valid
                         ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(42,18-42,30)
                         (ApplyTT @x1 @x5)))
                       :qid @query.8)))
                    :qid @query.7))))
                :qid @query.6)))
             :qid @query.5)))))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.append_assoc, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple3
 (Universe Universe Universe Term Term Term Term Term Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@0 (Term) Universe)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@1 (Term) Universe)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@2 (Term) Universe)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@_1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@_2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@_3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@_b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3_@_c (Term) Term)
; Constructor distinct
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (= 153 (Term_constr_id (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8)))
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid constructor_distinct_FStar.Pervasives.Native.Mktuple3))
  :named constructor_distinct_FStar.Pervasives.Native.Mktuple3))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@0
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @u0)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@0))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@0))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@1
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @u1)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@1))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@1))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@2
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @u2)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@2))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@2))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@_1
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @x6)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@_1))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@_1))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@_2
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @x7)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@_2))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@_2))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@_3
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @x8)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@_3))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@_3))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@_a
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @x3)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@_a))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@_a))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@_b
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @x4)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@_b))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@_b))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple3; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple3; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(65,25-65,33); use=FStar.Pervasives.Native.fst(65,25-65,33)
  (forall
    ((@u0 Universe)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple3_@_c
      (FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
     @x5)
    :pattern ((FStar.Pervasives.Native.Mktuple3 @u0 @u1 @u2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple3_@_c))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple3_@_c))
(push) ;; push{2
; universe local constant
(declare-fun uu___1124 () Universe)
; universe local constant
(declare-fun uu___1123 () Universe)
; a : Type (Type)
(declare-fun x_9ecc547c2c206cff31a29ddb75882a86_2 () Term)
; binder_x_9ecc547c2c206cff31a29ddb75882a86_2
;;; Fact-ids: 
(assert
 (! (HasType x_9ecc547c2c206cff31a29ddb75882a86_2 (Tm_type uu___1124))
  :named binder_x_9ecc547c2c206cff31a29ddb75882a86_2))
; b : Type (Type)
(declare-fun x_aeaaf64f60a07c3550d419f59cbfae4a_3 () Term)
; binder_x_aeaaf64f60a07c3550d419f59cbfae4a_3
;;; Fact-ids: 
(assert
 (! (HasType x_aeaaf64f60a07c3550d419f59cbfae4a_3 (Tm_type uu___1123))
  :named binder_x_aeaaf64f60a07c3550d419f59cbfae4a_3))
; xs : Prims.list a (Prims.list a)
(declare-fun x_d5bdb6b26cd2c11359d1f6510358cf74_4 () Term)
; binder_x_d5bdb6b26cd2c11359d1f6510358cf74_4
;;; Fact-ids: 
(assert
 (! (HasType
   x_d5bdb6b26cd2c11359d1f6510358cf74_4
   (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2))
  :named binder_x_d5bdb6b26cd2c11359d1f6510358cf74_4))
; ys : Prims.list a (Prims.list a)
(declare-fun x_d5bdb6b26cd2c11359d1f6510358cf74_5 () Term)
; binder_x_d5bdb6b26cd2c11359d1f6510358cf74_5
;;; Fact-ids: 
(assert
 (! (HasType
   x_d5bdb6b26cd2c11359d1f6510358cf74_5
   (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2))
  :named binder_x_d5bdb6b26cd2c11359d1f6510358cf74_5))
; f : _: a -> Prims.list b (_: a -> Prims.list b)
(declare-fun x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6 () Term)
; _: a -> Prims.list b
(declare-fun Tm_arrow_47d363f16725a9987dec964cd98a548c (Universe Universe) Term)
; kinding_Tm_arrow_47d363f16725a9987dec964cd98a548c
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(44,27-44,67); use=M02_Types.Monad.fst(44,56-44,67)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (HasType (Tm_arrow_47d363f16725a9987dec964cd98a548c @u0 @u1) (Tm_type (U_max @u0 @u1)))
    :pattern
     ((HasType (Tm_arrow_47d363f16725a9987dec964cd98a548c @u0 @u1) (Tm_type (U_max @u0 @u1))))
    :qid kinding_Tm_arrow_47d363f16725a9987dec964cd98a548c))
  :named kinding_Tm_arrow_47d363f16725a9987dec964cd98a548c))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(44,27-44,67); use=M02_Types.Monad.fst(44,56-44,67)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_47d363f16725a9987dec964cd98a548c @u2 @u3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_47d363f16725a9987dec964cd98a548c @u2 @u3)))
    :qid M02_Types.Monad_pre_typing_Tm_arrow_47d363f16725a9987dec964cd98a548c))
  :named M02_Types.Monad_pre_typing_Tm_arrow_47d363f16725a9987dec964cd98a548c))
; interpretation_Tm_arrow_47d363f16725a9987dec964cd98a548c
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(44,27-44,67); use=M02_Types.Monad.fst(44,56-44,67)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_47d363f16725a9987dec964cd98a548c @u1 @u2))
     (and
      ;; def=M02_Types.Monad.fst(44,27-44,67); use=M02_Types.Monad.fst(44,56-44,67)
      (forall ((@x3 Term))
       (! (implies
         (HasType @x3 x_9ecc547c2c206cff31a29ddb75882a86_2)
         (HasType (ApplyTT @x0 @x3) (Prims.list @u1 x_aeaaf64f60a07c3550d419f59cbfae4a_3)))
        :pattern ((ApplyTT @x0 @x3))
        :qid M02_Types.Monad_interpretation_Tm_arrow_47d363f16725a9987dec964cd98a548c.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_47d363f16725a9987dec964cd98a548c @u1 @u2)))
    :qid M02_Types.Monad_interpretation_Tm_arrow_47d363f16725a9987dec964cd98a548c))
  :named M02_Types.Monad_interpretation_Tm_arrow_47d363f16725a9987dec964cd98a548c))
; binder_x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
;;; Fact-ids: 
(assert
 (! (HasType
   x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
   (Tm_arrow_47d363f16725a9987dec964cd98a548c uu___1123 uu___1124))
  :named binder_x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6))
; Uninterpreted function symbol for impure function
(declare-fun M02_Types.Monad.concatMap_append (Universe Universe Term Term Term Term Term) Term)
; Uninterpreted name for impure function
(declare-fun M02_Types.Monad.concatMap_append@tok (Universe Universe) Term)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)

; Encoding query formula : forall (p: Prims.pure_post Prims.unit).
;   (forall (pure_result: Prims.unit).
;       FStar.List.Tot.Base.concatMap f (xs @ ys) ==
;       FStar.List.Tot.Base.concatMap f xs @ FStar.List.Tot.Base.concatMap f ys ==>
;       p pure_result) ==>
;   (forall (k: Prims.pure_post Prims.unit).
;       (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x) ==>
;       (~(Nil? xs) /\ ~(Cons? xs) ==> Prims.l_False) /\
;       (xs == [] ==> (forall (any_result: Prims.unit). k any_result)) /\
;       (~(Nil? xs) ==>
;         (forall (b: a) (b: Prims.list a).
;             xs == b :: b ==>
;             (b << xs \/ b === xs /\ ys << ys) /\
;             (forall (any_result: (_: a -> Prims.list b)).
;                 f == any_result ==>
;                 (forall (pure_result: Prims.unit).
;                     FStar.List.Tot.Base.concatMap f (b @ ys) ==
;                     FStar.List.Tot.Base.concatMap f b @ FStar.List.Tot.Base.concatMap f ys ==>
;                     (forall (b: Prims.list b) (b: Prims.list b) (b: Prims.list b).
;                         (f b,
;                         FStar.List.Tot.Base.concatMap f b,
;                         FStar.List.Tot.Base.concatMap f ys) ==
;                         (b,
;                         b,
;                         b) ==>
;                         (forall (pure_result: Prims.unit).
;                             (b @ b) @ b == b @ b @ b ==> k pure_result)))))))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec concatMap_append`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   ;; def=M02_Types.Monad.fst(46,4-51,32); use=M02_Types.Monad.fst(46,4-51,32)
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(46,4-51,32)
       (forall ((@x1 Term))
        (! (implies
          (and
           (or label_1 (HasType @x1 Prims.unit))
           ;; def=M02_Types.Monad.fst(45,12-45,70); use=M02_Types.Monad.fst(46,4-51,32)
           (or
            label_2
            ;; def=M02_Types.Monad.fst(45,12-45,70); use=M02_Types.Monad.fst(46,4-51,32)
            (=
             (FStar.List.Tot.Base.concatMap
              uu___1124
              uu___1123
              x_9ecc547c2c206cff31a29ddb75882a86_2
              x_aeaaf64f60a07c3550d419f59cbfae4a_3
              x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
              (FStar.List.Tot.Base.op_At
               uu___1124
               x_9ecc547c2c206cff31a29ddb75882a86_2
               x_d5bdb6b26cd2c11359d1f6510358cf74_4
               x_d5bdb6b26cd2c11359d1f6510358cf74_5))
             (FStar.List.Tot.Base.op_At
              uu___1123
              x_aeaaf64f60a07c3550d419f59cbfae4a_3
              (FStar.List.Tot.Base.concatMap
               uu___1124
               uu___1123
               x_9ecc547c2c206cff31a29ddb75882a86_2
               x_aeaaf64f60a07c3550d419f59cbfae4a_3
               x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
               x_d5bdb6b26cd2c11359d1f6510358cf74_4)
              (FStar.List.Tot.Base.concatMap
               uu___1124
               uu___1123
               x_9ecc547c2c206cff31a29ddb75882a86_2
               x_aeaaf64f60a07c3550d419f59cbfae4a_3
               x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
               x_d5bdb6b26cd2c11359d1f6510358cf74_5)))))
          ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(46,4-51,32)
          (Valid
           ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(46,4-51,32)
           (ApplyTT @x0 @x1)))
         :pattern
          (;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(46,4-51,32)
           (Valid
            ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(46,4-51,32)
            (ApplyTT @x0 @x1)))
         :qid @query.1)))
      ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(46,4-51,32)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 (Prims.pure_post U_zero Prims.unit))
          ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(46,4-51,32)
          (forall ((@x2 Term))
           (! (implies
             ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(46,4-51,32)
             (Valid
              ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(46,4-51,32)
              (ApplyTT @x0 @x2))
             ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(46,4-51,32)
             (Valid
              ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(46,4-51,32)
              (ApplyTT @x1 @x2)))
            :weight 0
            :pattern ((ApplyTT @x1 @x2))
            :qid @query.3)))
         ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(46,4-51,32)
         (and
          (implies
           ;; def=M02_Types.Monad.fst(44,39-44,41); use=M02_Types.Monad.fst(46,10-46,12)
           (and
            ;; def=M02_Types.Monad.fst(44,39-44,41); use=M02_Types.Monad.fst(46,10-46,12)
            (not
             ;; def=M02_Types.Monad.fst(44,39-44,41); use=M02_Types.Monad.fst(46,10-46,12)
             (BoxBool_proj_0
              (Prims.uu___is_Nil
               uu___1124
               x_9ecc547c2c206cff31a29ddb75882a86_2
               x_d5bdb6b26cd2c11359d1f6510358cf74_4)))
            ;; def=M02_Types.Monad.fst(44,39-44,41); use=M02_Types.Monad.fst(46,10-46,12)
            (not
             ;; def=M02_Types.Monad.fst(44,39-44,41); use=M02_Types.Monad.fst(46,10-46,12)
             (BoxBool_proj_0
              (Prims.uu___is_Cons
               uu___1124
               x_9ecc547c2c206cff31a29ddb75882a86_2
               x_d5bdb6b26cd2c11359d1f6510358cf74_4))))
           label_3)
          (implies
           ;; def=M02_Types.Monad.fst(44,39-47,8); use=M02_Types.Monad.fst(46,10-47,8)
           (=
            x_d5bdb6b26cd2c11359d1f6510358cf74_4
            (Prims.Nil uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2))
           ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(46,4-51,32)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 Prims.unit)
              ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(46,4-51,32)
              (Valid
               ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(46,4-51,32)
               (ApplyTT @x1 @x2)))
             :qid @query.4)))
          (implies
           ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(46,4-51,32)
           (not
            ;; def=M02_Types.Monad.fst(44,39-44,41); use=M02_Types.Monad.fst(46,10-46,12)
            (BoxBool_proj_0
             (Prims.uu___is_Nil
              uu___1124
              x_9ecc547c2c206cff31a29ddb75882a86_2
              x_d5bdb6b26cd2c11359d1f6510358cf74_4)))
           ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(46,4-51,32)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 x_9ecc547c2c206cff31a29ddb75882a86_2)
              ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(46,4-51,32)
              (forall ((@x3 Term))
               (! (implies
                 (and
                  (HasType @x3 (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2))
                  ;; def=M02_Types.Monad.fst(44,39-48,14); use=M02_Types.Monad.fst(46,10-48,14)
                  (=
                   x_d5bdb6b26cd2c11359d1f6510358cf74_4
                   (Prims.Cons uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2 @x2 @x3)))
                 ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(46,4-51,32)
                 (and
                  ;; def=M02_Types.Monad.fst(44,39-51,32); use=M02_Types.Monad.fst(49,31-49,32)
                  (or
                   label_4
                   ;; def=M02_Types.Monad.fst(46,4-51,32); use=M02_Types.Monad.fst(49,31-49,32)
                   (Valid
                    ;; def=M02_Types.Monad.fst(46,4-51,32); use=M02_Types.Monad.fst(49,31-49,32)
                    (Prims.precedes
                     uu___1124
                     uu___1124
                     (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2)
                     (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2)
                     @x3
                     x_d5bdb6b26cd2c11359d1f6510358cf74_4))
                   ;; def=M02_Types.Monad.fst(44,39-51,32); use=M02_Types.Monad.fst(49,31-49,32)
                   (and
                    ;; def=M02_Types.Monad.fst(44,39-44,41); use=M02_Types.Monad.fst(49,31-49,32)
                    (Valid
                     ;; def=M02_Types.Monad.fst(44,39-44,41); use=M02_Types.Monad.fst(49,31-49,32)
                     (Prims.op_Equals_Equals_Equals
                      uu___1124
                      (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2)
                      (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2)
                      @x3
                      x_d5bdb6b26cd2c11359d1f6510358cf74_4))
                    ;; def=M02_Types.Monad.fst(46,4-51,32); use=M02_Types.Monad.fst(49,31-49,32)
                    (Valid
                     ;; def=M02_Types.Monad.fst(46,4-51,32); use=M02_Types.Monad.fst(49,31-49,32)
                     (Prims.precedes
                      uu___1124
                      uu___1124
                      (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2)
                      (Prims.list uu___1124 x_9ecc547c2c206cff31a29ddb75882a86_2)
                      x_d5bdb6b26cd2c11359d1f6510358cf74_5
                      x_d5bdb6b26cd2c11359d1f6510358cf74_5))))
                  ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(46,4-51,32)
                  (forall ((@x4 Term))
                   (! (implies
                     (and
                      (HasType @x4 (Tm_arrow_47d363f16725a9987dec964cd98a548c uu___1123 uu___1124))
                      ;; def=M02_Types.Monad.fst(44,54-44,55); use=M02_Types.Monad.fst(46,4-51,32)
                      (= x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6 @x4))
                     ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(49,8-49,24)
                     (forall ((@x5 Term))
                      (! (implies
                        (and
                         (HasType @x5 Prims.unit)
                         ;; def=M02_Types.Monad.fst(45,12-45,70); use=M02_Types.Monad.fst(49,8-49,24)
                         (=
                          (FStar.List.Tot.Base.concatMap
                           uu___1124
                           uu___1123
                           x_9ecc547c2c206cff31a29ddb75882a86_2
                           x_aeaaf64f60a07c3550d419f59cbfae4a_3
                           x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
                           (FStar.List.Tot.Base.op_At
                            uu___1124
                            x_9ecc547c2c206cff31a29ddb75882a86_2
                            @x3
                            x_d5bdb6b26cd2c11359d1f6510358cf74_5))
                          (FStar.List.Tot.Base.op_At
                           uu___1123
                           x_aeaaf64f60a07c3550d419f59cbfae4a_3
                           (FStar.List.Tot.Base.concatMap
                            uu___1124
                            uu___1123
                            x_9ecc547c2c206cff31a29ddb75882a86_2
                            x_aeaaf64f60a07c3550d419f59cbfae4a_3
                            x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
                            @x3)
                           (FStar.List.Tot.Base.concatMap
                            uu___1124
                            uu___1123
                            x_9ecc547c2c206cff31a29ddb75882a86_2
                            x_aeaaf64f60a07c3550d419f59cbfae4a_3
                            x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
                            x_d5bdb6b26cd2c11359d1f6510358cf74_5))))
                        ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(46,4-51,32)
                        (forall ((@x6 Term))
                         (! (implies
                           (HasType @x6 (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3))
                           ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(46,4-51,32)
                           (forall ((@x7 Term))
                            (! (implies
                              (HasType
                               @x7
                               (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3))
                              ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(46,4-51,32)
                              (forall ((@x8 Term))
                               (! (implies
                                 (and
                                  (HasType
                                   @x8
                                   (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3))
                                  ;; def=M02_Types.Monad.fst(50,13-50,26); use=M02_Types.Monad.fst(50,13-50,26)
                                  (=
                                   (FStar.Pervasives.Native.Mktuple3
                                    uu___1123
                                    uu___1123
                                    uu___1123
                                    (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3)
                                    (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3)
                                    (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3)
                                    (ApplyTT x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6 @x2)
                                    (FStar.List.Tot.Base.concatMap
                                     uu___1124
                                     uu___1123
                                     x_9ecc547c2c206cff31a29ddb75882a86_2
                                     x_aeaaf64f60a07c3550d419f59cbfae4a_3
                                     x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
                                     @x3)
                                    (FStar.List.Tot.Base.concatMap
                                     uu___1124
                                     uu___1123
                                     x_9ecc547c2c206cff31a29ddb75882a86_2
                                     x_aeaaf64f60a07c3550d419f59cbfae4a_3
                                     x_bcc47da5feb2689c36ebd5e1cd3ceb5d_6
                                     x_d5bdb6b26cd2c11359d1f6510358cf74_5))
                                   (FStar.Pervasives.Native.Mktuple3
                                    uu___1123
                                    uu___1123
                                    uu___1123
                                    (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3)
                                    (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3)
                                    (Prims.list uu___1123 x_aeaaf64f60a07c3550d419f59cbfae4a_3)
                                    @x6
                                    @x7
                                    @x8)))
                                 ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(51,8-51,20)
                                 (forall ((@x9 Term))
                                  (! (implies
                                    (and
                                     (HasType @x9 Prims.unit)
                                     ;; def=M02_Types.Monad.fst(39,12-39,46); use=M02_Types.Monad.fst(51,8-51,20)
                                     (=
                                      (FStar.List.Tot.Base.op_At
                                       uu___1123
                                       x_aeaaf64f60a07c3550d419f59cbfae4a_3
                                       (FStar.List.Tot.Base.op_At
                                        uu___1123
                                        x_aeaaf64f60a07c3550d419f59cbfae4a_3
                                        @x6
                                        @x7)
                                       @x8)
                                      (FStar.List.Tot.Base.op_At
                                       uu___1123
                                       x_aeaaf64f60a07c3550d419f59cbfae4a_3
                                       @x6
                                       (FStar.List.Tot.Base.op_At
                                        uu___1123
                                        x_aeaaf64f60a07c3550d419f59cbfae4a_3
                                        @x7
                                        @x8))))
                                    ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(51,8-51,20)
                                    (Valid
                                     ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(51,8-51,20)
                                     (ApplyTT @x1 @x9)))
                                   :qid @query.12)))
                                :qid @query.11)))
                             :qid @query.10)))
                          :qid @query.9)))
                       :qid @query.8)))
                    :qid @query.7))))
                :qid @query.6)))
             :qid @query.5)))))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.concatMap_append, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(push) ;; push{2
; universe local constant
(declare-fun uu___1193 () Universe)
; universe local constant
(declare-fun uu___1192 () Universe)
; universe local constant
(declare-fun uu___1191 () Universe)
; a : Type (Type)
(declare-fun x_5291e79fe22e1a22b149e48ad1f333b7_3 () Term)
; binder_x_5291e79fe22e1a22b149e48ad1f333b7_3
;;; Fact-ids: 
(assert
 (! (HasType x_5291e79fe22e1a22b149e48ad1f333b7_3 (Tm_type uu___1193))
  :named binder_x_5291e79fe22e1a22b149e48ad1f333b7_3))
; b : Type (Type)
(declare-fun x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4 () Term)
; binder_x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
;;; Fact-ids: 
(assert
 (! (HasType x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4 (Tm_type uu___1192))
  :named binder_x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4))
; c : Type (Type)
(declare-fun x_d1b9400b70639cdd98adb2a0203ec3f4_5 () Term)
; binder_x_d1b9400b70639cdd98adb2a0203ec3f4_5
;;; Fact-ids: 
(assert
 (! (HasType x_d1b9400b70639cdd98adb2a0203ec3f4_5 (Tm_type uu___1191))
  :named binder_x_d1b9400b70639cdd98adb2a0203ec3f4_5))
; xs : Prims.list a (Prims.list a)
(declare-fun x_9532d2d16117ce60589a9083bb3becbe_6 () Term)
; binder_x_9532d2d16117ce60589a9083bb3becbe_6
;;; Fact-ids: 
(assert
 (! (HasType
   x_9532d2d16117ce60589a9083bb3becbe_6
   (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3))
  :named binder_x_9532d2d16117ce60589a9083bb3becbe_6))
; f : _: a -> Prims.list b (_: a -> Prims.list b)
(declare-fun x_a6d7374e9c8eeb8261a65adfca25792e_7 () Term)
; _: a -> Prims.list b
(declare-fun Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f (Universe Universe) Term)
; kinding_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,66); use=M02_Types.Monad.fst(53,55-53,66)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (HasType (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u0 @u1) (Tm_type (U_max @u0 @u1)))
    :pattern
     ((HasType (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u0 @u1) (Tm_type (U_max @u0 @u1))))
    :qid kinding_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
  :named kinding_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,66); use=M02_Types.Monad.fst(53,55-53,66)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u2 @u3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u2 @u3)))
    :qid M02_Types.Monad_pre_typing_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
  :named M02_Types.Monad_pre_typing_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
; interpretation_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,66); use=M02_Types.Monad.fst(53,55-53,66)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u1 @u2))
     (and
      ;; def=M02_Types.Monad.fst(53,26-53,66); use=M02_Types.Monad.fst(53,55-53,66)
      (forall ((@x3 Term))
       (! (implies
         (HasType @x3 x_5291e79fe22e1a22b149e48ad1f333b7_3)
         (HasType (ApplyTT @x0 @x3) (Prims.list @u1 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4)))
        :pattern ((ApplyTT @x0 @x3))
        :qid M02_Types.Monad_interpretation_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u1 @u2)))
    :qid M02_Types.Monad_interpretation_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
  :named M02_Types.Monad_interpretation_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
; binder_x_a6d7374e9c8eeb8261a65adfca25792e_7
;;; Fact-ids: 
(assert
 (! (HasType
   x_a6d7374e9c8eeb8261a65adfca25792e_7
   (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f uu___1192 uu___1193))
  :named binder_x_a6d7374e9c8eeb8261a65adfca25792e_7))
; g : _: b -> Prims.list c (_: b -> Prims.list c)
(declare-fun x_46f1c4a5584aa156b80fe0f325f80f97_8 () Term)
; _: b -> Prims.list c
(declare-fun Tm_arrow_1ac033956bc64594ebab90a7d66eacdd (Universe Universe) Term)
; kinding_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,29-53,82); use=M02_Types.Monad.fst(53,71-53,82)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (HasType (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u0 @u1) (Tm_type (U_max @u0 @u1)))
    :pattern
     ((HasType (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u0 @u1) (Tm_type (U_max @u0 @u1))))
    :qid kinding_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
  :named kinding_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,29-53,82); use=M02_Types.Monad.fst(53,71-53,82)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u2 @u3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u2 @u3)))
    :qid M02_Types.Monad_pre_typing_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
  :named M02_Types.Monad_pre_typing_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
; interpretation_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,29-53,82); use=M02_Types.Monad.fst(53,71-53,82)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u1 @u2))
     (and
      ;; def=M02_Types.Monad.fst(53,29-53,82); use=M02_Types.Monad.fst(53,71-53,82)
      (forall ((@x3 Term))
       (! (implies
         (HasType @x3 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4)
         (HasType (ApplyTT @x0 @x3) (Prims.list @u1 x_d1b9400b70639cdd98adb2a0203ec3f4_5)))
        :pattern ((ApplyTT @x0 @x3))
        :qid M02_Types.Monad_interpretation_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u1 @u2)))
    :qid M02_Types.Monad_interpretation_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
  :named M02_Types.Monad_interpretation_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
; binder_x_46f1c4a5584aa156b80fe0f325f80f97_8
;;; Fact-ids: 
(assert
 (! (HasType
   x_46f1c4a5584aa156b80fe0f325f80f97_8
   (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd uu___1191 uu___1192))
  :named binder_x_46f1c4a5584aa156b80fe0f325f80f97_8))
; Uninterpreted function symbol for impure function
(declare-fun
 M02_Types.Monad.concatMap_assoc
 (Universe Universe Universe Term Term Term Term Term Term)
 Term)
; Uninterpreted name for impure function
(declare-fun M02_Types.Monad.concatMap_assoc@tok (Universe Universe Universe) Term)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)

; y: a -> Prims.list c
(declare-fun Tm_arrow_ed238b516b78d0b1d22070215ef0d36b (Universe Universe) Term)
; kinding_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,27); use=M02_Types.Monad.fst(53,55-59,14)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (HasType (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u0 @u1) (Tm_type (U_max @u0 @u1)))
    :pattern
     ((HasType (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u0 @u1) (Tm_type (U_max @u0 @u1))))
    :qid kinding_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
  :named kinding_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,27); use=M02_Types.Monad.fst(53,55-59,14)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u2 @u3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u2 @u3)))
    :qid M02_Types.Monad_pre_typing_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
  :named M02_Types.Monad_pre_typing_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
; interpretation_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,27); use=M02_Types.Monad.fst(53,55-59,14)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u1 @u2))
     (and
      ;; def=M02_Types.Monad.fst(53,26-53,27); use=M02_Types.Monad.fst(53,55-59,14)
      (forall ((@x3 Term))
       (! (implies
         (HasType @x3 x_5291e79fe22e1a22b149e48ad1f333b7_3)
         (HasType (ApplyTT @x0 @x3) (Prims.list @u1 x_d1b9400b70639cdd98adb2a0203ec3f4_5)))
        :pattern ((ApplyTT @x0 @x3))
        :qid M02_Types.Monad_interpretation_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u1 @u2)))
    :qid M02_Types.Monad_interpretation_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
  :named M02_Types.Monad_interpretation_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
(declare-fun Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 (Universe Universe Universe) Term)
; typing_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(60,32-60,49); use=M02_Types.Monad.fst(59,8-59,14)
  (forall ((@u0 Universe) (@u1 Universe) (@u2 Universe))
   (! (HasType
     (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u0 @u1 @u2)
     (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u0 @u1))
    :pattern ((Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u0 @u1 @u2))
    :qid typing_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0))
  :named typing_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0))
; interpretation_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(60,32-60,49); use=M02_Types.Monad.fst(59,8-59,14)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe) (@u3 Universe))
   (! (=
     (ApplyTT (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u1 @u2 @u3) @x0)
     (FStar.List.Tot.Base.concatMap
      @u3
      @u1
      x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
      x_d1b9400b70639cdd98adb2a0203ec3f4_5
      x_46f1c4a5584aa156b80fe0f325f80f97_8
      (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x0)))
    :pattern ((ApplyTT (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u1 @u2 @u3) @x0))
    :qid interpretation_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0))
  :named interpretation_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0))




; Encoding query formula : forall (p: Prims.pure_post Prims.unit).
;   (forall (pure_result: Prims.unit).
;       FStar.List.Tot.Base.concatMap (fun y -> FStar.List.Tot.Base.concatMap g (f y)) xs ==
;       FStar.List.Tot.Base.concatMap g (FStar.List.Tot.Base.concatMap f xs) ==>
;       p pure_result) ==>
;   (forall (k: Prims.pure_post Prims.unit).
;       (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x) ==>
;       (~(Nil? xs) /\ ~(Cons? xs) ==> Prims.l_False) /\
;       (xs == [] ==> (forall (any_result: Prims.unit). k any_result)) /\
;       (~(Nil? xs) ==>
;         (forall (b: a) (b: Prims.list a).
;             xs == b :: b ==>
;             b << xs /\
;             (forall (any_result: (_: b -> Prims.list c)).
;                 g == any_result ==>
;                 (forall (pure_result: Prims.unit).
;                     FStar.List.Tot.Base.concatMap (fun y -> FStar.List.Tot.Base.concatMap g (f y)) b ==
;                     FStar.List.Tot.Base.concatMap g (FStar.List.Tot.Base.concatMap f b) ==>
;                     (forall (pure_result: Prims.unit).
;                         FStar.List.Tot.Base.concatMap (fun y ->
;                               FStar.List.Tot.Base.concatMap g (f y))
;                           (b :: b) ==
;                         FStar.List.Tot.Base.concatMap g (FStar.List.Tot.Base.concatMap f (b :: b)) ==>
;                         (forall (pure_result: Prims.unit).
;                             FStar.List.Tot.Base.concatMap g
;                               (f b @ FStar.List.Tot.Base.concatMap f b) ==
;                             FStar.List.Tot.Base.concatMap g (f b) @
;                             FStar.List.Tot.Base.concatMap g (FStar.List.Tot.Base.concatMap f b) ==>
;                             k pure_result)))))))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec concatMap_assoc`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   ;; def=M02_Types.Monad.fst(55,4-67,52); use=M02_Types.Monad.fst(55,4-67,52)
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(55,4-67,52)
       (forall ((@x1 Term))
        (! (implies
          (and
           (or label_1 (HasType @x1 Prims.unit))
           ;; def=M02_Types.Monad.fst(54,12-54,87); use=M02_Types.Monad.fst(55,4-67,52)
           (or
            label_2
            ;; def=M02_Types.Monad.fst(54,12-54,87); use=M02_Types.Monad.fst(55,4-67,52)
            (=
             (FStar.List.Tot.Base.concatMap
              uu___1193
              uu___1191
              x_5291e79fe22e1a22b149e48ad1f333b7_3
              x_d1b9400b70639cdd98adb2a0203ec3f4_5
              (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
              x_9532d2d16117ce60589a9083bb3becbe_6)
             (FStar.List.Tot.Base.concatMap
              uu___1192
              uu___1191
              x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
              x_d1b9400b70639cdd98adb2a0203ec3f4_5
              x_46f1c4a5584aa156b80fe0f325f80f97_8
              (FStar.List.Tot.Base.concatMap
               uu___1193
               uu___1192
               x_5291e79fe22e1a22b149e48ad1f333b7_3
               x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
               x_a6d7374e9c8eeb8261a65adfca25792e_7
               x_9532d2d16117ce60589a9083bb3becbe_6)))))
          ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(55,4-67,52)
          (Valid
           ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(55,4-67,52)
           (ApplyTT @x0 @x1)))
         :pattern
          (;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(55,4-67,52)
           (Valid
            ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(55,4-67,52)
            (ApplyTT @x0 @x1)))
         :qid @query.1)))
      ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(55,4-67,52)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 (Prims.pure_post U_zero Prims.unit))
          ;; def=Prims.fst(410,2-410,97); use=M02_Types.Monad.fst(55,4-67,52)
          (forall ((@x2 Term))
           (! (implies
             ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(55,4-67,52)
             (Valid
              ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(55,4-67,52)
              (ApplyTT @x0 @x2))
             ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(55,4-67,52)
             (Valid
              ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(55,4-67,52)
              (ApplyTT @x1 @x2)))
            :weight 0
            :pattern ((ApplyTT @x1 @x2))
            :qid @query.3)))
         ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(55,4-67,52)
         (and
          (implies
           ;; def=M02_Types.Monad.fst(53,41-53,43); use=M02_Types.Monad.fst(55,10-55,12)
           (and
            ;; def=M02_Types.Monad.fst(53,41-53,43); use=M02_Types.Monad.fst(55,10-55,12)
            (not
             ;; def=M02_Types.Monad.fst(53,41-53,43); use=M02_Types.Monad.fst(55,10-55,12)
             (BoxBool_proj_0
              (Prims.uu___is_Nil
               uu___1193
               x_5291e79fe22e1a22b149e48ad1f333b7_3
               x_9532d2d16117ce60589a9083bb3becbe_6)))
            ;; def=M02_Types.Monad.fst(53,41-53,43); use=M02_Types.Monad.fst(55,10-55,12)
            (not
             ;; def=M02_Types.Monad.fst(53,41-53,43); use=M02_Types.Monad.fst(55,10-55,12)
             (BoxBool_proj_0
              (Prims.uu___is_Cons
               uu___1193
               x_5291e79fe22e1a22b149e48ad1f333b7_3
               x_9532d2d16117ce60589a9083bb3becbe_6))))
           label_3)
          (implies
           ;; def=M02_Types.Monad.fst(53,41-56,8); use=M02_Types.Monad.fst(55,10-56,8)
           (=
            x_9532d2d16117ce60589a9083bb3becbe_6
            (Prims.Nil uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3))
           ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(55,4-67,52)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 Prims.unit)
              ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(55,4-67,52)
              (Valid
               ;; def=Prims.fst(459,90-459,102); use=M02_Types.Monad.fst(55,4-67,52)
               (ApplyTT @x1 @x2)))
             :qid @query.4)))
          (implies
           ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(55,4-67,52)
           (not
            ;; def=M02_Types.Monad.fst(53,41-53,43); use=M02_Types.Monad.fst(55,10-55,12)
            (BoxBool_proj_0
             (Prims.uu___is_Nil
              uu___1193
              x_5291e79fe22e1a22b149e48ad1f333b7_3
              x_9532d2d16117ce60589a9083bb3becbe_6)))
           ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(55,4-67,52)
           (forall ((@x2 Term))
            (! (implies
              (HasType @x2 x_5291e79fe22e1a22b149e48ad1f333b7_3)
              ;; def=Prims.fst(421,99-421,120); use=M02_Types.Monad.fst(55,4-67,52)
              (forall ((@x3 Term))
               (! (implies
                 (and
                  (HasType @x3 (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3))
                  ;; def=M02_Types.Monad.fst(53,41-57,14); use=M02_Types.Monad.fst(55,10-57,14)
                  (=
                   x_9532d2d16117ce60589a9083bb3becbe_6
                   (Prims.Cons uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3 @x2 @x3)))
                 ;; def=Prims.fst(467,77-467,89); use=M02_Types.Monad.fst(55,4-67,52)
                 (and
                  ;; def=M02_Types.Monad.fst(55,4-67,52); use=M02_Types.Monad.fst(58,29-58,30)
                  (or
                   label_4
                   ;; def=M02_Types.Monad.fst(55,4-67,52); use=M02_Types.Monad.fst(58,29-58,30)
                   (Valid
                    ;; def=M02_Types.Monad.fst(55,4-67,52); use=M02_Types.Monad.fst(58,29-58,30)
                    (Prims.precedes
                     uu___1193
                     uu___1193
                     (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3)
                     (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3)
                     @x3
                     x_9532d2d16117ce60589a9083bb3becbe_6)))
                  ;; def=Prims.fst(459,66-459,102); use=M02_Types.Monad.fst(55,4-67,52)
                  (forall ((@x4 Term))
                   (! (implies
                     (and
                      (HasType @x4 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd uu___1191 uu___1192))
                      ;; def=M02_Types.Monad.fst(53,69-53,70); use=M02_Types.Monad.fst(55,4-67,52)
                      (= x_46f1c4a5584aa156b80fe0f325f80f97_8 @x4))
                     ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(58,8-58,23)
                     (forall ((@x5 Term))
                      (! (implies
                        (and
                         (HasType @x5 Prims.unit)
                         ;; def=M02_Types.Monad.fst(54,12-54,87); use=M02_Types.Monad.fst(58,8-58,23)
                         (=
                          (FStar.List.Tot.Base.concatMap
                           uu___1193
                           uu___1191
                           x_5291e79fe22e1a22b149e48ad1f333b7_3
                           x_d1b9400b70639cdd98adb2a0203ec3f4_5
                           (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
                           @x3)
                          (FStar.List.Tot.Base.concatMap
                           uu___1192
                           uu___1191
                           x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                           x_d1b9400b70639cdd98adb2a0203ec3f4_5
                           x_46f1c4a5584aa156b80fe0f325f80f97_8
                           (FStar.List.Tot.Base.concatMap
                            uu___1193
                            uu___1192
                            x_5291e79fe22e1a22b149e48ad1f333b7_3
                            x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                            x_a6d7374e9c8eeb8261a65adfca25792e_7
                            @x3))))
                        ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(59,8-59,14)
                        (forall ((@x6 Term))
                         (! (implies
                           (and
                            (HasType @x6 Prims.unit)
                            ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
                            (=
                             (FStar.List.Tot.Base.concatMap
                              uu___1193
                              uu___1191
                              x_5291e79fe22e1a22b149e48ad1f333b7_3
                              x_d1b9400b70639cdd98adb2a0203ec3f4_5
                              (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
                              (Prims.Cons uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3 @x2 @x3))
                             (FStar.List.Tot.Base.concatMap
                              uu___1192
                              uu___1191
                              x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                              x_d1b9400b70639cdd98adb2a0203ec3f4_5
                              x_46f1c4a5584aa156b80fe0f325f80f97_8
                              (FStar.List.Tot.Base.concatMap
                               uu___1193
                               uu___1192
                               x_5291e79fe22e1a22b149e48ad1f333b7_3
                               x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                               x_a6d7374e9c8eeb8261a65adfca25792e_7
                               (Prims.Cons uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3 @x2 @x3)))))
                           ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(67,8-67,24)
                           (forall ((@x7 Term))
                            (! (implies
                              (and
                               (HasType @x7 Prims.unit)
                               ;; def=M02_Types.Monad.fst(45,12-45,70); use=M02_Types.Monad.fst(67,8-67,24)
                               (=
                                (FStar.List.Tot.Base.concatMap
                                 uu___1192
                                 uu___1191
                                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                                 x_d1b9400b70639cdd98adb2a0203ec3f4_5
                                 x_46f1c4a5584aa156b80fe0f325f80f97_8
                                 (FStar.List.Tot.Base.op_At
                                  uu___1192
                                  x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                                  (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x2)
                                  (FStar.List.Tot.Base.concatMap
                                   uu___1193
                                   uu___1192
                                   x_5291e79fe22e1a22b149e48ad1f333b7_3
                                   x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                                   x_a6d7374e9c8eeb8261a65adfca25792e_7
                                   @x3)))
                                (FStar.List.Tot.Base.op_At
                                 uu___1191
                                 x_d1b9400b70639cdd98adb2a0203ec3f4_5
                                 (FStar.List.Tot.Base.concatMap
                                  uu___1192
                                  uu___1191
                                  x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                                  x_d1b9400b70639cdd98adb2a0203ec3f4_5
                                  x_46f1c4a5584aa156b80fe0f325f80f97_8
                                  (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x2))
                                 (FStar.List.Tot.Base.concatMap
                                  uu___1192
                                  uu___1191
                                  x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                                  x_d1b9400b70639cdd98adb2a0203ec3f4_5
                                  x_46f1c4a5584aa156b80fe0f325f80f97_8
                                  (FStar.List.Tot.Base.concatMap
                                   uu___1193
                                   uu___1192
                                   x_5291e79fe22e1a22b149e48ad1f333b7_3
                                   x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                                   x_a6d7374e9c8eeb8261a65adfca25792e_7
                                   @x3)))))
                              ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(67,8-67,24)
                              (Valid
                               ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(67,8-67,24)
                               (ApplyTT @x1 @x7)))
                             :qid @query.10)))
                          :qid @query.9)))
                       :qid @query.8)))
                    :qid @query.7))))
                :qid @query.6)))
             :qid @query.5)))))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.concatMap_assoc, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(declare-fun Prims.guard_free (Term) Term)
; free var typing
;;; Fact-ids: Name Prims.guard_free; Namespace Prims
(assert
 (! ;; def=Prims.fst(354,5-354,15); use=Prims.fst(354,5-354,15)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 (Tm_type U_zero)) (HasType (Prims.guard_free @x0) (Tm_type U_zero)))
    :pattern ((Prims.guard_free @x0))
    :qid typing_Prims.guard_free))
  :named typing_Prims.guard_free))
(push) ;; push{2
; universe local constant
(declare-fun uu___1193 () Universe)
; universe local constant
(declare-fun uu___1192 () Universe)
; universe local constant
(declare-fun uu___1191 () Universe)
; a : Type (Type)
(declare-fun x_5291e79fe22e1a22b149e48ad1f333b7_3 () Term)
; binder_x_5291e79fe22e1a22b149e48ad1f333b7_3
;;; Fact-ids: 
(assert
 (! (HasType x_5291e79fe22e1a22b149e48ad1f333b7_3 (Tm_type uu___1193))
  :named binder_x_5291e79fe22e1a22b149e48ad1f333b7_3))
; b : Type (Type)
(declare-fun x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4 () Term)
; binder_x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
;;; Fact-ids: 
(assert
 (! (HasType x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4 (Tm_type uu___1192))
  :named binder_x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4))
; c : Type (Type)
(declare-fun x_d1b9400b70639cdd98adb2a0203ec3f4_5 () Term)
; binder_x_d1b9400b70639cdd98adb2a0203ec3f4_5
;;; Fact-ids: 
(assert
 (! (HasType x_d1b9400b70639cdd98adb2a0203ec3f4_5 (Tm_type uu___1191))
  :named binder_x_d1b9400b70639cdd98adb2a0203ec3f4_5))
; xs : Prims.list a (Prims.list a)
(declare-fun x_9532d2d16117ce60589a9083bb3becbe_6 () Term)
; binder_x_9532d2d16117ce60589a9083bb3becbe_6
;;; Fact-ids: 
(assert
 (! (HasType
   x_9532d2d16117ce60589a9083bb3becbe_6
   (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3))
  :named binder_x_9532d2d16117ce60589a9083bb3becbe_6))
; f : _: a -> Prims.list b (_: a -> Prims.list b)
(declare-fun x_a6d7374e9c8eeb8261a65adfca25792e_7 () Term)
; _: a -> Prims.list b
(declare-fun Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f (Universe Universe) Term)
; kinding_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,66); use=M02_Types.Monad.fst(53,55-53,66)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (HasType (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u0 @u1) (Tm_type (U_max @u0 @u1)))
    :pattern
     ((HasType (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u0 @u1) (Tm_type (U_max @u0 @u1))))
    :qid kinding_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
  :named kinding_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,66); use=M02_Types.Monad.fst(53,55-53,66)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u2 @u3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u2 @u3)))
    :qid M02_Types.Monad_pre_typing_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
  :named M02_Types.Monad_pre_typing_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
; interpretation_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,66); use=M02_Types.Monad.fst(53,55-53,66)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u1 @u2))
     (and
      ;; def=M02_Types.Monad.fst(53,26-53,66); use=M02_Types.Monad.fst(53,55-53,66)
      (forall ((@x3 Term))
       (! (implies
         (HasType @x3 x_5291e79fe22e1a22b149e48ad1f333b7_3)
         (HasType (ApplyTT @x0 @x3) (Prims.list @u1 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4)))
        :pattern ((ApplyTT @x0 @x3))
        :qid M02_Types.Monad_interpretation_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f @u1 @u2)))
    :qid M02_Types.Monad_interpretation_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
  :named M02_Types.Monad_interpretation_Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f))
; binder_x_a6d7374e9c8eeb8261a65adfca25792e_7
;;; Fact-ids: 
(assert
 (! (HasType
   x_a6d7374e9c8eeb8261a65adfca25792e_7
   (Tm_arrow_a6a3fdb0b5c8f67d93ab99c387f06b1f uu___1192 uu___1193))
  :named binder_x_a6d7374e9c8eeb8261a65adfca25792e_7))
; g : _: b -> Prims.list c (_: b -> Prims.list c)
(declare-fun x_46f1c4a5584aa156b80fe0f325f80f97_8 () Term)
; _: b -> Prims.list c
(declare-fun Tm_arrow_1ac033956bc64594ebab90a7d66eacdd (Universe Universe) Term)
; kinding_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,29-53,82); use=M02_Types.Monad.fst(53,71-53,82)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (HasType (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u0 @u1) (Tm_type (U_max @u0 @u1)))
    :pattern
     ((HasType (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u0 @u1) (Tm_type (U_max @u0 @u1))))
    :qid kinding_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
  :named kinding_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,29-53,82); use=M02_Types.Monad.fst(53,71-53,82)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u2 @u3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u2 @u3)))
    :qid M02_Types.Monad_pre_typing_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
  :named M02_Types.Monad_pre_typing_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
; interpretation_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,29-53,82); use=M02_Types.Monad.fst(53,71-53,82)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u1 @u2))
     (and
      ;; def=M02_Types.Monad.fst(53,29-53,82); use=M02_Types.Monad.fst(53,71-53,82)
      (forall ((@x3 Term))
       (! (implies
         (HasType @x3 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4)
         (HasType (ApplyTT @x0 @x3) (Prims.list @u1 x_d1b9400b70639cdd98adb2a0203ec3f4_5)))
        :pattern ((ApplyTT @x0 @x3))
        :qid M02_Types.Monad_interpretation_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd @u1 @u2)))
    :qid M02_Types.Monad_interpretation_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
  :named M02_Types.Monad_interpretation_Tm_arrow_1ac033956bc64594ebab90a7d66eacdd))
; binder_x_46f1c4a5584aa156b80fe0f325f80f97_8
;;; Fact-ids: 
(assert
 (! (HasType
   x_46f1c4a5584aa156b80fe0f325f80f97_8
   (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd uu___1191 uu___1192))
  :named binder_x_46f1c4a5584aa156b80fe0f325f80f97_8))
; Uninterpreted function symbol for impure function
(declare-fun
 M02_Types.Monad.concatMap_assoc
 (Universe Universe Universe Term Term Term Term Term Term)
 Term)
; Uninterpreted name for impure function
(declare-fun M02_Types.Monad.concatMap_assoc@tok (Universe Universe Universe) Term)
(declare-fun label_1 () Bool)
; y: a -> Prims.list c
(declare-fun Tm_arrow_ed238b516b78d0b1d22070215ef0d36b (Universe Universe) Term)
; kinding_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,27); use=M02_Types.Monad.fst(53,26-67,52)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (HasType (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u0 @u1) (Tm_type (U_max @u0 @u1)))
    :pattern
     ((HasType (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u0 @u1) (Tm_type (U_max @u0 @u1))))
    :qid kinding_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
  :named kinding_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,27); use=M02_Types.Monad.fst(53,26-67,52)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u2 @u3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u2 @u3)))
    :qid M02_Types.Monad_pre_typing_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
  :named M02_Types.Monad_pre_typing_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
; interpretation_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,26-53,27); use=M02_Types.Monad.fst(53,26-67,52)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u1 @u2))
     (and
      ;; def=M02_Types.Monad.fst(53,26-53,27); use=M02_Types.Monad.fst(53,26-67,52)
      (forall ((@x3 Term))
       (! (implies
         (HasType @x3 x_5291e79fe22e1a22b149e48ad1f333b7_3)
         (HasType (ApplyTT @x0 @x3) (Prims.list @u1 x_d1b9400b70639cdd98adb2a0203ec3f4_5)))
        :pattern ((ApplyTT @x0 @x3))
        :qid M02_Types.Monad_interpretation_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u1 @u2)))
    :qid M02_Types.Monad_interpretation_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
  :named M02_Types.Monad_interpretation_Tm_arrow_ed238b516b78d0b1d22070215ef0d36b))
(declare-fun Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 (Universe Universe Universe) Term)
; typing_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(54,33-54,50); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Universe) (@u1 Universe) (@u2 Universe))
   (! (HasType
     (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u0 @u1 @u2)
     (Tm_arrow_ed238b516b78d0b1d22070215ef0d36b @u0 @u1))
    :pattern ((Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u0 @u1 @u2))
    :qid typing_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0))
  :named typing_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0))
; interpretation_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(54,33-54,50); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@x0 Term) (@u1 Universe) (@u2 Universe) (@u3 Universe))
   (! (=
     (ApplyTT (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u1 @u2 @u3) @x0)
     (FStar.List.Tot.Base.concatMap
      @u3
      @u1
      x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
      x_d1b9400b70639cdd98adb2a0203ec3f4_5
      x_46f1c4a5584aa156b80fe0f325f80f97_8
      (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x0)))
    :pattern ((ApplyTT (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u1 @u2 @u3) @x0))
    :qid interpretation_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0))
  :named interpretation_Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0))
(declare-fun Tm_refine_4f270e33e23275479ca9be199c6d2d9f (Universe Universe Universe Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Universe) (@u1 Universe) (@u2 Universe) (@x3 Term))
   (! (HasType (Tm_refine_4f270e33e23275479ca9be199c6d2d9f @u0 @u1 @u2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_4f270e33e23275479ca9be199c6d2d9f @u0 @u1 @u2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_4f270e33e23275479ca9be199c6d2d9f))
  :named refinement_kinding_Tm_refine_4f270e33e23275479ca9be199c6d2d9f))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe) (@u4 Universe) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_4f270e33e23275479ca9be199c6d2d9f @u2 @u3 @u4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(55,4-67,52)
      (forall ((@x6 Term))
       (! (implies
         (and
          (HasType @x6 Prims.unit)
          ;; def=M02_Types.Monad.fst(54,12-54,87); use=M02_Types.Monad.fst(55,4-67,52)
          (=
           (FStar.List.Tot.Base.concatMap
            @u3
            @u2
            x_5291e79fe22e1a22b149e48ad1f333b7_3
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u2 @u3 @u4)
            x_9532d2d16117ce60589a9083bb3becbe_6)
           (FStar.List.Tot.Base.concatMap
            @u4
            @u2
            x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            x_46f1c4a5584aa156b80fe0f325f80f97_8
            (FStar.List.Tot.Base.concatMap
             @u3
             @u4
             x_5291e79fe22e1a22b149e48ad1f333b7_3
             x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
             x_a6d7374e9c8eeb8261a65adfca25792e_7
             x_9532d2d16117ce60589a9083bb3becbe_6))))
         ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(55,4-67,52)
         (Valid
          ;; def=Prims.fst(449,83-449,96); use=M02_Types.Monad.fst(55,4-67,52)
          (ApplyTT @x5 @x6)))
        :qid refinement_interpretation_Tm_refine_4f270e33e23275479ca9be199c6d2d9f.1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_4f270e33e23275479ca9be199c6d2d9f @u2 @u3 @u4 @x5)))
    :qid refinement_interpretation_Tm_refine_4f270e33e23275479ca9be199c6d2d9f))
  :named refinement_interpretation_Tm_refine_4f270e33e23275479ca9be199c6d2d9f))
; haseq for Tm_refine_4f270e33e23275479ca9be199c6d2d9f
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(449,36-449,97); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Universe) (@u1 Universe) (@u2 Universe) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_4f270e33e23275479ca9be199c6d2d9f @u0 @u1 @u2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_4f270e33e23275479ca9be199c6d2d9f @u0 @u1 @u2 @x3))))
    :qid haseqTm_refine_4f270e33e23275479ca9be199c6d2d9f))
  :named haseqTm_refine_4f270e33e23275479ca9be199c6d2d9f))
(declare-fun Tm_refine_28b3529e604de38cfa56254e079a0089 (Term Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(410,27-410,88); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_28b3529e604de38cfa56254e079a0089 @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_28b3529e604de38cfa56254e079a0089 @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_28b3529e604de38cfa56254e079a0089))
  :named refinement_kinding_Tm_refine_28b3529e604de38cfa56254e079a0089))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(410,27-410,88); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_28b3529e604de38cfa56254e079a0089 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Prims.fst(410,27-410,88); use=M02_Types.Monad.fst(55,4-67,52)
      (forall ((@x4 Term))
       (! ;; def=Prims.fst(410,73-410,87); use=M02_Types.Monad.fst(55,4-67,52)
        (implies
         ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(55,4-67,52)
         (Valid
          ;; def=Prims.fst(410,73-410,79); use=M02_Types.Monad.fst(55,4-67,52)
          (ApplyTT @x2 @x4))
         ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(55,4-67,52)
         (Valid
          ;; def=Prims.fst(410,84-410,87); use=M02_Types.Monad.fst(55,4-67,52)
          (ApplyTT @x3 @x4)))
        :pattern ((ApplyTT @x3 @x4))
        :qid refinement_interpretation_Tm_refine_28b3529e604de38cfa56254e079a0089.1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_28b3529e604de38cfa56254e079a0089 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_28b3529e604de38cfa56254e079a0089))
  :named refinement_interpretation_Tm_refine_28b3529e604de38cfa56254e079a0089))
; haseq for Tm_refine_28b3529e604de38cfa56254e079a0089
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(410,27-410,88); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_28b3529e604de38cfa56254e079a0089 @x0 @x1)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_28b3529e604de38cfa56254e079a0089 @x0 @x1))))
    :qid haseqTm_refine_28b3529e604de38cfa56254e079a0089))
  :named haseqTm_refine_28b3529e604de38cfa56254e079a0089))
(declare-fun Tm_refine_0589ad0a61c037dad4c4d27911c4a462 (Universe) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Universe))
   (! (HasType (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 @u0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 @u0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_0589ad0a61c037dad4c4d27911c4a462))
  :named refinement_kinding_Tm_refine_0589ad0a61c037dad4c4d27911c4a462))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 @u2))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(55,4-67,52)
      (not
       ;; def=M02_Types.Monad.fst(53,41-53,43); use=M02_Types.Monad.fst(55,10-55,12)
       (BoxBool_proj_0
        (Prims.uu___is_Nil
         @u2
         x_5291e79fe22e1a22b149e48ad1f333b7_3
         x_9532d2d16117ce60589a9083bb3becbe_6)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 @u2)))
    :qid refinement_interpretation_Tm_refine_0589ad0a61c037dad4c4d27911c4a462))
  :named refinement_interpretation_Tm_refine_0589ad0a61c037dad4c4d27911c4a462))
; haseq for Tm_refine_0589ad0a61c037dad4c4d27911c4a462
;;; Fact-ids: 
(assert
 (! ;; def=Prims.fst(397,19-397,21); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Universe))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 @u0)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 @u0))))
    :qid haseqTm_refine_0589ad0a61c037dad4c4d27911c4a462))
  :named haseqTm_refine_0589ad0a61c037dad4c4d27911c4a462))
(declare-fun Tm_refine_7ba254d355809bc67781852bce763dc4 (Universe Term Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,41-57,14); use=M02_Types.Monad.fst(55,10-57,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_7ba254d355809bc67781852bce763dc4 @u0 @x1 @x2) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_7ba254d355809bc67781852bce763dc4 @u0 @x1 @x2) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_7ba254d355809bc67781852bce763dc4))
  :named refinement_kinding_Tm_refine_7ba254d355809bc67781852bce763dc4))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,41-57,14); use=M02_Types.Monad.fst(55,10-57,14)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_7ba254d355809bc67781852bce763dc4 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=M02_Types.Monad.fst(53,41-57,14); use=M02_Types.Monad.fst(55,10-57,14)
      (=
       x_9532d2d16117ce60589a9083bb3becbe_6
       (Prims.Cons @u2 x_5291e79fe22e1a22b149e48ad1f333b7_3 @x3 @x4))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_7ba254d355809bc67781852bce763dc4 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_7ba254d355809bc67781852bce763dc4))
  :named refinement_interpretation_Tm_refine_7ba254d355809bc67781852bce763dc4))
; haseq for Tm_refine_7ba254d355809bc67781852bce763dc4
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,41-57,14); use=M02_Types.Monad.fst(55,10-57,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_7ba254d355809bc67781852bce763dc4 @u0 @x1 @x2)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_7ba254d355809bc67781852bce763dc4 @u0 @x1 @x2))))
    :qid haseqTm_refine_7ba254d355809bc67781852bce763dc4))
  :named haseqTm_refine_7ba254d355809bc67781852bce763dc4))

(declare-fun Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d (Universe Universe Universe Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,69-53,70); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Universe) (@u1 Universe) (@u2 Universe) (@x3 Term))
   (! (HasType (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d @u0 @u1 @u2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d @u0 @u1 @u2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d))
  :named refinement_kinding_Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,69-53,70); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe) (@u4 Universe) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d @u2 @u3 @u4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=M02_Types.Monad.fst(53,69-53,70); use=M02_Types.Monad.fst(55,4-67,52)
      (= x_46f1c4a5584aa156b80fe0f325f80f97_8 @x5)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d @u2 @u3 @u4 @x5)))
    :qid refinement_interpretation_Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d))
  :named refinement_interpretation_Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d))
; haseq for Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(53,69-53,70); use=M02_Types.Monad.fst(55,4-67,52)
  (forall ((@u0 Universe) (@u1 Universe) (@u2 Universe) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d @u0 @u1 @u2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d @u0 @u1 @u2 @x3))))
    :qid haseqTm_refine_eaa0ebe3a38c1360ecc38b55d63f978d))
  :named haseqTm_refine_eaa0ebe3a38c1360ecc38b55d63f978d))


(declare-fun Tm_refine_eee424e01be2643ec690859133e546b9 (Universe Universe Universe Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(54,12-54,87); use=M02_Types.Monad.fst(58,8-58,23)
  (forall ((@u0 Universe) (@u1 Universe) (@u2 Universe) (@x3 Term))
   (! (HasType (Tm_refine_eee424e01be2643ec690859133e546b9 @u0 @u1 @u2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_eee424e01be2643ec690859133e546b9 @u0 @u1 @u2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_eee424e01be2643ec690859133e546b9))
  :named refinement_kinding_Tm_refine_eee424e01be2643ec690859133e546b9))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(54,12-54,87); use=M02_Types.Monad.fst(58,8-58,23)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe) (@u4 Universe) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_eee424e01be2643ec690859133e546b9 @u2 @u3 @u4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=M02_Types.Monad.fst(54,12-54,87); use=M02_Types.Monad.fst(58,8-58,23)
      (=
       (FStar.List.Tot.Base.concatMap
        @u3
        @u2
        x_5291e79fe22e1a22b149e48ad1f333b7_3
        x_d1b9400b70639cdd98adb2a0203ec3f4_5
        (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 @u2 @u3 @u4)
        @x5)
       (FStar.List.Tot.Base.concatMap
        @u4
        @u2
        x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
        x_d1b9400b70639cdd98adb2a0203ec3f4_5
        x_46f1c4a5584aa156b80fe0f325f80f97_8
        (FStar.List.Tot.Base.concatMap
         @u3
         @u4
         x_5291e79fe22e1a22b149e48ad1f333b7_3
         x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
         x_a6d7374e9c8eeb8261a65adfca25792e_7
         @x5)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_eee424e01be2643ec690859133e546b9 @u2 @u3 @u4 @x5)))
    :qid refinement_interpretation_Tm_refine_eee424e01be2643ec690859133e546b9))
  :named refinement_interpretation_Tm_refine_eee424e01be2643ec690859133e546b9))
; haseq for Tm_refine_eee424e01be2643ec690859133e546b9
;;; Fact-ids: 
(assert
 (! ;; def=M02_Types.Monad.fst(54,12-54,87); use=M02_Types.Monad.fst(58,8-58,23)
  (forall ((@u0 Universe) (@u1 Universe) (@u2 Universe) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_eee424e01be2643ec690859133e546b9 @u0 @u1 @u2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_eee424e01be2643ec690859133e546b9 @u0 @u1 @u2 @x3))))
    :qid haseqTm_refine_eee424e01be2643ec690859133e546b9))
  :named haseqTm_refine_eee424e01be2643ec690859133e546b9))




; Encoding query formula : forall (p: Prims.pure_post Prims.unit)
;   (_:
;   _:
;   Prims.unit
;     { forall (pure_result: Prims.unit).
;         FStar.List.Tot.Base.concatMap (fun y -> FStar.List.Tot.Base.concatMap g (f y)) xs ==
;         FStar.List.Tot.Base.concatMap g (FStar.List.Tot.Base.concatMap f xs) ==>
;         p pure_result }) (k: Prims.pure_post Prims.unit)
;   (_: _: Prims.unit{forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x})
;   (_: _: Prims.unit{~(Nil? xs)}) (b: a) (b: Prims.list a) (_: _: Prims.unit{xs == b :: b})
;   (any_result: (_: b -> Prims.list c)) (_: _: Prims.unit{g == any_result}) (pure_result: Prims.unit)
;   (_:
;   _:
;   Prims.unit
;     { FStar.List.Tot.Base.concatMap (fun y -> FStar.List.Tot.Base.concatMap g (f y)) b ==
;       FStar.List.Tot.Base.concatMap g (FStar.List.Tot.Base.concatMap f b) }).
;   (* - Could not prove goal #1 *)
;   (match
;       match f b with
;       | [] -> []
;       | a :: tl -> g a @ FStar.List.Tot.Base.concatMap g tl
;     with
;     | [] -> FStar.List.Tot.Base.concatMap (fun y -> FStar.List.Tot.Base.concatMap g (f y)) b
;     | a :: tl ->
;       a :: (tl @ FStar.List.Tot.Base.concatMap (fun y -> FStar.List.Tot.Base.concatMap g (f y)) b)) ==
;   (match
;       match f b with
;       | [] -> FStar.List.Tot.Base.concatMap f b
;       | a :: tl -> a :: (tl @ FStar.List.Tot.Base.concatMap f b)
;     with
;     | [] -> []
;     | a :: tl -> g a @ FStar.List.Tot.Base.concatMap g tl)
; Context: While encoding a query
; While typechecking the top-level declaration `let rec concatMap_assoc`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall
     ((@x0 Term)
      (@x1 Term)
      (@x2 Term)
      (@x3 Term)
      (@x4 Term)
      (@x5 Term)
      (@x6 Term)
      (@x7 Term)
      (@x8 Term)
      (@x9 Term)
      (@x10 Term)
      (@x11 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       (HasType @x1 (Tm_refine_4f270e33e23275479ca9be199c6d2d9f uu___1191 uu___1193 uu___1192 @x0))
       (HasType @x2 (Prims.pure_post U_zero Prims.unit))
       (HasType @x3 (Tm_refine_28b3529e604de38cfa56254e079a0089 @x0 @x2))
       (HasType @x4 (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 uu___1193))
       (HasType @x5 x_5291e79fe22e1a22b149e48ad1f333b7_3)
       (HasType @x6 (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3))
       (HasType @x7 (Tm_refine_7ba254d355809bc67781852bce763dc4 uu___1193 @x5 @x6))
       (HasType @x8 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd uu___1191 uu___1192))
       (HasType @x9 (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d uu___1191 uu___1192 uu___1193 @x8))
       (HasType @x10 Prims.unit)
       (HasType @x11 (Tm_refine_eee424e01be2643ec690859133e546b9 uu___1191 uu___1193 uu___1192 @x6)))
      ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
      (or
       label_1
       ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
       (=
        (let
          ((@lb12
            (let ((@lb12 (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x5)))
             (ite
              (is-Prims.Nil @lb12)
              (Prims.Nil uu___1191 x_d1b9400b70639cdd98adb2a0203ec3f4_5)
              (ite
               (is-Prims.Cons @lb12)
               (FStar.List.Tot.Base.append
                uu___1191
                x_d1b9400b70639cdd98adb2a0203ec3f4_5
                (ApplyTT x_46f1c4a5584aa156b80fe0f325f80f97_8 (Prims.Cons_@hd @lb12))
                (FStar.List.Tot.Base.concatMap
                 uu___1192
                 uu___1191
                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                 x_d1b9400b70639cdd98adb2a0203ec3f4_5
                 x_46f1c4a5584aa156b80fe0f325f80f97_8
                 (Prims.Cons_@tl @lb12)))
               Tm_unit)))))
         (ite
          (is-Prims.Nil @lb12)
          (FStar.List.Tot.Base.concatMap
           uu___1193
           uu___1191
           x_5291e79fe22e1a22b149e48ad1f333b7_3
           x_d1b9400b70639cdd98adb2a0203ec3f4_5
           (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
           @x6)
          (ite
           (is-Prims.Cons @lb12)
           (Prims.Cons
            uu___1191
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (Prims.Cons_@hd @lb12)
            (FStar.List.Tot.Base.append
             uu___1191
             x_d1b9400b70639cdd98adb2a0203ec3f4_5
             (Prims.Cons_@tl @lb12)
             (FStar.List.Tot.Base.concatMap
              uu___1193
              uu___1191
              x_5291e79fe22e1a22b149e48ad1f333b7_3
              x_d1b9400b70639cdd98adb2a0203ec3f4_5
              (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
              @x6)))
           Tm_unit)))
        (let
          ((@lb12
            (let ((@lb12 (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x5)))
             (ite
              (is-Prims.Nil @lb12)
              (FStar.List.Tot.Base.concatMap
               uu___1193
               uu___1192
               x_5291e79fe22e1a22b149e48ad1f333b7_3
               x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
               x_a6d7374e9c8eeb8261a65adfca25792e_7
               @x6)
              (ite
               (is-Prims.Cons @lb12)
               (Prims.Cons
                uu___1192
                x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                (Prims.Cons_@hd @lb12)
                (FStar.List.Tot.Base.append
                 uu___1192
                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                 (Prims.Cons_@tl @lb12)
                 (FStar.List.Tot.Base.concatMap
                  uu___1193
                  uu___1192
                  x_5291e79fe22e1a22b149e48ad1f333b7_3
                  x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                  x_a6d7374e9c8eeb8261a65adfca25792e_7
                  @x6)))
               Tm_unit)))))
         (ite
          (is-Prims.Nil @lb12)
          (Prims.Nil uu___1191 x_d1b9400b70639cdd98adb2a0203ec3f4_5)
          (ite
           (is-Prims.Cons @lb12)
           (FStar.List.Tot.Base.append
            uu___1191
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (ApplyTT x_46f1c4a5584aa156b80fe0f325f80f97_8 (Prims.Cons_@hd @lb12))
            (FStar.List.Tot.Base.concatMap
             uu___1192
             uu___1191
             x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
             x_d1b9400b70639cdd98adb2a0203ec3f4_5
             x_46f1c4a5584aa156b80fe0f325f80f97_8
             (Prims.Cons_@tl @lb12)))
           Tm_unit))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.concatMap_assoc, 2)
; STATUS: unknown because (incomplete quantifiers)
; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(push) ;; push{0
; <fuel='2' ifuel='2'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall
     ((@x0 Term)
      (@x1 Term)
      (@x2 Term)
      (@x3 Term)
      (@x4 Term)
      (@x5 Term)
      (@x6 Term)
      (@x7 Term)
      (@x8 Term)
      (@x9 Term)
      (@x10 Term)
      (@x11 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       (HasType @x1 (Tm_refine_4f270e33e23275479ca9be199c6d2d9f uu___1191 uu___1193 uu___1192 @x0))
       (HasType @x2 (Prims.pure_post U_zero Prims.unit))
       (HasType @x3 (Tm_refine_28b3529e604de38cfa56254e079a0089 @x0 @x2))
       (HasType @x4 (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 uu___1193))
       (HasType @x5 x_5291e79fe22e1a22b149e48ad1f333b7_3)
       (HasType @x6 (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3))
       (HasType @x7 (Tm_refine_7ba254d355809bc67781852bce763dc4 uu___1193 @x5 @x6))
       (HasType @x8 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd uu___1191 uu___1192))
       (HasType @x9 (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d uu___1191 uu___1192 uu___1193 @x8))
       (HasType @x10 Prims.unit)
       (HasType @x11 (Tm_refine_eee424e01be2643ec690859133e546b9 uu___1191 uu___1193 uu___1192 @x6)))
      ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
      (or
       label_1
       ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
       (=
        (let
          ((@lb12
            (let ((@lb12 (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x5)))
             (ite
              (is-Prims.Nil @lb12)
              (Prims.Nil uu___1191 x_d1b9400b70639cdd98adb2a0203ec3f4_5)
              (ite
               (is-Prims.Cons @lb12)
               (FStar.List.Tot.Base.append
                uu___1191
                x_d1b9400b70639cdd98adb2a0203ec3f4_5
                (ApplyTT x_46f1c4a5584aa156b80fe0f325f80f97_8 (Prims.Cons_@hd @lb12))
                (FStar.List.Tot.Base.concatMap
                 uu___1192
                 uu___1191
                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                 x_d1b9400b70639cdd98adb2a0203ec3f4_5
                 x_46f1c4a5584aa156b80fe0f325f80f97_8
                 (Prims.Cons_@tl @lb12)))
               Tm_unit)))))
         (ite
          (is-Prims.Nil @lb12)
          (FStar.List.Tot.Base.concatMap
           uu___1193
           uu___1191
           x_5291e79fe22e1a22b149e48ad1f333b7_3
           x_d1b9400b70639cdd98adb2a0203ec3f4_5
           (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
           @x6)
          (ite
           (is-Prims.Cons @lb12)
           (Prims.Cons
            uu___1191
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (Prims.Cons_@hd @lb12)
            (FStar.List.Tot.Base.append
             uu___1191
             x_d1b9400b70639cdd98adb2a0203ec3f4_5
             (Prims.Cons_@tl @lb12)
             (FStar.List.Tot.Base.concatMap
              uu___1193
              uu___1191
              x_5291e79fe22e1a22b149e48ad1f333b7_3
              x_d1b9400b70639cdd98adb2a0203ec3f4_5
              (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
              @x6)))
           Tm_unit)))
        (let
          ((@lb12
            (let ((@lb12 (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x5)))
             (ite
              (is-Prims.Nil @lb12)
              (FStar.List.Tot.Base.concatMap
               uu___1193
               uu___1192
               x_5291e79fe22e1a22b149e48ad1f333b7_3
               x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
               x_a6d7374e9c8eeb8261a65adfca25792e_7
               @x6)
              (ite
               (is-Prims.Cons @lb12)
               (Prims.Cons
                uu___1192
                x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                (Prims.Cons_@hd @lb12)
                (FStar.List.Tot.Base.append
                 uu___1192
                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                 (Prims.Cons_@tl @lb12)
                 (FStar.List.Tot.Base.concatMap
                  uu___1193
                  uu___1192
                  x_5291e79fe22e1a22b149e48ad1f333b7_3
                  x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                  x_a6d7374e9c8eeb8261a65adfca25792e_7
                  @x6)))
               Tm_unit)))))
         (ite
          (is-Prims.Nil @lb12)
          (Prims.Nil uu___1191 x_d1b9400b70639cdd98adb2a0203ec3f4_5)
          (ite
           (is-Prims.Cons @lb12)
           (FStar.List.Tot.Base.append
            uu___1191
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (ApplyTT x_46f1c4a5584aa156b80fe0f325f80f97_8 (Prims.Cons_@hd @lb12))
            (FStar.List.Tot.Base.concatMap
             uu___1192
             uu___1191
             x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
             x_d1b9400b70639cdd98adb2a0203ec3f4_5
             x_46f1c4a5584aa156b80fe0f325f80f97_8
             (Prims.Cons_@tl @lb12)))
           Tm_unit))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.concatMap_assoc, 2)
; STATUS: unknown because (incomplete quantifiers)
; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(push) ;; push{0
; <fuel='4' ifuel='2'>
;;; Fact-ids: 
(assert
 (! (= MaxFuel (SFuel (SFuel (SFuel (SFuel ZFuel))))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall
     ((@x0 Term)
      (@x1 Term)
      (@x2 Term)
      (@x3 Term)
      (@x4 Term)
      (@x5 Term)
      (@x6 Term)
      (@x7 Term)
      (@x8 Term)
      (@x9 Term)
      (@x10 Term)
      (@x11 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       (HasType @x1 (Tm_refine_4f270e33e23275479ca9be199c6d2d9f uu___1191 uu___1193 uu___1192 @x0))
       (HasType @x2 (Prims.pure_post U_zero Prims.unit))
       (HasType @x3 (Tm_refine_28b3529e604de38cfa56254e079a0089 @x0 @x2))
       (HasType @x4 (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 uu___1193))
       (HasType @x5 x_5291e79fe22e1a22b149e48ad1f333b7_3)
       (HasType @x6 (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3))
       (HasType @x7 (Tm_refine_7ba254d355809bc67781852bce763dc4 uu___1193 @x5 @x6))
       (HasType @x8 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd uu___1191 uu___1192))
       (HasType @x9 (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d uu___1191 uu___1192 uu___1193 @x8))
       (HasType @x10 Prims.unit)
       (HasType @x11 (Tm_refine_eee424e01be2643ec690859133e546b9 uu___1191 uu___1193 uu___1192 @x6)))
      ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
      (or
       label_1
       ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
       (=
        (let
          ((@lb12
            (let ((@lb12 (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x5)))
             (ite
              (is-Prims.Nil @lb12)
              (Prims.Nil uu___1191 x_d1b9400b70639cdd98adb2a0203ec3f4_5)
              (ite
               (is-Prims.Cons @lb12)
               (FStar.List.Tot.Base.append
                uu___1191
                x_d1b9400b70639cdd98adb2a0203ec3f4_5
                (ApplyTT x_46f1c4a5584aa156b80fe0f325f80f97_8 (Prims.Cons_@hd @lb12))
                (FStar.List.Tot.Base.concatMap
                 uu___1192
                 uu___1191
                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                 x_d1b9400b70639cdd98adb2a0203ec3f4_5
                 x_46f1c4a5584aa156b80fe0f325f80f97_8
                 (Prims.Cons_@tl @lb12)))
               Tm_unit)))))
         (ite
          (is-Prims.Nil @lb12)
          (FStar.List.Tot.Base.concatMap
           uu___1193
           uu___1191
           x_5291e79fe22e1a22b149e48ad1f333b7_3
           x_d1b9400b70639cdd98adb2a0203ec3f4_5
           (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
           @x6)
          (ite
           (is-Prims.Cons @lb12)
           (Prims.Cons
            uu___1191
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (Prims.Cons_@hd @lb12)
            (FStar.List.Tot.Base.append
             uu___1191
             x_d1b9400b70639cdd98adb2a0203ec3f4_5
             (Prims.Cons_@tl @lb12)
             (FStar.List.Tot.Base.concatMap
              uu___1193
              uu___1191
              x_5291e79fe22e1a22b149e48ad1f333b7_3
              x_d1b9400b70639cdd98adb2a0203ec3f4_5
              (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
              @x6)))
           Tm_unit)))
        (let
          ((@lb12
            (let ((@lb12 (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x5)))
             (ite
              (is-Prims.Nil @lb12)
              (FStar.List.Tot.Base.concatMap
               uu___1193
               uu___1192
               x_5291e79fe22e1a22b149e48ad1f333b7_3
               x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
               x_a6d7374e9c8eeb8261a65adfca25792e_7
               @x6)
              (ite
               (is-Prims.Cons @lb12)
               (Prims.Cons
                uu___1192
                x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                (Prims.Cons_@hd @lb12)
                (FStar.List.Tot.Base.append
                 uu___1192
                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                 (Prims.Cons_@tl @lb12)
                 (FStar.List.Tot.Base.concatMap
                  uu___1193
                  uu___1192
                  x_5291e79fe22e1a22b149e48ad1f333b7_3
                  x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                  x_a6d7374e9c8eeb8261a65adfca25792e_7
                  @x6)))
               Tm_unit)))))
         (ite
          (is-Prims.Nil @lb12)
          (Prims.Nil uu___1191 x_d1b9400b70639cdd98adb2a0203ec3f4_5)
          (ite
           (is-Prims.Cons @lb12)
           (FStar.List.Tot.Base.append
            uu___1191
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (ApplyTT x_46f1c4a5584aa156b80fe0f325f80f97_8 (Prims.Cons_@hd @lb12))
            (FStar.List.Tot.Base.concatMap
             uu___1192
             uu___1191
             x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
             x_d1b9400b70639cdd98adb2a0203ec3f4_5
             x_46f1c4a5584aa156b80fe0f325f80f97_8
             (Prims.Cons_@tl @lb12)))
           Tm_unit))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.concatMap_assoc, 2)
; STATUS: unknown because (incomplete quantifiers)
; Z3 invocation started by F*
; F* version: 2026.03.24~dev -- commit hash: unset
; Z3 version (according to F*): 4.13.3

(push) ;; push{0
; <fuel='8' ifuel='2'>
;;; Fact-ids: 
(assert
 (! (= MaxFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel ZFuel)))))))))
  :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall
     ((@x0 Term)
      (@x1 Term)
      (@x2 Term)
      (@x3 Term)
      (@x4 Term)
      (@x5 Term)
      (@x6 Term)
      (@x7 Term)
      (@x8 Term)
      (@x9 Term)
      (@x10 Term)
      (@x11 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       (HasType @x1 (Tm_refine_4f270e33e23275479ca9be199c6d2d9f uu___1191 uu___1193 uu___1192 @x0))
       (HasType @x2 (Prims.pure_post U_zero Prims.unit))
       (HasType @x3 (Tm_refine_28b3529e604de38cfa56254e079a0089 @x0 @x2))
       (HasType @x4 (Tm_refine_0589ad0a61c037dad4c4d27911c4a462 uu___1193))
       (HasType @x5 x_5291e79fe22e1a22b149e48ad1f333b7_3)
       (HasType @x6 (Prims.list uu___1193 x_5291e79fe22e1a22b149e48ad1f333b7_3))
       (HasType @x7 (Tm_refine_7ba254d355809bc67781852bce763dc4 uu___1193 @x5 @x6))
       (HasType @x8 (Tm_arrow_1ac033956bc64594ebab90a7d66eacdd uu___1191 uu___1192))
       (HasType @x9 (Tm_refine_eaa0ebe3a38c1360ecc38b55d63f978d uu___1191 uu___1192 uu___1193 @x8))
       (HasType @x10 Prims.unit)
       (HasType @x11 (Tm_refine_eee424e01be2643ec690859133e546b9 uu___1191 uu___1193 uu___1192 @x6)))
      ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
      (or
       label_1
       ;; def=M02_Types.Monad.fst(59,15-62,9); use=M02_Types.Monad.fst(59,8-59,14)
       (=
        (let
          ((@lb12
            (let ((@lb12 (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x5)))
             (ite
              (is-Prims.Nil @lb12)
              (Prims.Nil uu___1191 x_d1b9400b70639cdd98adb2a0203ec3f4_5)
              (ite
               (is-Prims.Cons @lb12)
               (FStar.List.Tot.Base.append
                uu___1191
                x_d1b9400b70639cdd98adb2a0203ec3f4_5
                (ApplyTT x_46f1c4a5584aa156b80fe0f325f80f97_8 (Prims.Cons_@hd @lb12))
                (FStar.List.Tot.Base.concatMap
                 uu___1192
                 uu___1191
                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                 x_d1b9400b70639cdd98adb2a0203ec3f4_5
                 x_46f1c4a5584aa156b80fe0f325f80f97_8
                 (Prims.Cons_@tl @lb12)))
               Tm_unit)))))
         (ite
          (is-Prims.Nil @lb12)
          (FStar.List.Tot.Base.concatMap
           uu___1193
           uu___1191
           x_5291e79fe22e1a22b149e48ad1f333b7_3
           x_d1b9400b70639cdd98adb2a0203ec3f4_5
           (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
           @x6)
          (ite
           (is-Prims.Cons @lb12)
           (Prims.Cons
            uu___1191
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (Prims.Cons_@hd @lb12)
            (FStar.List.Tot.Base.append
             uu___1191
             x_d1b9400b70639cdd98adb2a0203ec3f4_5
             (Prims.Cons_@tl @lb12)
             (FStar.List.Tot.Base.concatMap
              uu___1193
              uu___1191
              x_5291e79fe22e1a22b149e48ad1f333b7_3
              x_d1b9400b70639cdd98adb2a0203ec3f4_5
              (Tm_abs_a4f6ef1cd3a07bea5cafde5be09cb3e0 uu___1191 uu___1193 uu___1192)
              @x6)))
           Tm_unit)))
        (let
          ((@lb12
            (let ((@lb12 (ApplyTT x_a6d7374e9c8eeb8261a65adfca25792e_7 @x5)))
             (ite
              (is-Prims.Nil @lb12)
              (FStar.List.Tot.Base.concatMap
               uu___1193
               uu___1192
               x_5291e79fe22e1a22b149e48ad1f333b7_3
               x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
               x_a6d7374e9c8eeb8261a65adfca25792e_7
               @x6)
              (ite
               (is-Prims.Cons @lb12)
               (Prims.Cons
                uu___1192
                x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                (Prims.Cons_@hd @lb12)
                (FStar.List.Tot.Base.append
                 uu___1192
                 x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                 (Prims.Cons_@tl @lb12)
                 (FStar.List.Tot.Base.concatMap
                  uu___1193
                  uu___1192
                  x_5291e79fe22e1a22b149e48ad1f333b7_3
                  x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
                  x_a6d7374e9c8eeb8261a65adfca25792e_7
                  @x6)))
               Tm_unit)))))
         (ite
          (is-Prims.Nil @lb12)
          (Prims.Nil uu___1191 x_d1b9400b70639cdd98adb2a0203ec3f4_5)
          (ite
           (is-Prims.Cons @lb12)
           (FStar.List.Tot.Base.append
            uu___1191
            x_d1b9400b70639cdd98adb2a0203ec3f4_5
            (ApplyTT x_46f1c4a5584aa156b80fe0f325f80f97_8 (Prims.Cons_@hd @lb12))
            (FStar.List.Tot.Base.concatMap
             uu___1192
             uu___1191
             x_1efe7eaa9f709f6ffdd2dd66ac0c589d_4
             x_d1b9400b70639cdd98adb2a0203ec3f4_5
             x_46f1c4a5584aa156b80fe0f325f80f97_8
             (Prims.Cons_@tl @lb12)))
           Tm_unit))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (M02_Types.Monad.concatMap_assoc, 2)
; STATUS: unknown because (incomplete quantifiers)
