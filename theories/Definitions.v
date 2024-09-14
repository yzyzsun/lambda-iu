(* generated by Ott 0.33 from: lambda-iu.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.


Set Implicit Arguments.

Definition one (C : Type) (item : C) : list C := cons item nil.
Notation "x ~ a" := (one (x, a)) (at level 50) : list_scope.

Fixpoint dom
  (C : Type) (E : list (nat*C)) : list nat :=
  match E with
    | nil => nil
    | (x, _) :: E' => x :: dom E'
  end.

Definition binds
  (A : Type) (x : nat) (a : A) (E : list (nat*A)) : Prop :=
  In (x, a) E.

Definition fresh
  (A : Type) (x : nat) (E : list (nat*A)) : Prop :=
  ~ In x (dom E).

Inductive uniq (A : Type) : list (nat*A) -> Prop :=
  | uniq_nil :
      uniq nil
  | uniq_cons : forall x a E,
      uniq E ->
      fresh x E ->
      uniq (x ~ a ++ E).

Unset Implicit Arguments.

Definition var : Set := nat. (*r variable/label *)

Inductive typ : Set :=  (*r types *)
 | t_top : typ (*r top type *)
 | t_bot : typ (*r bottom type *)
 | t_null : typ (*r null type *)
 | t_int : typ (*r integer type *)
 | t_arrow (A:typ) (B:typ) (*r function type *)
 | t_rcd (l:var) (A:typ) (*r record type *)
 | t_and (A:typ) (B:typ) (*r intersection type *)
 | t_or (A:typ) (B:typ) (*r union type *).

Inductive styp : Set :=  (*r source types *)
 | st_int : styp (*r integer type *)
 | st_arrow (As:styp) (Bs:styp) (*r function type *)
 | st_narrow (P:nptyp) (Bs:styp) (*r function type with named parameters *)
with nptyp : Set :=  (*r named parameter types *)
 | pt_empty : nptyp (*r empty *)
 | pt_required (P:nptyp) (l:var) (As:styp) (*r required parameter *)
 | pt_optional (P:nptyp) (l:var) (As:styp) (*r optional parameter *).

Inductive exp : Set :=  (*r expressions *)
 | e_top : exp (*r top value *)
 | e_null : exp (*r null value *)
 | e_int : exp (*r integer literal *)
 | e_var (x:var) (*r variable *)
 | e_abs (x:var) (A:typ) (e:exp) (B:typ) (*r abstraction *)
 | e_app (e1:exp) (e2:exp) (*r application *)
 | e_rcd (l:var) (e:exp) (*r record *)
 | e_prj (e:exp) (l:var) (*r projection *)
 | e_merge (e1:exp) (e2:exp) (*r merging *)
 | e_switch (e0:exp) (x:var) (A:typ) (e1:exp) (B:typ) (e2:exp) (*r type switch *)
 | e_letin (letin5:letin) (e:exp)
with letin : Set :=  (*r let-in bindings *)
 | letin_identity : letin
 | letin_composition (letin5:letin) (letin':letin)
 | letin_bind (x:var) (e:exp).

Definition sctx : Set := list (nat * styp).

Inductive sexp : Set :=  (*r source expressions *)
 | se_int : sexp (*r integer literal *)
 | se_var (x:var) (*r variable *)
 | se_abs (x:var) (As:styp) (es:sexp) (*r abstraction *)
 | se_app (es1:sexp) (es2:sexp) (*r application *)
 | se_nabs (p:npexp) (es:sexp) (*r abstraction with named parameters *)
 | se_napp (es:sexp) (a:narg) (*r application to named arguments *)
with npexp : Set :=  (*r named parameters *)
 | par_empty : npexp (*r empty *)
 | par_required (p:npexp) (l:var) (As:styp) (*r required parameter *)
 | par_optional (p:npexp) (l:var) (es:sexp) (*r optional parameter *)
with narg : Set :=  (*r named arguments *)
 | arg_empty : narg (*r empty *)
 | arg_field (a:narg) (l:var) (es:sexp) (*r field *).

Definition ctx : Set := list (nat * typ).

(** subrules *)
Fixpoint is_val_of_exp (e_5:exp) : Prop :=
  match e_5 with
  | e_top => (True)
  | e_null => (True)
  | e_int => (True)
  | (e_var x) => False
  | (e_abs x A e B) => (True)
  | (e_app e1 e2) => False
  | (e_rcd l e) => ((is_val_of_exp e))
  | (e_prj e l) => False
  | (e_merge e1 e2) => ((is_val_of_exp e1) /\ (is_val_of_exp e2))
  | (e_switch e0 x A e1 B e2) => False
  | (e_letin letin5 e) => False
end.

Fixpoint remove (l : nat) (a : narg) :=
  match a with
    | arg_empty => arg_empty
    | arg_field a' l' es => let a'' := remove l a' in
                            if l =? l' then a''
                            else arg_field a'' l' es
  end.

(** definitions *)

(** funs Trans *)
Fixpoint ptrans (x1:nptyp) : typ:=
  match x1 with
  | pt_empty => t_top
  | (pt_required P l As) => (t_and  (ptrans P )  (t_rcd l  (trans As ) ))
  | (pt_optional P l As) => (t_and  (ptrans P )  (t_rcd l (t_or  (trans As )  t_null)))
end
with trans (x1:styp) : typ:=
  match x1 with
  | st_int => t_int
  | (st_arrow As Bs) => (t_arrow  (trans As )   (trans Bs ) )
  | (st_narrow P Bs) => (t_arrow  (ptrans P )   (trans Bs ) )
end.

(** definitions *)

(** funs CtxTrans *)
Fixpoint ctxtrans (x1:sctx) : ctx:=
  match x1 with
  |  nil  =>  nil 
  |  (( x , As ):: Gs )  =>  (( x ,  (trans As )  )::  (ctxtrans Gs )  ) 
end.

(** definitions *)

(* defns Target *)
Inductive sub : typ -> typ -> Prop :=    (* defn sub *)
 | Sub_Top : forall (A:typ),
     sub A t_top
 | Sub_Bot : forall (A:typ),
     sub t_bot A
 | Sub_Null : 
     sub t_null t_null
 | Sub_Int : 
     sub t_int t_int
 | Sub_Arrow : forall (A1 A2 B1 B2:typ),
     sub B1 A1 ->
     sub A2 B2 ->
     sub (t_arrow A1 A2) (t_arrow B1 B2)
 | Sub_Rcd : forall (l:var) (A B:typ),
     sub A B ->
     sub (t_rcd l A) (t_rcd l B)
 | Sub_And : forall (A B C:typ),
     sub A B ->
     sub A C ->
     sub A (t_and B C)
 | Sub_AndL : forall (A B C:typ),
     sub A C ->
     sub (t_and A B) C
 | Sub_AndR : forall (A B C:typ),
     sub B C ->
     sub (t_and A B) C
 | Sub_Or : forall (A B C:typ),
     sub A C ->
     sub B C ->
     sub (t_or A B) C
 | Sub_OrL : forall (A B C:typ),
     sub A B ->
     sub A (t_or B C)
 | Sub_OrR : forall (A B C:typ),
     sub A C ->
     sub A (t_or B C)
with typing : ctx -> exp -> typ -> Prop :=    (* defn typing *)
 | Typ_Top : forall (G:ctx),
      (uniq G )  ->
     typing G e_top t_top
 | Typ_Int : forall (G:ctx),
      (uniq G )  ->
     typing G e_int t_int
 | Typ_Var : forall (G:ctx) (x:var) (A:typ),
      (binds x A G )  ->
      (uniq G )  ->
     typing G (e_var x) A
 | Typ_Abs : forall (G:ctx) (x:var) (A:typ) (e:exp) (B:typ),
     typing  (( x , A ):: G )  e B ->
     typing G  ( (e_abs x A e B) )  (t_arrow A B)
 | Typ_App : forall (G:ctx) (e1 e2:exp) (B A:typ),
     typing G e1 (t_arrow A B) ->
     typing G e2 A ->
     typing G (e_app e1 e2) B
 | Typ_Rcd : forall (G:ctx) (l:var) (e:exp) (A:typ),
     typing G e A ->
     typing G (e_rcd l e) (t_rcd l A)
 | Typ_Prj : forall (G:ctx) (e:exp) (l:var) (A:typ),
     typing G e (t_rcd l A) ->
     typing G (e_prj e l) A
 | Typ_Merge : forall (G:ctx) (e1 e2:exp) (A B:typ),
     typing G e1 A ->
     typing G e2 B ->
     typing G (e_merge e1 e2) (t_and A B)
 | Typ_Switch : forall (G:ctx) (e0:exp) (x:var) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing G e0 (t_or A B) ->
     typing  (( x , A ):: G )  e1 C ->
     typing  (( x , B ):: G )  e2 C ->
     typing G (e_switch e0 x A e1 B e2) C
 | Typ_Let : forall (G:ctx) (letin5:letin) (e:exp) (A:typ) (G':ctx),
     letbind G letin5 G' ->
     typing G' e A ->
     typing G (e_letin letin5 e) A
 | Typ_Sub : forall (G:ctx) (e:exp) (B A:typ),
     typing G e A ->
     sub A B ->
     typing G e B
with letbind : ctx -> letin -> ctx -> Prop :=    (* defn letbind *)
 | LB_Let : forall (G:ctx) (x:var) (e:exp) (A:typ),
     typing G e A ->
     letbind G (letin_bind x e)  (( x , A ):: G ) 
 | LB_Comp : forall (G:ctx) (letin1 letin2:letin) (G'' G':ctx),
     letbind G letin1 G' ->
     letbind G' letin2 G'' ->
     letbind G (letin_composition letin1 letin2) G''
 | LB_Id : forall (G:ctx),
     letbind G letin_identity G.
(** definitions *)

(* defns Source *)
Inductive elab : sctx -> sexp -> styp -> exp -> Prop :=    (* defn elab *)
 | Ela_Int : forall (Gs:sctx),
      (uniq Gs )  ->
     elab Gs se_int st_int e_int
 | Ela_Var : forall (Gs:sctx) (x:var) (As:styp),
      (binds x As Gs )  ->
      (uniq Gs )  ->
     elab Gs (se_var x) As (e_var x)
 | Ela_Abs : forall (Gs:sctx) (x:var) (As:styp) (es:sexp) (Bs:styp) (A:typ) (e:exp) (B:typ),
     elab  (( x , As ):: Gs )  es Bs e ->
      (  (trans As )  = A )  ->
      (  (trans Bs )  = B )  ->
     elab Gs (se_abs x As es) (st_arrow As Bs) (e_abs x A e B)
 | Ela_App : forall (Gs:sctx) (es1 es2:sexp) (Bs:styp) (e1 e2:exp) (As:styp),
     elab Gs es1 (st_arrow As Bs) e1 ->
     elab Gs es2 As e2 ->
     elab Gs (se_app es1 es2) Bs (e_app e1 e2)
 | Ela_NAbs : forall (Gs:sctx) (p:npexp) (es:sexp) (P:nptyp) (Bs:styp) (x:var) (A:typ) (letin5:letin) (e:exp) (B:typ) (Gs':sctx),
      (fresh x Gs' )  ->
      (uniq Gs' )  ->
     pelab Gs x p P letin5 Gs' ->
     elab Gs' es Bs e ->
      (  (ptrans P )  = A )  ->
      (  (trans Bs )  = B )  ->
     elab Gs (se_nabs p es) (st_narrow P Bs) (e_abs x A (e_letin letin5 e) B)
 | Ela_NApp : forall (Gs:sctx) (es:sexp) (a:narg) (Bs:styp) (e e':exp) (P:nptyp),
     elab Gs es (st_narrow P Bs) e ->
     pmatch Gs P a e' ->
     elab Gs (se_napp es a) Bs (e_app e e')
with pelab : sctx -> var -> npexp -> nptyp -> letin -> sctx -> Prop :=    (* defn pelab *)
 | PEla_Empty : forall (Gs:sctx) (x:var),
     pelab Gs x par_empty pt_empty letin_identity Gs
 | PEla_Required : forall (Gs:sctx) (x:var) (p:npexp) (l:var) (As:styp) (P:nptyp) (letin5:letin) (Gs':sctx),
     pelab Gs x p P letin5 Gs' ->
     pelab Gs x  ( (par_required p l As) )   ( (pt_required P l As) )  (letin_composition letin5 (letin_bind l (e_prj (e_var x) l)))  (( l , As ):: Gs' ) 
 | PEla_Optional : forall (Gs:sctx) (x:var) (p:npexp) (l:var) (es:sexp) (P:nptyp) (As:styp) (letin5:letin) (y:var) (A:typ) (e:exp) (Gs':sctx),
      (fresh y Gs' )  ->
      x <> y  ->
     pelab Gs x p P letin5 Gs' ->
     elab Gs' es As e ->
      (  (trans As )  = A )  ->
     pelab Gs x  ( (par_optional p l es) )   ( (pt_optional P l As) )  (letin_composition letin5 (letin_bind l (e_switch (e_prj (e_var x) l) y A (e_var y) t_null e)))  (( l , As ):: Gs' ) 
with pmatch : sctx -> nptyp -> narg -> exp -> Prop :=    (* defn pmatch *)
 | PMat_Empty : forall (Gs:sctx),
     pmatch Gs pt_empty arg_empty e_top
 | PMat_Extra : forall (Gs:sctx) (a:narg) (l:var) (es:sexp) (e' e:exp) (As:styp),
     elab Gs es As e ->
     pmatch Gs pt_empty a e' ->
     pmatch Gs pt_empty  ( (arg_field a l es) )  (e_merge e' (e_rcd l e))
 | PMat_Required : forall (Gs:sctx) (P:nptyp) (l:var) (As:styp) (a:narg) (e' e:exp) (es:sexp),
     lookup a l es ->
     elab Gs es As e ->
     pmatch Gs P  (remove l a )  e' ->
     pmatch Gs  ( (pt_required P l As) )  a (e_merge e' (e_rcd l e))
 | PMat_Present : forall (Gs:sctx) (P:nptyp) (l:var) (As:styp) (a:narg) (e' e:exp) (es:sexp),
     lookup a l es ->
     elab Gs es As e ->
     pmatch Gs P  (remove l a )  e' ->
     pmatch Gs  ( (pt_optional P l As) )  a (e_merge e' (e_rcd l e))
 | PMat_Absent : forall (Gs:sctx) (P:nptyp) (l:var) (As:styp) (a:narg) (e':exp),
     lookdown a l ->
     pmatch Gs P a e' ->
     pmatch Gs  ( (pt_optional P l As) )  a (e_merge e' (e_rcd l e_null))
with lookup : narg -> var -> sexp -> Prop :=    (* defn lookup *)
 | LU_Present : forall (a:narg) (l:var) (es:sexp),
     lookdown a l ->
     lookup  ( (arg_field a l es) )  l es
 | LU_Absent : forall (a:narg) (l':var) (es':sexp) (l:var) (es:sexp),
      l' <> l  ->
     lookup a l es ->
     lookup  ( (arg_field a l' es') )  l es
with lookdown : narg -> var -> Prop :=    (* defn lookdown *)
 | LD_Empty : forall (l:var),
     lookdown arg_empty l
 | LD_Absent : forall (a:narg) (l':var) (es:sexp) (l:var),
      l' <> l  ->
     lookdown a l ->
     lookdown  ( (arg_field a l' es) )  l.


