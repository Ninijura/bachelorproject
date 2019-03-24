Require Import String.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.
Require Import FunctionalExtensionality.

Reserved Notation "x >>= f" (at level 40, left associativity). 
Class Monad (M : Type -> Type) :=
  {
    unit : forall {A}, A -> M A;
    bind : forall {A B}, M A -> (A -> M B) -> M B
    where "x >>= f" := (bind x f);
    monad_law_unit_l : forall {A B} (a : A) (k : A -> M B), unit a >>= k = k a;
    monad_law_unit_r : forall {A} (x : M A), x >>= unit = x;
    monad_law_assoc : forall {A B C} (x : M A) (k : A -> M B) (h : B -> M C),
        x >>= (fun a => k a >>= h) = x >>= k >>= h
  }.

(* -------------------------------------------------------------------------------- *)

Definition continuation_monad_type := fun ZO A => (A -> ZO) -> ZO.
Instance continuation_monad ZO : Monad (continuation_monad_type ZO) :=
  {
    unit := fun {A} (x : A) (f : A -> ZO) => f x ;
    bind := fun {A B} (mu : (A -> ZO) -> ZO) (M : A -> (B -> ZO) -> ZO) (f : B -> ZO) => mu (fun (x : A) => M x f)
  }. 
Proof. all: reflexivity. Defined.

Definition M := continuation_monad_type. 

Definition expectation_monad_type (R : realType) := M R.
Instance expectation_monad (R : realType) : Monad (expectation_monad_type R) := continuation_monad R.

(*Instance option_monad : Monad option :=
  {
    unit := @Some ;
    bind _ _ x f :=
      match x with
      | Some y => f y
      | None => None
      end
  }.
Proof.
  all: try destruct x.
  all: reflexivity.
Qed.

Check @None.*)

(* -------------------------------------------------------------------------------- *)

(* Inductive Rml {A} : Type :=
   | Var : nat -> @Rml A 
   | Const : A -> @Rml A
   | Let_stm : forall B, nat -> @Rml B -> @Rml A -> @Rml A
   (* | Fun_stm : forall B, nat -> B -> @Rml A -> @Rml A *)
   | If_stm : @Rml bool -> @Rml A -> @Rml A -> @Rml A
   | App_stm : forall B, @Rml (B -> A) -> @Rml B -> @Rml A. *)


Inductive RMLtype : Type :=
| RMLnat 
| RMLbool 
| RMLfun of RMLtype & RMLtype.

Fixpoint interpType (t : RMLtype) : Type :=
  match t with
  | RMLnat => nat
  | RMLbool => bool
  | RMLfun t1 t2 => interpType t1 -> (M R (interpType t2))
  end. 
  
Inductive RMLval : Type :=
| bVal of bool
| nVal of nat
| fVal A B of interpType (RMLfun A B).

Inductive Rml : Type :=
| Var       of nat                 (* variable identifier *)
| Const     of RMLval            (* value of the constant *) 
| Let_stm   of nat & Rml & Rml     (* let string = Rml in Rml *)
| If_stm    of Rml & Rml & Rml   (* if bool then Rml else Rml *)
| Fun_stm   of nat & seq Rml 
. 


(* | Fun_stm : forall B, nat -> B -> @Rml A -> @Rml A 
   | If_stm : @Rml bool -> @Rml A -> @Rml A -> @Rml A
   | App_stm : forall B, @Rml (B -> A) -> @Rml B -> @Rml A. *)

(* -------------------------------------------------------------------------------- *)
  
(*Compute (fun env => ((fun y => if y == "x"
                        then 3
                        else env y) "x")+2).

Let_stm x := 3 in x + 2.


Compute (fun x => x).
Compute (fun x => *)

(*Inductive env : Type := forall A, (forall B, B -> option A).
Compute (Const (fun x => x 3 2))*)


Fixpoint interp_helper args name (env : nat -> RMLval) : M R RMLval :=

    let helper := fix helper args (acc : seq RMLval) :=
                    match args with
                    | nil => (*List.fold_left (fun partial_app value => unit (partial_app val))
                                           acc *)
                                           (unit (env name))
                    | arg :: args' => bind arg (fun y => helper args' (y :: acc))
                    end
    in helper args nil.
    
                         

Fixpoint interp {A} (x : Rml) env : M R RMLval :=
  match x with
  | Var y => unit (env y)
  | Const c => unit c
  | Let_stm x a b => bind (interp a env) 
                         (fun x' => interp b 
                                        (fun y => if x == y
                                               then x'
                                               else env y))
  | If_stm b m1 m2 => bind (interp b env)
                          (fun (t : RMLval) =>
                             match t with
                             | bVal true => interp m1 env
                             | bVal false => interp m2 env
                             | _ => unit (bVal false)
                             end) 
  | Fun_stm name args =>
    (fix helper args (acc : seq RMLval) :=
       match args with
       | nil => List.fold_left (fun partial_app value => unit (partial_app val))
                              acc 
                              (unit (env name))
       | arg :: args' => bind arg (fun y => helper args' (y :: acc))
       end) args
  (*| App_stm typ f v => bind (interp f env)
                           (fun y => bind (interp v env) (fun v_interp =>  y v_interp))*)
  end.


(* Compute interp (App_stm nat (Const (fun x => x + 10)) (Const 2)).
Compute interp (If_stm (App_stm nat (Const (fun x => x > 10)) (Const 2)) (Const 3) (Const 2)).*)
Example test1 :
  interp (Let_stm 0 (Const (nVal 4)) (Var 0)) (fun x => bVal false) =
  interp (Const (nVal 4)) (fun x => bVal false).
Proof. reflexivity. Qed.


Compute interp (Let_stm 0 (Const (nVal 4)) (Var 0)) (fun x => bVal false).

(Const (fun e => 2) e)

Definition punit {R} {A} := @unit (expectation_monad_type R) (expectation_monad R) A.
Definition pbind {R} {A B} := @bind (expectation_monad_type R) (expectation_monad R) A B.
