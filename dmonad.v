(* -------------------------------------------------------------------- *)
(* ------- *) Require Import ClassicalFacts Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Set   Printing Projections.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Parameter (R : realType).

(* -------------------------------------------------------------------- *)
Lemma funext : forall {T U : Type} (f g : T -> U),
  (forall x, f x = g x) -> f = g.
Proof. by move=> T U f g; apply: functional_extensionality_dep. Qed.

Lemma funext2 : forall {T U V : Type} (f g : T -> U -> V),
  (forall x y, f x y = g x y) -> f = g.
Proof. by move=> T U V f g eq; apply/funext=> x; apply/funext. Qed.

(* -------------------------------------------------------------------- *)
Lemma distr_eqP {T : choiceType} (f1 f2 : {distr T / R}) :
  f1 =1 f2 <-> f1 = f2.
Proof. 
split=> [|->] //; case: f1 f2 => [mu1 ge0_1 s1 le1_1] [mu2 ge0_2 s2 le1_2].
move/funext => /= eq_mu; have PI (A : Prop): A \/ ~ A by case: (asboolP A); auto.
by subst; congr Distr; apply Prop_irrelevance.
Qed.

(* -------------------------------------------------------------------- *)
Definition Choice T := (ChoiceType (EqType T gen_eqMixin) gen_choiceMixin).

(* -------------------------------------------------------------------- *)
Record premonad := mkPreMonad {
  M    :> Type -> Type;
  unit :  forall {T : Type}, T -> M T;
  bind :  forall {T U : Type}, M T -> (T -> M U) -> M U;
}.

Arguments unit p {T} _.
Arguments bind p {T U} _ _.

(* -------------------------------------------------------------------- *)
Variant ismonad (M : premonad) :=
| IsMonad of
       (forall {T U} (x : T) (f : T -> M U),
          M.(bind) (M.(unit) x) f = f x)
     & (forall {T} (m : M T),
          M.(bind) m M.(unit) = m)
     & (forall {T U V} (m : M T) (f : T -> M U) (g : U -> M V),
          M.(bind) (M.(bind) m f) g = M.(bind) m (fun x => M.(bind) (f x) g)).

(* -------------------------------------------------------------------- *)
Definition dpremonad :=
  {| M    := fun T => {distr (Choice T) / R}
   ; unit := fun T => @dunit R (Choice T)
   ; bind := fun T U m f => @dlet R (Choice T) (Choice U) f m |}.

(* -------------------------------------------------------------------- *)
Lemma ismonad_dpremonad : ismonad dpremonad.
Proof. constructor => [T U x f|T m|T U V m f g] /=.
+ by apply/distr_eqP/dlet_unit.
+ by apply/distr_eqP/dlet_dunit_id.
+ by apply/distr_eqP/dlet_dlet.
Qed.

