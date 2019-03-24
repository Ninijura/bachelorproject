(* This file is created in order to get my thoughts sorted out *)
(* The current goal is to "Define Rml semantics using semantics constructs. *) 

From mathcomp Require Import all_ssreflect all_algebra. 
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.
Require Import FunctionalExtensionality.

(* RML:
Variables                x
Primitive constants      c
Conditionals             if b then e1 else e2
Local bindings           let x = e1 in e2
Applications             f e1 e2 ... en      with f being defined as function 
 *)


(* pwhile's return type is a distribution of memories.
   Rml returns a measure on the type (t -> [0,1]) -> [0,1]
   This means that if we input a memory, we'd get a distribution over memories
   But Rml does not have memories...?
   I looks like prp_ is applying a predicate to all of the memory; 
   that might be the thing to use in order to return the right thing *)
