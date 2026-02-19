(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*    David Knothe, FZI Research Center for Information Technology     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** The whole compiler and its proof of semantic preservation *)

Require Import String.
Require Import Axioms Coqlib Errors.
Require Import AST Linking Smallstep.
Require Import Semantics SemanticsSmallBig.
Require Import Behaviors Tracex.
Require Import Compopts.
Require Import CompilerSmallstep CminLoopBigSmallEquiv.
Require DropGotos.
Require Cminor CminLoop.
Require CminLoopRemoveSkips.
Require CminLoopRemoveDummys.
Require CminLoopUnswitching.
Require CminLoopWhileTrue.
Require CminLoopInvert.
Require CminLoopRepeatTransform.
Require CminLoopUnroll.

Parameter print_CminLoop: Z -> CminLoop.program -> unit.

Notation "a @ b" :=
   (b a) (at level 50, left associativity, only parsing).

(* For now, apply transformations to each and every loop. *)
Definition should_unswitch_loop (body: CminLoop.stmt) := true.
Definition should_invert_loop (body: CminLoop.stmt) := true.
Definition should_unroll_loop (body: CminLoop.stmt) := true.

Definition inside_loop_compiler (p: CminLoop.program) : CminLoop.program :=
  p
  @ print (print_CminLoop 0)
  @ CminLoopRemoveSkips.transl_program_rep
  @ print (print_CminLoop 1)
  @ CminLoopRemoveDummys.transl_program_rep
  @ print (print_CminLoop 2)
  @ CminLoopUnroll.transl_program should_unroll_loop
  @ print (print_CminLoop 3)
  @ CminLoopUnswitching.transl_program should_unswitch_loop
  @ CminLoopWhileTrue.transl_program
  @ CminLoopInvert.transl_program should_invert_loop.

Definition loop_compiler (p: Cminor.program) : res Cminor.program :=
  if optim_loop tt then
    OK p
    @@@ DropGotos.transf_program1
     @@ inside_loop_compiler
     @@ DropGotos.transf_program2
  else
    OK p.

Theorem inside_loop_compiler_forward_transformation:
  forall p tp,
  inside_loop_compiler p = tp ->
  bigstep_semantics p ⇉ bigstep_semantics tp.
Proof.
  intros p1 tp H. unfold inside_loop_compiler in H. simpl in H. unfold print in H.
  set (p2 := CminLoopRemoveSkips.transl_program_rep p1) in H.
  set (p3 := CminLoopRemoveDummys.transl_program_rep p2) in H.
  set (p4 := CminLoopUnroll.transl_program _ p3) in H.
  set (p5 := CminLoopUnswitching.transl_program _ p4) in H.
  set (p6 := CminLoopWhileTrue.transl_program p5) in H.
  set (p7 := CminLoopInvert.transl_program _ p6) in H.
  subst.
  eapply forward_transformation_trans with (S2:=bigstep_semantics p2).
  eapply CminLoopRemoveSkips.forward_preservation_rep. apply match_transform_program.
  eapply forward_transformation_trans with (S2:=bigstep_semantics p3).
  eapply CminLoopRemoveDummys.forward_preservation_rep. apply match_transform_program.
  eapply forward_transformation_trans with (S2:=bigstep_semantics p4).
  eapply CminLoopUnroll.forward_preservation. unfold p4. apply match_transform_program.
  eapply forward_transformation_trans with (S2:=bigstep_semantics p5).
  eapply CminLoopUnswitching.forward_preservation. apply match_transform_program.
  eapply forward_transformation_trans with (S2:=bigstep_semantics p6).
  eapply CminLoopWhileTrue.forward_preservation. apply match_transform_program.
  eapply CminLoopInvert.forward_preservation. apply match_transform_program.
Qed.

Theorem inside_loop_compiler_backward_transformation:
  forall p tp,
  inside_loop_compiler p = tp ->
  bigstep_semantics p ⇇ bigstep_semantics tp.
Proof.
  intros.
  apply forward_to_backward.
  apply bigstep_semantics_determinate.
  apply bigstep_semantics_receptive.
  apply bigstep_semantics_nonempty.
  now apply inside_loop_compiler_forward_transformation.
Qed.


(** First, consider semantic preservation as defined by the bigstep and behavioral semantics. *)

Theorem inside_loop_compiler_bigstep_preservation:
  forall p tp,
  inside_loop_compiler p = tp ->
  forward_preservation (bigstep_semantics p) (bigstep_semantics tp) /\
  backward_preservation (bigstep_semantics p) (bigstep_semantics tp).
Proof.
  intros. split.
  now apply forward_preservation_from_transformation, inside_loop_compiler_forward_transformation.
  now apply backward_preservation_from_transformation, inside_loop_compiler_backward_transformation.
Qed.

Theorem inside_loop_compiler_smallstep_beh_preservation:
  forall p tp,
  inside_loop_compiler p = tp ->
  forward_preservation (CminLoop.beh_semantics p) (CminLoop.beh_semantics tp) /\
  backward_preservation (CminLoop.beh_semantics p) (CminLoop.beh_semantics tp).
Proof.
  intros. apply inside_loop_compiler_bigstep_preservation in H as [].
  unfold forward_preservation, backward_preservation. split; intros.
  * apply big_small_equivalent, H in H1 as [b []]. exists b. now apply big_small_equivalent in H1.
  * apply big_small_equivalent, H0 in H1 as [b []]. exists b. now apply big_small_equivalent in H1.
Qed.

(** Now, consider the semeantic preservation given by the standard smallstep semantics,
    instead of by the derived behavioral semantics. *)
Require Import SmallstepBehaviors.

Theorem inside_loop_compiler_preservation:
  forall p tp,
  inside_loop_compiler p = tp ->
  forward_preservation (CminLoop.semantics p) (CminLoop.semantics tp) /\
  backward_preservation (CminLoop.semantics p) (CminLoop.semantics tp).
Proof.
  intros. apply inside_loop_compiler_smallstep_beh_preservation in H as []. split.
  * now apply smallstep_forward_preservation in H.
  * now apply smallstep_backward_preservation in H0. 
Qed.

Lemma drop_gotos_preservation:
  forall p tp,
  DropGotos.transf_program1 p = OK tp ->
  forward_preservation (Cminor.semantics p) (CminLoop.semantics tp) /\
  backward_preservation (Cminor.semantics p) (CminLoop.semantics tp).
Proof.
  intros. assert (forward_simulation (Cminor.semantics p) (CminLoop.semantics tp)).
  * now apply DropGotos.transf_program_correct1, DropGotos.transf_program_match1.
  * split. now apply forward_simulation_preservation.
    apply forward_to_backward_simulation in H0. now apply backward_simulation_preservation.
    apply Cminor.semantics_receptive. apply CminLoop.semantics_determinate.
Qed.

Lemma add_gotos_preservation:
  forall p tp,
  DropGotos.transf_program2 p = tp ->
  forward_preservation (CminLoop.semantics p) (Cminor.semantics tp) /\
  backward_preservation (CminLoop.semantics p) (Cminor.semantics tp).
Proof.
   intros. assert (forward_simulation (CminLoop.semantics p) (Cminor.semantics tp)).
  * subst. now apply DropGotos.transf_program_correct2, DropGotos.transf_program_match2.
  * split. now apply forward_simulation_preservation.
    apply forward_to_backward_simulation in H0. now apply backward_simulation_preservation.
    apply CminLoop.semantics_receptive. apply Cminor.semantics_determinate.
Qed.

Theorem loop_compiler_preservation:
  forall p tp,
  loop_compiler p = OK tp ->
  forward_preservation (Cminor.semantics p) (Cminor.semantics tp) /\
  backward_preservation (Cminor.semantics p) (Cminor.semantics tp).
Proof.
  intros. unfold loop_compiler in H. destruct (optim_loop tt).
  + simpl in H. destruct (DropGotos.transf_program1 p) as [cml|e] eqn:P2; try discriminate.
    injection H; intros; clear H. split.
    - eapply forward_preservation_trans with (L2:=CminLoop.semantics cml).
      now apply drop_gotos_preservation.
      eapply forward_preservation_trans with (L2:=CminLoop.semantics (inside_loop_compiler cml)).
      now apply inside_loop_compiler_preservation. now apply add_gotos_preservation.
    - eapply backward_preservation_trans with (L2:=CminLoop.semantics cml).
      now apply drop_gotos_preservation.
      eapply backward_preservation_trans with (L2:=CminLoop.semantics (inside_loop_compiler cml)).
      now apply inside_loop_compiler_preservation. now apply add_gotos_preservation.
  + injection H; intros; subst. split. apply forward_preservation_refl. apply backward_preservation_refl.
Qed.

(** The full compiler, with optional loop transformations in-between. *)

Definition compiler (p: Csyntax.program): res Asm.program :=
  OK p
  @@@ transf_c_to_cminor
  @@@ loop_compiler
  @@@ transf_cminor_to_asm.

(** The main compiler correctness theorem. Corollaries of it are in Complements.v. *)

Theorem compiler_backward_preservation: forall p tp,
  compiler p = OK tp ->
  backward_preservation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. unfold compiler in H. simpl in H.
  destruct (transf_c_to_cminor p) as [p2|e] eqn:P2; simpl in H; try discriminate.
  destruct (loop_compiler p2) as [p3|e] eqn:P3; simpl in H; try discriminate.
  destruct (transf_cminor_to_asm p3) as [p4|e] eqn:P4; simpl in H; try discriminate.
  injection H; intros; subst.
  eapply backward_preservation_trans.
  apply backward_simulation_preservation, c_to_cminor_program_simulation. eauto.
  eapply backward_preservation_trans.
  apply loop_compiler_preservation. eauto.
  apply backward_simulation_preservation, cminor_to_asm_program_simulation. eauto.
Qed.



(*** Defining a `match` relation for linking ***)

(* In order to reason about linking, we change the order of the transformations:
   we apply a chain of transformations to each function and then put them together into a program,
   instead of applying a chain of program transformations to a program.
   We now show equivalence between these transformations. *)

Section TRANSF_COMMUTATIVE.

Context {V: Type}.

Lemma bracket_apply_total:
  forall {A B C: Type} (a: res A) (f: A -> B) (g: B -> C),
  a @@ f @@ g = a @@ (fun x => g (f x)).
Proof.
  intros. now destruct a.
Qed.

Lemma transf_program_partial_total_comm3:
  forall {F1 F2 F3 F4: Type}
  (p: program F1 V) (transf1: F1 -> res F2) (transf2: F2 -> F3) (transf3: F3 -> F4),
  OK p @@@ transform_partial_program transf1 @@ transform_program transf2 @@ transform_program transf3 =
  transform_partial_program (fun f => OK f @@@ transf1 @@ transf2 @@ transf3) p.
Proof.
  intros. rewrite bracket_apply_total, transf_program_total_total_comm_ext. rewrite transf_program_partial_total_comm.
  simpl. f_equal. apply extensionality. intros. now rewrite bracket_apply_total.
Qed.

End TRANSF_COMMUTATIVE.

(* New, equivalent definitions to the above loop transformation. *)

Definition inside_loop_compile_function (f: CminLoop.function) : CminLoop.function :=
  f
  @ CminLoopRemoveSkips.transl_function_rep
  @ CminLoopRemoveDummys.transl_function_rep
  @ CminLoopUnroll.transl_function should_unroll_loop
  @ CminLoopUnswitching.transl_function should_unswitch_loop
  @ CminLoopWhileTrue.transl_function
  @ CminLoopInvert.transl_function should_invert_loop.

Definition inside_loop_compile_fundef (f: CminLoop.fundef) : CminLoop.fundef :=
  f
  @ CminLoopRemoveSkips.transl_fundef_rep
  @ CminLoopRemoveDummys.transl_fundef_rep
  @ CminLoopUnroll.transl_fundef should_unroll_loop
  @ CminLoopUnswitching.transl_fundef should_unswitch_loop
  @ CminLoopWhileTrue.transl_fundef
  @ CminLoopInvert.transl_fundef should_invert_loop.

Definition loop_compile_function (f: Cminor.function) : res Cminor.function :=
  if optim_loop tt then
    OK f
    @@@ DropGotos.transf_function1
     @@ inside_loop_compile_function
     @@ DropGotos.transf_function2
  else
    OK f.

Definition loop_compile_fundef (f: Cminor.fundef) : res Cminor.fundef :=
  if optim_loop tt then
    OK f
    @@@ DropGotos.transf_fundef1
     @@ inside_loop_compile_fundef
     @@ DropGotos.transf_fundef2
  else
    OK f.

Lemma function_fundef_equivalent:
  AST.transf_partial_fundef loop_compile_function = loop_compile_fundef.
Proof.
  apply extensionality. intro.
  unfold transf_partial_fundef. unfold bind. destruct x.
  * unfold loop_compile_function, loop_compile_fundef, inside_loop_compile_function, inside_loop_compile_fundef in *.
    destruct optim_loop. 2: auto.
    simpl in *. now destruct (DropGotos.transf_function1 f).
  * unfold loop_compile_fundef. now destruct optim_loop.
Qed.

(* The alternative, per-function definition of loop compiler. *)
Definition alt_loop_compiler (p: Cminor.program) : res Cminor.program :=
  transform_partial_program loop_compile_fundef p.

Definition match_cminor_prog_fundef (p: Cminor.program) (tp: Cminor.program) :=
  match_program (fun cu f tf => loop_compile_fundef f = OK tf) eq p tp.

Definition match_cminor_prog_function (p: Cminor.program) (tp: Cminor.program) :=
  match_program (fun cu f tf => AST.transf_partial_fundef loop_compile_function f = OK tf) eq p tp.

Lemma match_equiv: forall p tp,
  match_cminor_prog_fundef p tp <-> match_cminor_prog_function p tp.
Proof.
  intros. unfold match_cminor_prog_fundef, match_cminor_prog_function in *.
  match goal with [ |- match_program ?f1 eq p tp <-> match_program ?f2 eq p tp ] => enough (f1 = f2) end.
  now rewrite H. apply extensionality. intro. now rewrite function_fundef_equivalent.
Qed.

Theorem alt_loop_compiler_match:
  forall p tp, alt_loop_compiler p = OK tp ->
  match_cminor_prog_fundef p tp.
Proof.
  intros. eapply match_transform_partial_program_contextual in H; eauto.
Qed.


Lemma unfold_transform_program_chain: forall (p: Cminor.program),
  transform_partial_program (fun f => DropGotos.transf_fundef1 f @@ inside_loop_compile_fundef @@ DropGotos.transf_fundef2) p =
  OK p @@@ transform_partial_program DropGotos.transf_fundef1 @@ transform_program inside_loop_compile_fundef @@ transform_program DropGotos.transf_fundef2.
Proof.
  intros. symmetry. apply transf_program_partial_total_comm3.
Qed.

Lemma inside_loop_compile_fundef_identical:
  transform_program inside_loop_compile_fundef = inside_loop_compiler.
Proof.
  apply extensionality. intros. unfold inside_loop_compile_fundef, inside_loop_compiler. unfold print.
  rewrite <- transf_program_total_total_comm. unfold CminLoopInvert.transl_program. f_equal.
  rewrite <- transf_program_total_total_comm. unfold CminLoopWhileTrue.transl_program. f_equal.
  rewrite <- transf_program_total_total_comm. unfold CminLoopUnswitching.transl_program. f_equal.
  rewrite <- transf_program_total_total_comm. unfold CminLoopUnroll.transl_program. f_equal.
  rewrite <- transf_program_total_total_comm. unfold CminLoopRemoveDummys.transl_program_rep, CminLoopRepeatTransform.transl_program.
  f_equal.
Qed.

Lemma transl_program_identical: forall (p: Cminor.program),
  alt_loop_compiler p = loop_compiler p.
Proof.
  intro p.
  unfold alt_loop_compiler, loop_compiler, loop_compile_fundef. simpl.
  destruct (optim_loop tt).
  - now rewrite unfold_transform_program_chain, inside_loop_compile_fundef_identical.
  - apply transform_partial_function_id.
Qed.

Corollary alt_loop_compiler_preservation:
  forall p tp, match_cminor_prog_function p tp ->
  forward_preservation (Cminor.semantics p) (Cminor.semantics tp) /\
  backward_preservation (Cminor.semantics p) (Cminor.semantics tp).
Proof.
  intros. apply loop_compiler_preservation. rewrite <- transl_program_identical.
  symmetry. apply invert_match_program_partial. now apply match_equiv.
Qed.


(** We now define a pass linking relation, equivalent to the above one,
    that allows us to conclude the facts about separate compilation using `link_list_compose_passes`. *)

Local Open Scope linking_scope.

Definition loop_passes: Passes Cminor.program Cminor.program :=
  if optim_loop tt then
        mkpass DropGotos.match_prog1
    ::: mkpass CminLoopRemoveSkips.match_prog_rep
    ::: mkpass CminLoopRemoveDummys.match_prog_rep
    ::: mkpass (CminLoopUnroll.match_prog should_unroll_loop)
    ::: mkpass (CminLoopUnswitching.match_prog should_unswitch_loop)
    ::: mkpass CminLoopWhileTrue.match_prog
    ::: mkpass (CminLoopInvert.match_prog should_invert_loop)
    ::: mkpass DropGotos.match_prog2
    ::: pass_nil _
  else
        pass_nil _.

Lemma convert_into_pass_match: forall p tp, match_cminor_prog_function p tp -> pass_match (compose_passes loop_passes) p tp.
Proof.
  intros. unfold match_cminor_prog_function, loop_passes in *. rewrite function_fundef_equivalent in H. unfold loop_compile_fundef, inside_loop_compile_fundef in H.
  destruct optim_loop.
  * simpl. destruct H as [? []]. apply recover_prog_defs_from_match_partial in H.
    rewrite transf_globdefs_partial_total_comm, transf_globdefs_partial_total_comm in H.
    destruct transf_globdefs eqn:? in H; try easy. injection H; clear H; intros.
    rewrite transf_globdefs_total_total_comm with (transf2:=CminLoopInvert.transl_fundef _) in H.
    rewrite transf_globdefs_total_total_comm with (transf2:=CminLoopWhileTrue.transl_fundef) in H.
    rewrite transf_globdefs_total_total_comm with (transf2:=CminLoopUnswitching.transl_fundef _) in H.
    rewrite transf_globdefs_total_total_comm with (transf2:=CminLoopUnroll.transl_fundef _) in H.
    rewrite transf_globdefs_total_total_comm with (transf2:=CminLoopRemoveDummys.transl_fundef_rep) in H.
    eexists (mkprogram _ (prog_public p) (prog_main p)).
      split. constructor. eapply match_globdef_partial_from_prog_defs; eauto. auto.
    eexists (mkprogram _ (prog_public p) (prog_main p)).
      split. constructor. apply match_globdef_total_from_prog_defs. eauto.
    eexists (mkprogram _ (prog_public p) (prog_main p)).
      split. constructor. apply match_globdef_total_from_prog_defs. eauto.
    eexists (mkprogram _ (prog_public p) (prog_main p)).
      split. constructor. apply match_globdef_total_from_prog_defs. eauto.
    eexists (mkprogram _ (prog_public p) (prog_main p)).
      split. constructor. apply match_globdef_total_from_prog_defs. eauto.
    eexists (mkprogram _ (prog_public p) (prog_main p)).
      split. constructor. apply match_globdef_total_from_prog_defs. eauto.
    eexists (mkprogram _ (prog_public p) (prog_main p)).
      split. constructor. apply match_globdef_total_from_prog_defs. eauto.
    eexists (mkprogram _ (prog_public p) (prog_main p)).
      split. constructor. apply match_globdef_total_from_prog_defs. eauto.
    destruct tp. simpl in *. now subst.
  * destruct H as [? []]. destruct p, tp. simpl in *. subst. f_equal.
    induction H. auto. f_equal; auto. inv H. inv H2. destruct a1, b1. simpl in *. injection H5; intro; now subst. inv H4. destruct a1, b1. simpl in *. now subst.
Qed.

Lemma convert_from_pass_match: forall p tp, pass_match (compose_passes loop_passes) p tp -> match_cminor_prog_function p tp.
Proof.
  intros. unfold match_cminor_prog_function, loop_passes in *. rewrite function_fundef_equivalent. unfold loop_compile_fundef, inside_loop_compile_fundef.
  destruct optim_loop.
  * simpl in H. decompose [ex and] H. clear H.
    apply invert_match_program_partial in H1.
    apply invert_match_program_total in H2, H3, H4, H5, H6, H7, H8.
    unfold transform_program in *. subst. simpl.
    unfold transform_partial_program, transform_partial_program2, bind in H1.
    constructor.
    apply match_globdef_partial_from_prog_defs.
    rewrite transf_globdefs_partial_total_comm, transf_globdefs_partial_total_comm.
    destruct transf_globdefs eqn:?. 2: easy. injection H1; intros; subst. simpl.
    rewrite <- transf_globdefs_total_total_comm with (transf1:=CminLoopWhileTrue.transl_fundef).
    rewrite <- transf_globdefs_total_total_comm with (transf1:=CminLoopUnswitching.transl_fundef _).
    rewrite <- transf_globdefs_total_total_comm with (transf1:=CminLoopUnroll.transl_fundef _).
    rewrite <- transf_globdefs_total_total_comm with (transf1:=CminLoopRemoveDummys.transl_fundef_rep).
    rewrite <- transf_globdefs_total_total_comm with (transf1:=CminLoopRemoveSkips.transl_fundef_rep).
    auto. destruct transf_globdefs eqn:?. 2: easy. injection H1; intros; now subst.
  * simpl in H. subst. remember (prog_defs tp). constructor. rewrite <- Heql at 1 2. clear Heql. induction l. constructor.
    constructor. constructor. auto. destruct a, g; econstructor; eauto. apply linkorder_refl. now destruct v. auto. auto.
Qed.

Theorem separate_loop_compiler_preservation:
  forall units_before units_after program_before,
  nlist_forall2 (fun cu tcu => loop_compiler cu = OK tcu) units_before units_after ->
  link_list units_before = Some program_before ->
  exists program_after,
      link_list units_after = Some program_after
   /\ backward_preservation (Cminor.semantics program_before) (Cminor.semantics program_after).
Proof.
  intros.
  assert (nlist_forall2 match_cminor_prog_function units_before units_after).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply match_equiv, match_transform_partial_program; auto. now rewrite transl_program_identical. }
  assert (exists program_after, link_list units_after = Some program_after /\ (compose_passes loop_passes) program_before program_after).
  { eapply link_list_compose_passes; eauto. eapply nlist_forall2_imply; eauto. intros. now apply convert_into_pass_match. }
  destruct H2 as (program_after & P & Q).
  exists program_after; split; auto. apply alt_loop_compiler_preservation. now apply convert_from_pass_match.
Qed.

Lemma nlist_forall2_split_partial_partial: forall {A B C: Type} (f1: A -> res B) (f2: B -> res C) (al: nlist A) (cl: nlist C),
  nlist_forall2 (fun a c => f1 a @@@ f2 = OK c) al cl ->
  exists bl,
    nlist_forall2 (fun a b => f1 a = OK b) al bl /\ nlist_forall2 (fun b c => f2 b = OK c) bl cl.
Proof.
  intros. generalize dependent cl. induction al; intros.
  * inv H. destruct (f1 a) eqn:?. 2: easy. exists (nbase b0). split; constructor; auto.
  * inv H. destruct (f1 a) eqn:?. 2: easy. apply IHal in H4 as [bl []]. exists (ncons b0 bl). split; constructor; auto.
Qed.

(** The full separate compilation theorem. Corollaries of it are in Complements.v. *)

Theorem separate_compiler_preservation:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => compiler cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_preservation (Csem.semantics c_program) (Asm.semantics asm_program).
Proof.
  intros. unfold compiler in H.
  apply nlist_forall2_split_partial_partial in H as [cminor_units_2 []].
  apply nlist_forall2_split_partial_partial in H as [cminor_units_1 []].
  eapply separate_transf_c_to_cminor_simulation in H as [cminor_program1 []]; eauto.
  eapply separate_loop_compiler_preservation in H2 as [cminor_program2 []]; eauto.
  eapply separate_transf_cminor_to_asm_simulation in H1 as [asm_program []]; eauto.
  exists asm_program. split; auto.
  eapply backward_preservation_trans; eauto. eapply backward_simulation_preservation; eauto.
  eapply backward_preservation_trans; eauto. eapply backward_simulation_preservation; eauto.
Qed.