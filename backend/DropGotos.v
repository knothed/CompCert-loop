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

(** Cminor -> CminLoop and CminLoop -> Cminor transforms.

  In order to execute bigstep transforms, we pass from Cminor to CminLoop,
  a language without goto statements.
*)

Require Import AST.
Require Import Smallstep.
Require Import Cminor.
Require Import CminLoop.
Require Import CminLoopTransfCommon.
Require Import Coqlib.
Require Import Globalenvs.
Require Import Errors.
Require Import Linking.
Require Import Integers.
Require Import Floats.
Require Import Equality.
Require Import Values.

Fixpoint stmt_goto_free (s: Cminor.stmt) : Prop :=
  match s with
  | Cminor.Sseq s1 s2 => stmt_goto_free s1 /\ stmt_goto_free s2
  | Cminor.Sifthenelse expr s1 s2 => stmt_goto_free s1 /\ stmt_goto_free s2
  | Cminor.Sloop s => stmt_goto_free s
  | Cminor.Sblock s => stmt_goto_free s
  | Cminor.Slabel l s => stmt_goto_free s
  | Cminor.Sgoto l => False
  | _ => True
  end.

Definition stmt_goto_free_dec: forall s, {stmt_goto_free s} + {~stmt_goto_free s}.
Proof.
  dependent induction s; try now left; try now right.
  destruct IHs1; destruct IHs2; simpl; (try now left); now right.
  destruct IHs1; destruct IHs2; simpl; (try now left); now right.
  destruct IHs. now left. now right.
  destruct IHs. now left. now right.
  destruct IHs. now left. now right.
  now right.
Defined.

(** Originally, we planned to execute loop transformations (which includes removing all goto statements)
    exactly if there are no goto statements in the program (instead of using a compiler flag).
    However, this does not work alongside linking, because the decision 'prog_goto_free_dec' would
    have to be performed over all input files, not just in the one that is currently being compiled.
    CompCert would require LTO for this.

Definition globdef_goto_free (g: globdef Cminor.fundef unit) : Prop :=
  match g with
  | Gfun fd => match fd with
    | Internal fn => stmt_goto_free (Cminor.fn_body fn)
    | External ef => True
    end
  | Gvar v => True
  end.

Definition prog_goto_free (prog: Cminor.program): Prop :=
  forall id gv, In (id, gv) (prog_defs prog) -> globdef_goto_free gv.


Definition globdef_goto_free_dec: forall g, {globdef_goto_free g} + {~globdef_goto_free g}.
Proof.
  destruct g. destruct f. apply stmt_goto_free_dec. now left. now left.
Defined.

Definition prog_goto_free_dec: forall p, {prog_goto_free p} + {~prog_goto_free p}.
Proof.
  intro. unfold prog_goto_free.
  destruct (forallb (fun '(_,g) => globdef_goto_free_dec g) (prog_defs p)) eqn:?.
  * left. rewrite forallb_forall in Heqb. intros. apply Heqb in H. now destruct globdef_goto_free_dec.
  * right. intro. enough (forallb (fun '(_,g) => globdef_goto_free_dec g) (prog_defs p) = true) by congruence.
    apply forallb_forall. intros. destruct x. apply H in H0. now destruct globdef_goto_free_dec.
Defined.

 Another thing that is hard to do with linking is to exploit the connection between
 the program being goto-free and each transformed function being goto-free, as
 this would require the transformation to know that each transformed function
 is a member of the program's definitions. This would require additional context that
 has to be passed on during linking.

Lemma prog_fundef_goto_free: forall (prog: Cminor.program) id f,
  prog_goto_free prog ->
  In (id, Gfun (Internal f)) (prog_defs prog) ->
  stmt_goto_free (Cminor.fn_body f).
Proof.
  intros. now apply H in H0.
Qed.
*)


(** First, the Cminor -> CminLoop transformation. *)

Section ToCminLoop.

Local Notation "$ x" := (fun _ => x) (at level 100).

Fixpoint remove_gotos (s: Cminor.stmt) (gf: stmt_goto_free s) { struct s } : stmt.
refine (match s as s' return (s = s' -> stmt) with
  | Cminor.Sskip =>$ Sskip
  | Cminor.Sassign id e =>$ Sassign id e
  | Cminor.Sstore m e1 e2 =>$ Sstore m e1 e2
  | Cminor.Scall id sig e args =>$ Scall id sig e args
  | Cminor.Stailcall sig e args =>$ Stailcall sig e args
  | Cminor.Sbuiltin id ef args =>$ Sbuiltin id ef args
  | Cminor.Sseq s1 s2 =>$ Sseq (remove_gotos s1 _) (remove_gotos s2 _)
  | Cminor.Sifthenelse e s1 s2 =>$ Sifthenelse e (remove_gotos s1 _) (remove_gotos s2 _)
  | Cminor.Sloop s =>$ Sloop (remove_gotos s _)
  | Cminor.Sblock s =>$ Sblock (remove_gotos s _)
  | Cminor.Sexit n =>$ Sexit n
  | Cminor.Sswitch islong e s n =>$ Sswitch islong e s n
  | Cminor.Sreturn r =>$ Sreturn r
  | Cminor.Slabel l s =>$ remove_gotos s _
  | Cminor.Sgoto l =>$ _
end eq_refl).
  all: subst; try now simpl in gf.
Defined.

Lemma remove_gotos_irrel: forall s G1 G2,
  remove_gotos s G1 = remove_gotos s G2.
Proof.
  intros. dependent induction s; simpl; auto.
  destruct G1. erewrite IHs1, IHs2; eauto.
  destruct G1. erewrite IHs1, IHs2; eauto.
  erewrite IHs; eauto. erewrite IHs; eauto. inv G1.
Qed.

Definition transf_function1 (f: Cminor.function) : res function :=
  if (stmt_goto_free_dec (Cminor.fn_body f)) then
    OK {|
      fn_sig := Cminor.fn_sig f;
      fn_params := Cminor.fn_params f;
      fn_vars := Cminor.fn_vars f;
      fn_stackspace := Cminor.fn_stackspace f;
      fn_body := remove_gotos (Cminor.fn_body f) ltac:(eauto)
    |}
  else
    Error (MSG "Function with a GOTO stmt cannot be loop-transformed." :: nil).

Definition transf_fundef1 (f: Cminor.fundef) : res fundef :=
  transf_partial_fundef transf_function1 f.

Definition transf_program1 (p: Cminor.program) : res program :=
  transform_partial_program transf_fundef1 p.


Definition match_prog1 (p: Cminor.program) (tp: program) : Prop :=
  match_program (fun _ f tf => transf_fundef1 f = OK tf) eq p tp.

Lemma transf_program_match1:
  forall p tp, transf_program1 p = OK tp -> match_prog1 p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.


Inductive match_cont1: Cminor.cont -> cont -> Prop :=
  | match_stop1:
      match_cont1 Cminor.Kstop Kstop
  | match_seq1: forall s k k'
      (SF: stmt_goto_free s),
      match_cont1 k k' ->
      match_cont1 (Cminor.Kseq s k) (Kseq (remove_gotos s SF) k')
  | match_block1: forall k k',
      match_cont1 k k' ->
      match_cont1 (Cminor.Kblock k) (Kblock k')
  | match_call1: forall id f tf v e k k',
      transf_fundef1 (Internal f) = OK (Internal tf) ->
      match_cont1 k k' ->
      match_cont1 (Cminor.Kcall id f v e k) (Kcall id tf v e k').

Inductive match_states1: Cminor.state -> state -> Prop :=
  | match_state1: forall f tf s s' k k' sp e m
      (SF: stmt_goto_free s),
      transf_fundef1 (Internal f) = OK (Internal tf) ->
      s' = remove_gotos s SF ->
      match_cont1 k k' ->
      match_states1 (Cminor.State f s k sp e m) (State tf s' k' sp e m)
  | match_callstate1: forall f tf args k k' m,
      transf_fundef1 f = OK tf ->
      match_cont1 k k' ->
      match_states1 (Cminor.Callstate f args k m) (Callstate tf args k' m)
  | match_returnstate1: forall v k k' m,
      match_cont1 k k' ->
      match_states1 (Cminor.Returnstate v k m) (Returnstate v k' m).

Lemma match_cont1_is_call_cont: forall k k',
  match_cont1 k k' ->
  Cminor.is_call_cont k ->
  is_call_cont k'.
Proof.
  intros. destruct k; inv H0; now inv H.
Qed.

Lemma call_cont_match_cont1: forall k k',
  match_cont1 k k' ->
  match_cont1 (Cminor.call_cont k) (call_cont k').
Proof.
  intros. induction H; simpl.
  constructor. apply IHmatch_cont1. apply IHmatch_cont1. now constructor.
Qed.

Lemma remove_gotos_match_cont1: forall k k' s GF,
  match_cont1 k k' ->
  match_cont1 (Cminor.Kseq s k) (Kseq (remove_gotos s GF) k').
Proof.
  intros. induction H; simpl; repeat constructor; auto.
Qed.


Variable prog: Cminor.program.
Variable tprog: program.
Hypothesis TRANSL: match_prog1 prog tprog.
Let ge : Cminor.genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma sig_preserved1:
  forall f tf,
  transf_fundef1 f = OK tf ->
  funsig tf = Cminor.funsig f.
Proof.
  intros. unfold transf_fundef1, transf_partial_fundef, transf_function1 in H. destruct f. destruct stmt_goto_free_dec in H.
  simpl in H. injection H; intros; subst; auto. simpl in H. congruence. injection H; intros; subst; auto.
Qed.

Fixpoint label_depth (s: Cminor.stmt) := match s with
  | Cminor.Slabel l s => S (label_depth s)
  | _ => O
end.

Definition state_depth (s: Cminor.state) := match s with
  | Cminor.State f s k v e m => label_depth s
  | _ => O
end.

Definition order := ltof Cminor.state state_depth.

Ltac unfold_transf' H := unfold transf_fundef1, transf_partial_fundef, transf_function1, bind in H; destruct stmt_goto_free_dec in H; [|congruence]; injection H; intro T; subst.
Ltac unfold_transf := match goal with [ H: transf_fundef1 _ = OK _ |- _ ] => unfold_transf' H end.

Ltac solve_transl_extend :=
  try solve_transl TRANSL;
  try (eapply sig_preserved1; eauto);
  try (eapply match_cont1_is_call_cont; eauto);
  try (unfold_transf; eauto).

Theorem step_simulation1:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall S1', match_states1 S1 S1' ->
  exists S2', (plus step tge S1' t S2' \/ star step tge S1' t S2' /\ order S2 S1) /\ match_states1 S2 S2'.
Proof.
  Ltac trivial_state := eexists; split; [left; apply plus_one|]; econstructor; eauto; solve_transl_extend.

  intros; inv H; inv H0.
* inv H9; trivial_state.
* inv H9; trivial_state.
* trivial_state.
* trivial_state.
* trivial_state.
* eapply (Genv.find_funct_transf_partial TRANSL) in H3 as [? []]; eauto.
  eexists; split. left. eapply plus_one, step_call with (fd:=x); solve_transl_extend; eauto. repeat econstructor; eauto.
* eapply (Genv.find_funct_transf_partial TRANSL) in H3 as [? []]; eauto.
  eexists; split. left. eapply plus_one, step_tailcall with (fd:=x); solve_transl_extend; eauto. repeat econstructor; eauto; solve_transl_extend.
  now apply call_cont_match_cont1.
* trivial_state.
* trivial_state. now apply remove_gotos_match_cont1.
* trivial_state. destruct b; apply remove_gotos_irrel.
* trivial_state. fold remove_gotos. replace (Sloop (remove_gotos s _)) with (remove_gotos (Cminor.Sloop s) SF) by auto. now constructor.
* trivial_state. now constructor.
* inv H9; trivial_state.
* inv H9; trivial_state.
* inv H9; trivial_state.
* trivial_state.
* trivial_state. now apply call_cont_match_cont1.
* trivial_state. now apply call_cont_match_cont1.
* exists (State tf (remove_gotos s SF) k' sp e m). split. right.
  split. auto. constructor. cbv. lia. econstructor; eauto.
* inv SF.
* unfold_transf. trivial_state. unfold transf_fundef1, transf_partial_fundef, bind, transf_function1.
  destruct stmt_goto_free_dec. erewrite remove_gotos_irrel; eauto. congruence.
  simpl. erewrite remove_gotos_irrel; eauto.
* unfold transf_fundef, transf_partial_fundef in H6. injection H6; intros; subst. trivial_state.
* inv H4. trivial_state.
Unshelve. all: auto; try constructor. inv SF; now case b.
Qed.

Lemma transf_initial_states1:
  forall st1, Cminor.initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states1 st1 st2.
Proof.
  intros. inv H.
  eapply (Genv.find_funct_ptr_transf_partial TRANSL) in H2 as [? []].
  eexists; split; econstructor; eauto; solve_transl_extend.
  now eapply (Genv.init_mem_match TRANSL).
  erewrite (match_program_main TRANSL).
  erewrite (Genv.find_symbol_match TRANSL); eauto.
  rewrite <- H3. eapply sig_preserved1; eauto.
  constructor.
Qed.

Lemma transf_final_states1:
  forall st1 st2 r,
  match_states1 st1 st2 -> Cminor.final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. constructor.
Qed.

Theorem transf_program_correct1:
  forward_simulation (Cminor.semantics prog) (CminLoop.semantics tprog).
Proof.
  eapply forward_simulation_star_wf with (order := order).
  apply (Genv.senv_match TRANSL).
  eexact transf_initial_states1.
  eexact transf_final_states1.
  apply well_founded_ltof.
  eexact step_simulation1.
Qed.

End ToCminLoop.


(** Second, the CminLoop -> Cminor transformation. *)

Section BackToCminor.

Fixpoint add_gotos (s: stmt): Cminor.stmt := match s with
  | Sskip => Cminor.Sskip
  | Sassign id e => Cminor.Sassign id e
  | Sstore m e1 e2 => Cminor.Sstore m e1 e2
  | Scall id sig e args => Cminor.Scall id sig e args
  | Stailcall sig e args => Cminor.Stailcall sig e args
  | Sbuiltin id ef args => Cminor.Sbuiltin id ef args
  | Sseq s1 s2 => Cminor.Sseq (add_gotos s1) (add_gotos s2)
  | Sifthenelse e s1 s2 => Cminor.Sifthenelse e (add_gotos s1) (add_gotos s2)
  | Sloop s => Cminor.Sloop (add_gotos s)
  | Sblock s => Cminor.Sblock (add_gotos s)
  | Sdummy s => add_gotos s
  | Sexit n => Cminor.Sexit n
  | Sswitch islong e s n => Cminor.Sswitch islong e s n
  | Sreturn r => Cminor.Sreturn r
end.

Definition transf_function2 (f: function) : Cminor.function :=
  {|
    Cminor.fn_sig := fn_sig f;
    Cminor.fn_params := fn_params f;
    Cminor.fn_vars := fn_vars f;
    Cminor.fn_stackspace := fn_stackspace f;
    Cminor.fn_body := add_gotos (fn_body f)
  |}.
  
Definition transf_fundef2 (f: fundef) : Cminor.fundef :=
  transf_fundef transf_function2 f.

Definition transf_program2 (p: program) : Cminor.program :=
  transform_program transf_fundef2 p.


Definition match_prog2 (p: program) (tp: Cminor.program) : Prop :=
  match_program (fun _ f tf => tf = transf_fundef2 f) eq p tp.

Lemma transf_program_match2:
  forall p, match_prog2 p (transf_program2 p).
Proof.
  intros. eapply match_transform_program.
Qed.


Inductive match_cont2: cont -> Cminor.cont -> Prop :=
  | match_stop2:
      match_cont2 Kstop Cminor.Kstop
  | match_seq2: forall s k k',
      match_cont2 k k' ->
      match_cont2 (Kseq s k) (Cminor.Kseq (add_gotos s) k')
  | match_block2: forall k k',
      match_cont2 k k' ->
      match_cont2 (Kblock k) (Cminor.Kblock k')
  | match_call2: forall id f v e k k',
      match_cont2 k k' ->
      match_cont2 (Kcall id f v e k) (Cminor.Kcall id (transf_function2 f) v e k').

Inductive match_states2: state -> Cminor.state -> Prop :=
  | match_state: forall f s k k' sp e m,
      match_cont2 k k' ->
      match_states2 (State f s k sp e m) (Cminor.State (transf_function2 f) (add_gotos s) k' sp e m)
  | match_dummy: forall f s k k' sp e m,
      match_cont2 k k' ->
      match_states2 (State f (Sdummy s) k sp e m) (Cminor.State (transf_function2 f) (add_gotos s) k' sp e m)
  | match_callstate: forall f args k k' m,
      match_cont2 k k' ->
      match_states2 (Callstate f args k m) (Cminor.Callstate (transf_fundef2 f) args k' m)
  | match_returnstate: forall v k k' m,
      match_cont2 k k' ->
      match_states2 (Returnstate v k m) (Cminor.Returnstate v k' m).

Lemma match_cont2_is_call_cont: forall k k',
  match_cont2 k k' ->
  is_call_cont k ->
  Cminor.is_call_cont k'.
Proof.
  intros. destruct k; inv H0; now inv H.
Qed.

Lemma call_cont_match_cont2: forall k k',
  match_cont2 k k' ->
  match_cont2 (call_cont k) (Cminor.call_cont k').
Proof.
  intros. induction H; simpl.
  constructor. apply IHmatch_cont2. apply IHmatch_cont2. now constructor.
Qed.

Lemma remove_gotos_match_cont2: forall k k' s,
  match_cont2 k k' ->
  match_cont2 (Kseq s k) (Cminor.Kseq (add_gotos s) k').
Proof.
  intros. induction H; simpl; repeat constructor; auto.
Qed.


Variable prog: program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: match_prog2 prog tprog.
Let ge : genv := Genv.globalenv prog.
Let tge: Cminor.genv := Genv.globalenv tprog.

Lemma sig_preserved2:
  forall f,
  Cminor.funsig (transf_fundef2 f) = funsig f.
Proof.
  intros. unfold transf_fundef2, transf_function2. now destruct f.
Qed.

Ltac unfold_transf' H := unfold transf_fundef1, transf_partial_fundef, transf_function1, bind in H; destruct stmt_goto_free_dec in H; [|congruence]; injection H; intro T; subst.
Ltac unfold_transf := match goal with [ H: transf_fundef1 _ = OK _ |- _ ] => unfold_transf' H end.

Ltac solve_transl_extend :=
  try solve_transl TRANSL;
  try (eapply sig_preserved2; eauto);
  try (eapply match_cont2_is_call_cont; eauto);
  try (unfold_transf; eauto).

Fixpoint dummy_depth (s: stmt) := match s with
  | Sdummy s => S (dummy_depth s)
  | _ => O
end.

Definition state_depth' (s: state) := match s with
  | State f s k v e m => dummy_depth s
  | _ => O
end.

Definition order' := ltof state state_depth'.

Theorem step_simulation2:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states2 S1 S1' ->
  (* exists S2', Cminor.step tge S1' t S2' /\ match_states2 S2 S2'. *)
  exists S2', (plus Cminor.step tge S1' t S2' \/ star Cminor.step tge S1' t S2' /\ order' S2 S1) /\ match_states2 S2 S2'.

Proof.
  Ltac trivial_state := eexists; split; [ left; apply plus_one; econstructor; eauto; solve_transl_extend | econstructor; eauto ].

  intros; inv H; inv H0.
* inv H7; trivial_state.
* inv H7; trivial_state.
* trivial_state.
* trivial_state.
* trivial_state.
* eexists; split. left. apply plus_one. eapply Cminor.step_call with (fd:=transf_fundef2 fd); solve_transl_extend; eauto. repeat econstructor; eauto.
* eexists; split. left. apply plus_one. eapply Cminor.step_tailcall with (fd:=transf_fundef2 fd); solve_transl_extend; eauto. repeat econstructor; eauto; solve_transl_extend.
  now apply call_cont_match_cont2.
* trivial_state.
* trivial_state. now apply remove_gotos_match_cont2.
* destruct b; (eexists; split; [ left; apply plus_one; econstructor; solve_transl_extend; eauto | now econstructor]).
* trivial_state. now constructor.
* trivial_state. now constructor.
* eexists. split. right. split. apply star_refl. constructor. simpl. now constructor.
* eexists. split. right. split. apply star_refl. constructor. simpl. now constructor.
* inv H7; trivial_state.
* inv H7; trivial_state.
* inv H7; trivial_state.
* eexists; split. left. apply plus_one. econstructor; solve_transl_extend; eauto. now constructor.
* trivial_state. now apply call_cont_match_cont2.
* trivial_state. now apply call_cont_match_cont2.
* trivial_state.
* trivial_state.
* inv H4; trivial_state.
Qed.

Lemma transf_initial_states2:
  forall st1, initial_state prog st1 ->
  exists st2, Cminor.initial_state tprog st2 /\ match_states2 st1 st2.
Proof.
  intros. inv H.
  eexists; split; econstructor; eauto; solve_transl_extend.
  now eapply (Genv.init_mem_match TRANSL).
  erewrite (match_program_main TRANSL).
  erewrite (Genv.find_symbol_match TRANSL); eauto.
  eapply (Genv.find_funct_ptr_transf TRANSL); eauto.
  rewrite <- H3. eapply sig_preserved2; eauto.
  constructor.
Qed.

Lemma transf_final_states2:
  forall st1 st2 r,
  match_states2 st1 st2 -> final_state st1 r -> Cminor.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. constructor.
Qed.

Theorem transf_program_correct2:
  forward_simulation (CminLoop.semantics prog) (Cminor.semantics tprog).
Proof.
  eapply forward_simulation_star_wf with (order:=order').
  apply (Genv.senv_match TRANSL).
  eexact transf_initial_states2.
  eexact transf_final_states2.
  apply well_founded_ltof.
  eexact step_simulation2.
Qed.

End BackToCminor.