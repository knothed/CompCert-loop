(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*    David Knothe, FZI Research Center for Information Technology     *)
(*        Xavier Leroy, INRIA Paris-Rocquencourt                       *)
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

(** Putting both bigstep and smallstep semantics into the unified
    BehSem framework. Also, defining equivalence between
    smallstep and bigstep semantics via soundness and completeness. *)

Require Import Classical.
Require Import Coqlib.
Require Import Events.
Require Import Tracex.
Require Import Globalenvs.
Require Import Integers.
Require Import Behaviors SmallstepBehaviors.
Require Import Equality.
Require Import Smallstep Bigstep.
Require Import Foreverx.
Require Import Semantics.

(** * The BehSem associated with a smallstep semantics. *)

Require Import Smallstep.
Require Import SmallstepBehaviors.
Require Import Determinacy.

Section Smallstep.

Inductive small_forever L: tracex -> Prop :=
  | small_diverges: forall t, program_behaves L (Diverges t) -> small_forever L (Tfin t)
  | small_reacts: forall T, program_behaves L (Reacts T) -> small_forever L (Tinf T).

Inductive small_partial L: trace -> Prop :=
  | small_partial_intro: forall i t s, initial_state L i -> Star L i t s -> small_partial L t
  | small_no_initial_state: (~ exists s, initial_state L s) -> small_partial L E0.

(** To show compactness, we need determinacy. *)

Record SmallstepBehSem : Type := {
  sem: Smallstep.semantics;
  DET: determinate sem
}.
Coercion sem: SmallstepBehSem >-> Smallstep.semantics.

#[export] Instance SmallstepBehWeakSemantics: WeakBehSem SmallstepBehSem := {
  genvtype := Smallstep.genvtype;
  globalenv := Smallstep.globalenv;
  symbolenv := Smallstep.symbolenv;
  term := fun L t r => program_behaves L (Terminates t r);
  partial := small_partial;
  forever := small_forever;
}.

Section Compactness.

Context (L: SmallstepBehSem).

(** Compactness *)

Lemma forever_reactive_buildup: forall i T,
  (forall t T', t *** T' = T -> exists s, Star L i t s) ->
  (forall s t T', t *** T' = T -> Star L i t s -> Forever_reactive L s T').
Proof.
  cofix H. intros.
  destruct T'.
  assert ((t ++ e::nil) *** T' = T) by traceEq. apply H0 in H3 as [s'].
  pose proof H3. eapply cut_star in H3; [| apply DET | apply H2 ].
  replace (Econsinf e T') with ((e::nil) *** T') by traceEq. econstructor; eauto. easy.
  eapply H; eauto; traceEq.
Qed.

Lemma forever_reactive_compact: forall i T,
  (forall t, traceinf_prefix t T -> exists s, Star L i t s) ->
  Forever_reactive L i T.
Proof.
  intros. eapply forever_reactive_buildup with (t:=E0). intros. apply H. econstructor; eauto. traceEq. constructor.
Qed.

Lemma smallstep_compact: forall T,
  (forall t, traceinf_prefix t T -> small_partial L t) ->
  small_forever L (Tinf T).
Proof.
  intros. assert (exists i, initial_state L i) as [i].
  + destruct T. assert (traceinf_prefix (e::nil) (Econsinf e T)) by now econstructor. apply H in H0. inv H0. now exists i.
  + constructor. econstructor; eauto; econstructor. apply forever_reactive_compact. intros. assert (tracex_prefix t (Tinf T)) by auto.
    apply H in H2. inv H2. eapply DET in H0; eauto. subst. now exists s. exfalso. eapply H3. now exists i.
Qed.

End Compactness.

Lemma smallstep_partial_spec: forall (s: SmallstepBehSem), Partial_spec s.
Proof.
  intros. constructor; simpl in *.
  * intros. inv H0. 2: { inv H. symmetry in H0. apply app_eq_nil in H0 as []. subst. now constructor 2. }
    inv H. eapply split_star in H2 as [s' []]; auto. econstructor; eauto. apply DET.
  * intros. inv H0. inv H2. inv H. eapply split_star in H4 as [s'' []]; auto. econstructor; eauto. apply DET.
  * intros. inv H0.
  - inv H. inv H1. inv H0. eapply split_star in H2 as [s'' []]; auto. econstructor; eauto. apply DET.
  - inv H. inv H1. inv H0. eapply split_forever_reactive in H2 as [s'' []]; eauto. econstructor; eauto. apply DET.
  * intros. now apply smallstep_compact.
Qed.

#[export] Instance SmallstepSemantics: BehSem SmallstepBehSem := {
  partial_spec := smallstep_partial_spec;
}.

Lemma maximal_state_exists: forall (L: SmallstepBehSem) s,
  ~ Forever_silent L s ->
  (forall s' t', t' <> nil -> ~ Star L s t' s') ->
  exists s', Star L s E0 s' /\ Nostep L s'.
Proof.
  intros. destruct (classic (forall s1 t1, Star L s t1 s1 -> exists s2, Step L s1 E0 s2)).
  now apply diverges_forever_silent in H1.
  apply not_all_ex_not in H1 as [s']. apply not_all_ex_not in H1 as [t'].
  apply imply_to_and in H1 as []. pose proof (not_ex_all_not _ _ H2).
  exists s'. split.
  - destruct t'. auto. exfalso. eapply H0; eauto. congruence.
  - intros t s'' ?. destruct t. now apply H3 in H4. eapply H0 with (t':=t'**e::t); eauto.
    intro. apply app_eq_nil in H5 as []. congruence. eapply star_right; eauto.
Qed.

Theorem smallstep_behaves_equivalent: forall (L: SmallstepBehSem) beh,
  SmallstepBehaviors.program_behaves L beh <-> Semantics.behaves L beh.
Proof.
  intros. case beh; split; intros; try (constructor; auto; now constructor); try (inv H; auto; now inv H1).
  * inv H.
  - inv H1. constructor. constructor.
    + econstructor; eauto.
    + intros [t' []]. inv H1. 2: { symmetry in H5. apply app_eq_nil in H5 as []. congruence. }
      eapply DET in H0; eauto. subst.
      destruct t'. congruence. eapply cut_star in H6; eauto. 2: apply DET.
      inv H6. now apply H3 in H0.
    + intros [r]. inv H. inv H5. eapply DET in H0; eauto. subst.
      pose proof H8. apply DET in H8. eapply nostep_nostep_same in H2 as []; eauto. 2: apply DET. 2: now rewrite E0_right.
      subst. now apply H4 in H.
    + intro. inv H. inv H5. inv H1. eapply DET in H0; eauto. subst.
      eapply cut_star_same_trace_nostep in H2; eauto.
      eapply no_silent_nostep; eauto. all: apply DET.
  - repeat constructor.
    + now apply all_not_not_ex.
    + intros [t' []]. inv H0. now apply H1 in H2. now destruct t'.
    + intros [r]. inv H. now apply H1 in H0.
    + intro. inv H. inv H2. now apply H1 in H.
  * inv H. inv H1. inv H.
  - exploit maximal_state_exists.
    + intro. apply H3. constructor. econstructor; eauto. econstructor; eauto.
    + intros. intro. apply H0. exists t'. split; auto. econstructor; eauto. eapply star_trans; eauto.
    + intros [f []]. econstructor; eauto. constructor 4 with f; eauto. eapply star_trans; eauto. traceEq.
      intros r ?. apply H2. exists r. econstructor; eauto. constructor 1 with f; eauto. eapply star_trans; eauto. traceEq.
  - constructor 2. now apply not_ex_all_not.
Qed.


Lemma smallstep_forward_preservation: forall (L1 L2: SmallstepBehSem),
  SmallstepBehaviors.forward_preservation L1 L2 <->
  Semantics.forward_preservation L1 L2.
Proof.
  unfold Semantics.forward_preservation, SmallstepBehaviors.forward_preservation.
  split; intros.
  * apply smallstep_behaves_equivalent, H in H0 as [? []]. apply smallstep_behaves_equivalent in H0. now exists x.
  * apply smallstep_behaves_equivalent, H in H0 as [? []]. apply smallstep_behaves_equivalent in H0. now exists x.
Qed.

Lemma smallstep_backward_preservation: forall (L1 L2: SmallstepBehSem),
  SmallstepBehaviors.backward_preservation L1 L2 <->
  Semantics.backward_preservation L1 L2.
Proof.
  unfold Semantics.backward_preservation, SmallstepBehaviors.backward_preservation.
  split; intros.
  * apply smallstep_behaves_equivalent, H in H0 as [? []]. apply smallstep_behaves_equivalent in H0. now exists x.
  * apply smallstep_behaves_equivalent, H in H0 as [? []]. apply smallstep_behaves_equivalent in H0. now exists x.
Qed.


Section SmallstepProperties.

Context (L: SmallstepBehSem).

Lemma event_step_from_behaves: forall e t,
  partial L (t+:e) ->
  exists i s1 s2,
    initial_state L i /\ Star L i t s1 /\ Step L s1 (e::nil) s2.
Proof.
  intros. inv H. 2: { symmetry in H0. apply app_eq_nil in H0 as []. congruence. }
  eapply split_event_step in H1 as [s1 [s2 [? []]]]. now exists i, s1, s2. apply DET.
Qed.

Lemma smallstep_nonempty:
  nonempty L.
Proof.
  constructor. destruct (classic (exists i, initial_state L i)) as [[i]|]. econstructor; eauto. constructor. now constructor.
Qed.

Lemma smallstep_receptive:
  Smallstep.receptive L ->
  Semantics.receptive L.
Proof.
  constructor. intros.
  eapply event_step_from_behaves in H0 as [i [s [? [? []]]]].
  eapply (sr_receptive H) in H3 as [s2']. 2: apply H1.
  econstructor; eauto. eapply star_right; eauto.
Qed.

(** Determinism *)

Ltac unfold_det :=
  match goal with
  | [ H: Semantics.term L ?t ?b |- _ ] => inv H
  | [ H: Semantics.stuck L ?t |- _ ] => inv H
  | [ H: Semantics.partial L ?t |- _ ] => inv H
  | [ H: Semantics.forever L ?t |- _ ] => inv H
  | [ H: program_behaves (sem L) ?b |- _ ] => inv H
  | [ H: state_behaves (sem L) ?s ?b |- _ ] => inv H
  | [ H1: initial_state (sem L) ?i1, H2: initial_state (sem L) ?i2 |- _ ] =>
      eapply DET in H1; [| apply H2 ]; subst
  | [ H1: initial_state (sem L) ?i, H2: ~ exists s, initial_state (sem L) s |- _ ] =>
      exfalso; apply H2; now exists i
  end.

Ltac autoconstruct := eauto; repeat (econstructor; eauto).

Lemma smallstep_determinate:
  Semantics.determinate L.
Proof.
  constructor; intros.
  * inv H; inv H0; inv H1; inv H3; repeat unfold_det.
  - eapply nostep_nostep_same in H4 as []; eauto; subst; try (eapply DET; eauto). eapply sd_final_determ in H6; eauto. subst. now rewrite E0_right. apply DET.
  - exfalso. eapply nostep_left_E0 in H6 as []; eauto; subst.
    apply H4. rewrite E0_right. autoconstruct. all: eapply DET; eauto.
  - exfalso. eapply nostep_left_E0 in H4 as []; eauto; subst. eapply no_silent_nostep; eauto. all: eapply DET; eauto.
  - exfalso. eapply cut_forever_reactive in H4; eauto. inv H4. inv H0. auto. all: eapply DET; eauto.
  - exfalso. destruct x. eapply H3. rewrite E0_right in H8. autoconstruct.
    eapply H2. autoconstruct. congruence.
  - destruct x. now rewrite E0_right.
    exfalso. apply H5. autoconstruct. congruence.
  - auto.
  - exfalso. destruct x. rewrite E0_right in H7. eapply same_trace_forever_silent in H5; eauto. apply H3. autoconstruct. apply DET.
    apply H1. autoconstruct. congruence.
  - exfalso. eapply cut_forever_reactive in H7; eauto. inv H7. destruct t. easy.
    apply H1. eapply star_trans in H0; eauto. autoconstruct. apply DET.
  - exfalso. eapply nostep_right in H4; eauto; subst. eapply no_silent_nostep; eauto. all: eapply DET; eauto.
  - exfalso. destruct x. rewrite E0_right in *. apply H3. autoconstruct.
    eapply cut_star in H5; eauto. eapply cut_forever_silent in H5 as []; eauto. easy. all: apply DET.
  - destruct x. now rewrite E0_right.
    eapply cut_star, cut_forever_silent in H4; eauto. easy. all: apply DET.
  - exfalso. eapply unique_silent_reactive; eauto. apply DET.
  * apply event_step_from_behaves in H as [i [s1 [s2 [? []]]]], H0 as [i' [s1' [s2' [? []]]]].
    eapply DET in H; eauto; subst. pose proof H2. eapply cut_star_same_trace_step' in H2; eauto. subst.
    eapply DET; eauto. apply DET.
Qed.


End SmallstepProperties.

End Smallstep.


(** * The WeakBehSem associated with a specific bigstep semantics.
  Through equivalence with a smallstep semantics we can show partial_spec. *)

Require Bigstep.
Section Bigstep.

Inductive SpecificBigstep (B: Bigstep.semantics) : Type :=
| specific : SpecificBigstep B.

Lemma specific_bigstep_same: forall B (b1 b2: SpecificBigstep B),
  b1 = b2.
Proof.
  intros. now destruct b1, b2.
Qed.

#[export] Instance SpecificBigstepWeakSemantics: forall B, WeakBehSem (SpecificBigstep B) := {
  genvtype := fun _ => Bigstep.genvtype B;
  globalenv := fun _ => Bigstep.globalenv B;
  symbolenv := fun _ => Bigstep.symbolenv B;
  term := fun _ => Bigstep.terminates B;
  partial := fun _ => Bigstep.partial B;
  forever := fun _ => Bigstep.forever B
}.

End Bigstep.


(** * Soundness and completeness of a bigstep semantics with respect to a smallstep semantics.
      Together with determinacy, strong equivalence of the semantics follows. *)

Require Import Semantics.

Section SoundComplete.

Context `{b: Bigstep.semantics} (B: SpecificBigstep b) (L: SmallstepBehSem).

Record bigstep_sound: Prop :=
  Bigstep_sound {
    terminates_sound:
      forall t r, term B t r -> term L t r;
    forever_sound:
      forall T, forever B T -> forever L T;
    partial_sound:
      forall t, partial B t -> partial L t;
    symbols_sound:
      forall id : AST.ident, Senv.public_symbol (symbolenv L) id = Senv.public_symbol (symbolenv B) id
}.

Record bigstep_complete: Prop :=
  Bigstep_complete {
    terminates_complete:
      forall t r, term L t r -> term B t r;
    forever_complete:
      forall T, forever L T -> forever B T;
    partial_complete:
      forall t, partial L t -> partial B t;
    symbols_complete:
      forall id : AST.ident, Senv.public_symbol (symbolenv B) id = Senv.public_symbol (symbolenv L) id
}.

Lemma sound_forward_sim:
  bigstep_sound -> B ⇉ L.
Proof.
  intros. apply make_forward_transformation; apply H.
Qed.

Hypothesis (S: bigstep_sound) (C: bigstep_complete).

Lemma bigstep_partial_spec: forall s: SpecificBigstep b, Partial_spec s.
Proof.
  constructor.
  * intros. apply S in H0. apply C. eapply partial_spec in H0; eauto.
  * intros. apply S in H0. apply C. eapply partial_spec in H0; eauto.
  * intros. apply S in H0. apply C. eapply partial_spec in H0; eauto.
  * intros. apply C. eapply partial_spec. intros. apply S. apply H; auto.
Qed.

#[export] Instance SpecificBigstepSemantics: BehSem (SpecificBigstep b) := {
  partial_spec := bigstep_partial_spec
}.

Lemma complete_forward_sim:
  L ⇉ B.
Proof.
  intros. apply make_forward_transformation; apply C.
Qed.

Theorem big_small_equivalent:
  determinate L ->
  B ≡ L.
Proof.
  intros. apply equivalent_sym. eapply (@equivalence_from_forward_transformations SmallstepBehSem _ _ L (SpecificBigstep b) _ _ B).
  apply complete_forward_sim. apply sound_forward_sim. auto. auto.
Qed.

End SoundComplete.


(** * Soundness and of a bigstep semantics with respect to a general smallstep semantics. *)

Section BigSmallSoundGeneral.

Context `{b: Bigstep.semantics} (B: SpecificBigstep b) (L: Smallstep.semantics).

Record bigstep_sound_gen: Prop :=
  Bigstep_sound_gen {
    terminates_sound_gen:
      forall t r, term B t r -> program_behaves L (Terminates t r);
    forever_sound_gen:
      forall T, forever B T -> small_forever L T;
    partial_sound_gen:
      forall t, partial B t -> small_partial L t;
}.

Lemma smallstep_partial_has_behavior: forall t,
  small_partial L t -> exists beh t', program_behaves L beh /\ behavior_trace beh = t °° t'.
Proof.
  intros. inv H. destruct (state_behaves_exists L s). inv H.
  * exists (Terminates (t**t0) r), (Tfin t0). split. do 2 (econstructor; eauto). eapply star_trans; eauto. auto.
  * exists (Diverges (t**t0)), (Tfin t0). split. do 2 (econstructor; eauto). eapply star_trans; eauto. auto.
  * exists (Reacts (t***T)), (Tinf T). split. do 2 (econstructor; eauto). eapply star_forever_reactive; eauto. auto.
  * exists (Goes_wrong (t**t0)), (Tfin t0). split. do 2 (econstructor; eauto). eapply star_trans; eauto. auto.
  * exists (Goes_wrong E0), X0. split. constructor. intro. intro. apply H0. now exists s. auto.
Qed.

Lemma sound_forward_preserved:
  bigstep_sound_gen -> forall beh, behaves B beh -> exists beh', program_behaves L beh' /\ behavior_improves beh beh'.
Proof.
  intros. inv H0.
  * apply H in H1. exists (Terminates t r). split. inv H1. econstructor; eauto. now constructor.
  * inv H1. apply H in H0. apply smallstep_partial_has_behavior in H0 as [beh' [t' []]]. exists beh'. split; auto. apply prefix_improves_goes_wrong. rewrite H1. apply tracex_prefix_spec.
  * apply H in H1. exists (Diverges t). split. inv H1. auto. now constructor.
  * apply H in H1. exists (Reacts T). split. inv H1. auto. now constructor.
Qed.

End BigSmallSoundGeneral.