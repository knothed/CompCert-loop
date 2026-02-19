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

(** * Unroll loops with a static check whose condition is directly at the start. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import ZArith_dec.
Require Import Events.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Foreverx.
Require Import Bigstep.
Require Import Behaviors.
Require Import CminLoop.
Require Import CminLoopTransfCommon.
Require Import SemanticsSmallBig.
Require Import CminLoopBigSmallEquiv.
Require Import Semantics.
Require Import Linking.
Require Import Equality.
Require Import Tracex.
Require Import CminLoopUnswitching.
Require Import CminLoopWhileTrue.

Section Transformation.

(* An external parameter that decides whether a loop with the given inner body should be inverted or not.
   It is irrelevant to the correctness of the transformation. *)
Variable should_unroll_loop: stmt -> bool.

Definition max_unroll_depth := 16.

(** * Recognising an ordinary for-loop.
  `(for i = ?lit1; i < ?lit2; i++) { }`
*)

Section Recognising.

Inductive constant_comp: expr -> ident -> Z -> Prop :=
  | constant_lt: forall id max maxint,
      Int.signed maxint = max ->
      constant_comp (Ebinop (Ocmp Clt) (Evar id) (Econst (Ointconst maxint))) id max.

Inductive constant_init: stmt -> ident -> Z -> Prop :=
  | constant_init_intro: forall id z,
      constant_init (Sassign id (Econst (Ointconst z))) id (Int.signed z).

Inductive increment: stmt -> ident -> Prop :=
  | increment_intro: forall id o,
      Int.signed o = 1 ->
      increment (Sassign id (Ebinop Oadd (Evar id) (Econst (Ointconst o)))) id.

Inductive for_loop: stmt -> stmt -> expr -> stmt -> stmt -> Prop :=
  | for_loop_intro: forall init cond latch body,
      for_loop
      (Sseq
        init
        (Sblock
          (Sloop
            (Sseq
              (Sblock
                (Sseq
                  (Sifthenelse cond Sskip (Sexit 1))
                  body
                )
              )
              latch
            )
          )
        )
      )
      init cond latch body.

Ltac need e e' :=
  destruct e eqn:?; match goal with
    | [ E: e = e' |- _ ] => idtac
    | [ E: e = e' _ |- _ ] => idtac
    | [ E: e = e' _ _ |- _ ] => idtac
    | [ E: e = e' _ _ _ |- _ ] => idtac
    | [ E: e = e' _ _ _ _ |- _ ] => idtac
    | [ E: e = e' _ _ _ _ _ |- _ ] => idtac
    | _ => auto
  end.

Definition constant_comp_dec: forall e,
  {'(id, max) | constant_comp e id max} + {True}.
Proof.
  intros. need e Ebinop. need b Ocmp. need c Clt. need e0_1 Evar. need e0_2 Econst. need c0 Ointconst.
  left. now exists (i, Int.signed i0).
Defined.

Definition constant_init_dec: forall s,
  {'(id, init) | constant_init s id init} + {True}.
Proof.
  intros. need s Sassign. need e Econst. need c Ointconst.
  left. now exists (i, (Int.signed i0)).
Defined.

Definition increment_dec: forall s,
  {id | increment s id} + {True}.
Proof.
  intros. need s Sassign. need e Ebinop. need b Oadd. need e0_1 Evar. need e0_2 Econst. need c Ointconst. 
  destruct (peq i i0). 2: auto.
  destruct (Z.eq_dec (Int.signed i1) 1). 2: auto.
  subst. left. now eexists.
Qed.

Definition for_loop_dec: forall s,
  {'(init, cond, latch, body) | for_loop s init cond latch body} + {True}.
Proof.
  intros.
  need s Sseq.
    need s0_2 Sblock.
      need s0 Sloop.
        need s1 Sseq.
          need s2_1 Sblock.
            need s2 Sseq.
              need s3_1 Sifthenelse.
                need s3_3 Sskip.
                need s3_4 Sexit.
                  (destruct (Nat.eq_dec n 1)). 2: auto. subst.
  left. now exists (s0_1, e, s2_2, s3_2).
Defined.

End Recognising.


(** * Unrolling a loop.
  We do not recursively unroll loop bodys inside unrolled loops to avoid code explosion.
*)

Section Unrolling.

Context (body latch: stmt).
Context (cond: expr) (vmax: Z) (id: ident).

Definition orig_inner_loop := Sseq (Sblock (Sseq (Sifthenelse cond Sskip (Sexit 1)) body)) latch.

Definition single_iter_body :=
  Sseq body latch.

Fixpoint unroll_loop_inner (n: nat) := match n with
  | O => Sskip
  | S n => Sseq single_iter_body (unroll_loop_inner n)
end.

(** Unrolling correctness proof *)

Context (ge: genv) (f: function) (sp: val).

Hypothesis (INCR: increment latch id).
Hypothesis (COND: constant_comp cond id vmax).
Hypothesis (EXIT: no_exit body).
Hypothesis (VARS: doesnt_use_assigned_vars cond body).
Hypothesis (VMAX: Int.min_signed <= vmax <= Int.max_signed).

(* Shared lemmata *)

Lemma orig_cond_spec: forall e m v0 v
  (V: Int.min_signed <= v <= Int.max_signed)
  (ENV: e ! id = Some (Vint (Int.repr v))),
  eval_expr ge sp e m cond v0 ->
  (Val.bool_of_val v0 true <-> v < vmax) /\ (Val.bool_of_val v0 false <-> v >= vmax).
Proof.
  intros. inv COND. inv H. inv H3. inv H5. inv H6. inv H1.
  rewrite ENV in H0. injection H0; intro; subst.
  unfold Val.cmp, Val.of_optbool, Val.cmp_bool, Int.cmp, Int.lt, zlt. split; intros; split; intros.
  + inv H. rewrite negb_true_iff in H3.
    destruct Z_lt_dec in H2. 2: now inv H2. now rewrite Int.signed_repr in l.
  + destruct Z_lt_dec. constructor. rewrite Int.signed_repr in n; lia.
  + inv H. rewrite negb_false_iff in H3.
    destruct Z_lt_dec in H2. now inv H2. now rewrite Int.signed_repr in n0.
  + destruct Z_lt_dec. rewrite Int.signed_repr in l; lia. constructor.
Qed.

Lemma orig_inner_loop_out_normal: forall e1 m1 e2 m2 t out v
  (OUT: out <> Out_partial)
  (V: Int.min_signed <= v < vmax)
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  exec_stmt ge f sp e1 m1 orig_inner_loop t e2 m2 out ->
  out = Out_normal /\ e2 ! id = Some (Vint (Int.repr (v+1))).
Proof.
  intros. inv H; try congruence.
  + inv H2. inv H10; try easy.
    - inv H1. destruct b; inv H16. eapply orig_cond_spec with (v:=v) in H10 as []; eauto; try lia.
      apply H in H15. inv INCR. inv H7; try congruence. split. easy. inv H16. inv H6. inv H9. inv H10. inv H4.
      eapply var_unchanged_after_stmt in H8; eauto. 2: now destruct out0. 2: { intro. apply VARS. apply Exists_exists. exists id. split; eauto. inv COND. apply in_eq. }
      rewrite H3 in H8. injection H8; intro; subst.
      rewrite PTree.gss. f_equal. simpl. f_equal. rewrite Int.add_signed. rewrite Int.signed_repr. now rewrite H1. lia.
    - exfalso. inv H6; try easy. destruct b; now inv H16.
  + exfalso. inv H6; try easy. inv H4; try easy. apply no_exit_spec in H7; auto. now subst. now destruct out0.
    inv H6; try easy. destruct b; inv H15; try easy.
    eapply orig_cond_spec with (v:=v) in H14; eauto; lia.
Qed.

Lemma orig_inner_loop_out_exit: forall e1 m1 e2 m2 t out v
  (V: vmax <= v <= Int.max_signed)
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  exec_stmt ge f sp e1 m1 orig_inner_loop t e2 m2 out ->
  t = E0 /\ (out = Out_partial \/ out = Out_exit 0 /\ e1 = e2 /\ m1 = m2).
Proof.
  intros. inv H; try congruence; auto.
  + inv H2. inv H10; try easy.
    - exfalso. inv H1. destruct b; inv H16; try easy. eapply orig_cond_spec with (v:=v) in H10 as []; eauto.
      apply H in H15. lia. lia.
    - exfalso. inv H6; try easy. destruct b; now inv H16.
  + inv H6; auto. inv H4; auto.
    - exfalso. inv H1. destruct b; inv H15; try easy. eapply orig_cond_spec with (v:=v) in H14; eauto; lia.
    - inv H6; auto. destruct b; inv H15; auto. easy.
Qed.

Lemma orig_inner_loop_out_execinf: forall e1 m1 n t v
  (V: vmax <= v <= Int.max_signed)
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  execinf_stmt ge f sp e1 m1 orig_inner_loop n t ->
  False.
Proof.
  intros. inv H. inv H9.
  - inv H5. inv H11. destruct b; inv H15. inv H3. destruct b; inv H17.
    eapply orig_cond_spec with (v:=v) in H16; eauto. lia. lia.
  - inv INCR. inv H8.
Qed.

Lemma single_iter_body_spec: forall e1 m1 e2 m2 t out v
  (V: Int.min_signed <= v < vmax)
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  exec_stmt ge f sp e1 m1 orig_inner_loop t e2 m2 out ->
  exec_stmt ge f sp e1 m1 single_iter_body t e2 m2 out.
Proof.
  intros. inv H.
  + apply exec_partial_E0.
  + inv H2. inv H10; try easy.
    - inv H1. destruct b; inv H16; try easy.
      assert (out0 = Out_normal) by (eapply no_exit_spec; eauto; intro; now subst). subst.
      econstructor; eauto.
    - exfalso. inv H6; try easy. destruct b; now inv H16.
  + inv H6. apply exec_partial_E0. inv H4. apply exec_partial_E0.
    - assert (out0 = Out_partial) by (eapply no_exit_spec_partial; eauto; intro; now subst). subst.
      inv H1. destruct b; inv H15. now constructor.
    - inv H6. apply exec_partial_E0. destruct b; inv H15; try congruence; try apply exec_partial_E0; [idtac].
      exfalso. eapply orig_cond_spec with (v:=v) in H14; eauto; lia. 
Qed.

Lemma single_iter_body_partial_spec: forall e1 m1 e2 m2 t v
  (V: Int.min_signed <= v <= vmax)
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  exec_stmt ge f sp e1 m1 orig_inner_loop t e2 m2 Out_partial ->
  exec_stmt ge f sp e1 m1 single_iter_body t e2 m2 Out_partial.
Proof.
  intros. destruct (zeq v vmax).
  + subst. eapply orig_inner_loop_out_exit in H as []; eauto.
    subst. constructor. lia.
  + eapply single_iter_body_spec; eauto. lia.
Qed.

Lemma single_iter_body_execinf_spec: forall e1 m1 t n,
  execinf_stmt ge f sp e1 m1 orig_inner_loop t n ->
  execinf_stmt ge f sp e1 m1 single_iter_body t n.
Proof.
  intros. inv H. 2: { inv INCR. rewrite <- H0 in H8. inv H8. }
  inv H9. inv H5. inv H11. destruct b; inv H15.
  inv H3. destruct b; inv H17. constructor. auto.
  rewrite X0_left in *. destruct H2 as [|[?[?[]]]].
  subst. eapply execinf_X0_irrel; eauto. pose proof (H3 eq_refl). eapply execinf_mon; eauto. lia.
Qed.

(* Exec normal *)

Lemma count_orig_loop: forall v (V: Int.min_signed <= v <= vmax),
  forall e1 m1 t e2 m2 out
  (OUT: out <> Out_partial)
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  exec_stmt ge f sp e1 m1 (Sloop orig_inner_loop) t e2 m2 out ->
  exec_loop_counted_l ge f sp e1 m1 orig_inner_loop t e2 m2 out (Z.to_nat (vmax-v)).
Proof.
  intros v V. set (n := Z.to_nat (vmax-v)). replace v with (vmax - Z.of_nat n) in * by lia.
  induction n; intros.
  + inv H.
  - now constructor.
  - exfalso. eapply orig_inner_loop_out_exit with (v:=vmax) in H1 as [?[|[?[]]]]. congruence. congruence. lia. rewrite Z.sub_0_r in ENV. eauto.
  - pose proof H1. eapply orig_inner_loop_out_exit with (v:=vmax) in H1 as []; subst. now constructor. auto. lia. rewrite Z.sub_0_r in ENV. eauto.
  + inv H.
  - congruence.
  - econstructor; eauto. eapply IHn; eauto. lia. eapply orig_inner_loop_out_normal in H1 as []; eauto.
    rewrite H0. do 3 f_equal. lia. congruence. lia.
  - eapply orig_inner_loop_out_normal in H1 as []; eauto. congruence. lia.
Qed.

Inductive shift': Z -> Z -> Z -> Prop :=
  | do_shift: forall vmax' vmax, vmax' < vmax -> shift' vmax' vmax 1
  | dont_shift: forall vmax, shift' vmax vmax 0.

Lemma unroll_counted_loop_gen:
  forall vmax' (VMAX': Int.min_signed <= vmax' <= vmax) v (V: Int.min_signed <= v <= vmax'),
  forall e1 m1 t e2 m2 out i
  (SH: shift' vmax' vmax i)
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  exec_loop_counted_l ge f sp e1 m1 orig_inner_loop t e2 m2 out (Z.to_nat (vmax'-v)) ->
  exec_stmt ge f sp e1 m1 (unroll_loop_inner (Z.to_nat (vmax'-v+i))) t e2 m2 (outcome_block out).
Proof.
  intros vmax' VMAX' v V. set (n := Z.to_nat (vmax'-v)). replace v with (vmax' - Z.of_nat n) in * by lia.
  induction n; intros.
  + simpl. inv H.
    replace (Z.to_nat (vmax'-(vmax'-0)+i)) with (Z.to_nat i) by lia.
    simpl. rewrite Z.sub_0_r in ENV. inv SH.
    - destruct out; try now eapply orig_inner_loop_out_normal with (v:=vmax') in H0 as [].
      * constructor. eapply single_iter_body_spec; eauto. easy. easy.
      * econstructor; eauto. eapply single_iter_body_spec; eauto. lia. constructor. traceEq.
    - eapply orig_inner_loop_out_exit with (v:=vmax) in H0 as [?[|[?[]]]].
      subst. apply exec_partial_E0. inv H0. constructor. lia. auto.
  + inv H.
    pose proof ENV. eapply orig_inner_loop_out_normal in ENV as []; eauto; try lia; try congruence.
    replace (vmax' - Z.of_nat (S n) + 1) with (vmax' - Z.of_nat n) in H3 by lia. eapply IHn in H3; eauto; try lia.
    replace (Z.to_nat (vmax' - (vmax' - Z.of_nat (S n)) + i)) with (S (Z.to_nat (vmax' - (vmax' - Z.of_nat n) + i))) by (inv SH; lia).
    econstructor; eauto. eapply single_iter_body_spec with (v := vmax' - Z.of_nat (S n)); eauto. lia.
Qed.

Lemma unroll_counted_loop: forall v (V: Int.min_signed <= v <= vmax),
  forall e1 m1 t e2 m2 out
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  exec_loop_counted_l ge f sp e1 m1 orig_inner_loop t e2 m2 out (Z.to_nat (vmax-v)) ->
  exec_stmt ge f sp e1 m1 (unroll_loop_inner (Z.to_nat (vmax-v))) t e2 m2 (outcome_block out).
Proof.
  intros. rewrite <- Z.add_0_r at 1. eapply unroll_counted_loop_gen; eauto; try lia. constructor.
Qed.

(* Exec partial *)

Lemma count_orig_loop_partial: forall v (V: Int.min_signed <= v <= vmax),
  forall e1 m1 t e2 m2
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  exec_stmt ge f sp e1 m1 (Sloop orig_inner_loop) t e2 m2 Out_partial ->
  exists n, le n (Z.to_nat (vmax-v)) /\ exec_loop_counted_l ge f sp e1 m1 orig_inner_loop t e2 m2 Out_partial n.
Proof.
  intros v V. set (n := Z.to_nat (vmax-v)). replace v with (vmax - Z.of_nat n) in * by lia.
  induction n; intros.
  + inv H.
  - exists O. split; auto. constructor. apply exec_partial_E0.
  - exfalso. eapply orig_inner_loop_out_exit in H1 as [?[|[?[]]]]; eauto. inv H0; congruence. congruence. lia.
  - exists O. split; auto. now constructor.
  + inv H.
  - exists O. split. lia. constructor. apply exec_partial_E0.
  - eapply IHn in H2 as [n' []]; eauto.
    2: lia. 2: { eapply orig_inner_loop_out_normal in H1 as []; eauto. rewrite H0. do 3 f_equal. lia. congruence. lia. }
    exists (S n'). split. lia. econstructor; eauto.
  - exists O. split. lia. econstructor; eauto.
Qed.

Lemma further_unroll_partial_out: forall m n e1 m1 t e2 m2,
  exec_stmt ge f sp e1 m1 (unroll_loop_inner n) t e2 m2 Out_partial ->
  exec_stmt ge f sp e1 m1 (unroll_loop_inner (n+m)) t e2 m2 Out_partial.
Proof.
  induction m; intros. now rewrite Nat.add_0_r.
  replace (n + S m)%nat with (S (n+m)) by lia. eapply IHm in H. simpl.
  generalize dependent t. generalize dependent e1. generalize dependent m1. induction (n+m)%nat; intros.
  + simpl in *. inv H. constructor.
  + simpl in *. inv H. now constructor. now econstructor; eauto. now constructor; auto.
Qed.

(* Execinf *)

Lemma count_execinf_loop: forall v (V: Int.min_signed <= v <= vmax),
  forall e1 m1 t M
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  execinf_stmt ge f sp e1 m1 (Sloop orig_inner_loop) M t ->
  exists n,
    execinf_loop_counted ge f sp e1 m1 orig_inner_loop M t n /\
    le n (Z.to_nat (vmax-v)).
Proof.
  intros v V. set (n := Z.to_nat (vmax-v)). replace v with (vmax - Z.of_nat n) in * by lia.
  induction n; intros.
  + inv H.
  - exists O. repeat split. now constructor. lia.
  - exfalso. eapply orig_inner_loop_out_exit with (v:=vmax) in H2 as []. now inv H0. lia. now rewrite Z.sub_0_r in ENV.
  + inv H.
  - exists O. split. now constructor. lia.
  - eapply IHn in H3 as [n' [?]]; eauto. 2: lia.
    exists (S n'). split. econstructor 1; eauto. lia.
    eapply orig_inner_loop_out_normal in H2 as []; eauto; try lia; try easy.
    rewrite H0. do 3 f_equal. lia.
Qed.

Lemma unroll_counted_loop_inf_gen:
  forall vmax' (VMAX': Int.min_signed <= vmax' <= vmax) v (V: Int.min_signed <= v <= vmax'),
  forall e1 m1 t M i
  (SH: shift' vmax' vmax i)
  (ENV: e1 ! id = Some (Vint (Int.repr v))),
  execinf_loop_counted ge f sp e1 m1 orig_inner_loop M t (Z.to_nat (vmax'-v)) ->
  execinf_stmt ge f sp e1 m1 (unroll_loop_inner (Z.to_nat (vmax'-v+i))) M t.
Proof.
  intros vmax' VMAX' v V. set (n := Z.to_nat (vmax'-v)). replace v with (vmax' - Z.of_nat n) in * by lia.
  induction n; intros.
  + simpl. inv H. replace (Z.to_nat (vmax'-(vmax'-0)+i)) with (Z.to_nat i) by lia. inv SH.
    * constructor. apply guard_incr with (M-1). lia. eapply execinf_guard; eauto. now apply single_iter_body_execinf_spec.
    * exfalso. eapply orig_inner_loop_out_execinf in H0; eauto. lia.
  + inv H.
    pose proof H2. eapply orig_inner_loop_out_normal with (v := vmax' - Z.of_nat (S n)) in H2 as []; eauto; try lia; try congruence.
    replace (vmax' - Z.of_nat (S n) + 1) with (vmax' - Z.of_nat n) in H2 by lia.
    replace (Z.to_nat (vmax' - (vmax' - Z.of_nat (S n)) + i)) with (S (Z.to_nat (vmax' - (vmax' - Z.of_nat n) + i))) by (inv SH; lia).
    eapply IHn in H3; eauto; try lia.
    simpl. eapply execinf_Sseq_2; eauto. eapply single_iter_body_spec with (v := vmax' - Z.of_nat (S n)); eauto. lia.
Qed.

Lemma further_unroll_execinf: forall m n e1 m1 t M,
  execinf_stmt ge f sp e1 m1 (unroll_loop_inner n) M t ->
  execinf_stmt ge f sp e1 m1 (unroll_loop_inner (n+m)) M t.
Proof.
  induction m; intros. now rewrite Nat.add_0_r.
  replace (n + S m)%nat with (S (n+m)) by lia. eapply IHm in H. simpl.
  generalize dependent t. generalize dependent e1. generalize dependent m1. generalize dependent M. induction (n+m)%nat; intros.
  + simpl in *. inv H.
  + simpl in *. inv H. constructor; eauto. eapply execinf_Sseq_2; eauto.
Qed.

(** Full unrolling together with counter intitialisation. *)

Context (init: stmt) (v: Z).
Hypothesis (INIT: constant_init init id v).

Definition unrolled_loop :=
  Sseq init (unroll_loop_inner (Z.to_nat (vmax-v))).

Section UnrollSpec.

Hypothesis (V: Int.min_signed <= v <= vmax).

Theorem unroll_spec_normal: forall e1 m1 t e2 m2 out
  (OUT: out <> Out_partial),
  exec_stmt ge f sp e1 m1 (Sseq init (Sblock (Sloop orig_inner_loop))) t e2 m2 out ->
  exec_stmt ge f sp e1 m1 unrolled_loop t e2 m2 out.
Proof.
  intros. inv H.
  + apply exec_partial_E0.
  + inv INIT. rewrite <- H in H2. inv H2. inv H7. constructor. inv H12. inv H2.
    eapply count_orig_loop in H6; eauto.
    - eapply unroll_counted_loop in H6; eauto.
      econstructor; eauto. rewrite <- H. constructor. constructor. constructor.
      now rewrite PTree.gss, <- H1, Int.repr_signed.
    - now destruct out0.
    - now rewrite PTree.gss, <- H1, Int.repr_signed.
  + inv INIT. rewrite <- H in H6. inv H6. constructor. congruence.
Qed.

Theorem unroll_spec_partial: forall e1 m1 t e2 m2,
  exec_stmt ge f sp e1 m1 (Sseq init (Sblock (Sloop orig_inner_loop))) t e2 m2 Out_partial ->
  exec_stmt ge f sp e1 m1 unrolled_loop t e2 m2 Out_partial.
Proof.
  intros. inv H.
  + apply exec_partial_E0.
  + inv INIT. rewrite <- H in H2. inv H2. inv H12. inv H2. inv H7. econstructor; eauto.
    destruct out; inv H6. 2: destruct n; inv H2.
    eapply count_orig_loop_partial in H11 as [n []]; eauto.
    2: now rewrite PTree.gss, <- H1, Int.repr_signed.
    econstructor; eauto. rewrite <- H. econstructor. econstructor. econstructor.
    set (vmax' := v + Z.of_nat n). set (i := if Z.eq_dec vmax' vmax then 0 else 1).
    assert (SH: shift' vmax' vmax i). { destruct Z.eq_dec; subst; constructor; lia. }
    replace n with (Z.to_nat (vmax' - v)) in * by lia.
    replace (Z.to_nat (vmax-v)) with (Z.to_nat (vmax'-v+i) + Z.to_nat (vmax-vmax'-i))%nat by (inv SH; lia).
    eapply unroll_counted_loop_gen in H2; eauto; try lia. 2: now rewrite PTree.gss, <- H1, Int.repr_signed.
    now apply further_unroll_partial_out.
  + now constructor.
Qed.

Theorem unroll_spec_execinf_inner: forall e m e1 m1 t t1 M,
  execinf_stmt ge f sp e1 m1 (Sblock (Sloop orig_inner_loop)) M t ->
  exec_stmt ge f sp e m init t1 e1 m1 Out_normal ->
  execinf_stmt ge f sp e1 m1 (unroll_loop_inner (Z.to_nat (vmax-v))) M t.
Proof.
  intros. inv H.  
  eapply count_execinf_loop in H7 as [n' [?]]; eauto.
  2: { inv INIT. inv H0. inv H11. inv H0. now rewrite PTree.gss, Int.repr_signed. }
  set (vmax' := v + Z.of_nat n'). set (i := if Z.eq_dec vmax' vmax then 0 else 1).
  assert (SH: shift' vmax' vmax i). { destruct Z.eq_dec; subst; constructor; lia. }
  replace (Z.to_nat (vmax-v)) with (Z.to_nat (vmax'-v+i) + Z.to_nat (vmax-vmax'-i))%nat by (inv SH; lia).
  replace n' with (Z.to_nat (vmax' - v)) in * by lia.
  eapply unroll_counted_loop_inf_gen in H; eauto; try lia. 2: { inv INIT. inv H0. inv H12. inv H3. now rewrite PTree.gss, Int.repr_signed. }
  eapply further_unroll_execinf.
  eapply execinf_mon; eauto. lia.
Qed.

End UnrollSpec.

Section EmptyUnrollSpec.

Hypothesis (V: vmax < v <= Int.max_signed).

Theorem empty_unroll_spec: forall e1 m1 t e2 m2 out,
  exec_stmt ge f sp e1 m1 (Sseq init (Sblock (Sloop orig_inner_loop))) t e2 m2 out ->
  exec_stmt ge f sp e1 m1 unrolled_loop t e2 m2 out.
Proof.
  intros. inv H.
  + apply exec_partial_E0.
  + inv INIT. rewrite <- H in H2. inv H2. inv H7. constructor. inv H12. inv H2.
    inv H6.
    - constructor.
    - eapply orig_inner_loop_out_exit with (v:=v) in H2 as [? []].
      easy. easy. lia. now rewrite PTree.gss, <- H1, Int.repr_signed.
    - eapply orig_inner_loop_out_exit with (v:=v) in H2 as [? [|[?[]]]]; eauto.
      * subst. constructor.
      * subst. econstructor; eauto. rewrite <- H. repeat constructor.
        replace (Z.to_nat (vmax-v)) with O by lia. constructor.
      * lia.
      * now rewrite PTree.gss, <- H1, Int.repr_signed.
  + inv INIT. rewrite <- H in H6. inv H6. constructor. congruence.
Qed.

Theorem empty_unroll_spec_execinf_inner: forall e m e1 m1 t t1 M,
  execinf_stmt ge f sp e1 m1 (Sblock (Sloop orig_inner_loop)) M t ->
  exec_stmt ge f sp e m init t1 e1 m1 Out_normal ->
  False.
Proof.
  intros.
  + inv H. inv H7.
  - inv H8.
  * inv H12. inv H8. inv H14. destruct b; inv H18. inv H6. destruct b; inv H20. eapply orig_cond_spec with (v:=v) in H19; eauto.
     lia. lia. inv INIT. inv H0. inv H18. inv H6. now rewrite PTree.gss, Int.repr_signed.
  * inv INCR. inv H11.
  - eapply orig_inner_loop_out_exit with (v:=v) in H3 as [? []]; eauto. easy. easy. lia.
    inv INIT. inv H0. inv H13. inv H0. now rewrite PTree.gss, Int.repr_signed.
Qed.

End EmptyUnrollSpec.

Hypothesis (V: Int.min_signed <= v <= Int.max_signed).

Corollary unroll_spec:
  (forall e1 m1 t e2 m2 out,
    exec_stmt ge f sp e1 m1 (Sseq init (Sblock (Sloop orig_inner_loop))) t e2 m2 out ->
    exec_stmt ge f sp e1 m1 unrolled_loop t e2 m2 out).
Proof.
  intros; destruct (Z_le_dec v vmax).
  + subst. destruct (outcome_eq_dec out Out_partial).
    subst. now apply unroll_spec_partial. now apply unroll_spec_normal.
  + eapply empty_unroll_spec; eauto. lia.
Qed.

Corollary unroll_spec_execinf: forall e m e1 m1 t t1 M,
  execinf_stmt ge f sp e1 m1 (Sblock (Sloop orig_inner_loop)) M t ->
  exec_stmt ge f sp e m init t1 e1 m1 Out_normal ->
  execinf_stmt ge f sp e1 m1 (unroll_loop_inner (Z.to_nat (vmax-v))) M t.
Proof.
  intros. destruct (Z_le_dec v vmax).
  + eapply unroll_spec_execinf_inner; eauto. lia.
  + exfalso. eapply empty_unroll_spec_execinf_inner; eauto. lia.
Qed.

End Unrolling.


(*** TRANSFORMATION AND SEMANTIC PRESERVATION ***)

Fixpoint transform_stmt (s: stmt) : stmt.
Proof.
  destruct s eqn:?.
  + exact s.
  + exact s.
  + exact s.
  + exact s.
  + exact s.
  + exact s.
  + set (s' := Sseq (transform_stmt s0_1) (transform_stmt s0_2)).
    destruct (for_loop_dec (Sseq s0_1 s0_2)) as [[[[[init cond] latch] body]]|]. 2: exact s'.
    destruct (constant_init_dec s0_1) as [[[id v0]]|]. 2: exact s'.
    destruct (constant_comp_dec cond) as [[[id' vmax]]|]. 2: exact s'.
    destruct (increment_dec latch) as [[id'']|]. 2: exact s'.
    destruct (no_exit_dec body). 2: exact s'.
    destruct (doesnt_use_assigned_vars_dec cond body). 2: exact s'.
    destruct (peq id id'). 2: exact s'.
    destruct (peq id id''). 2: exact s'.
    subst id' id''.
    case (should_unroll_loop body) eqn:?. 2: exact s'.
    case (Z_le_dec (vmax-v0) max_unroll_depth) eqn:?. 2: exact s'.
    exact (unrolled_loop body latch vmax init v0).
  + exact (Sifthenelse e (transform_stmt s0_1) (transform_stmt s0_2)).
  + exact (Sloop (transform_stmt s0)).
  + exact (Sblock (transform_stmt s0)).
  + exact (Sdummy (transform_stmt s0)).
  + exact s.
  + exact s.
  + exact s.
Defined.

(* Unfold transformation *)
Ltac unfold_eq_rect := unfold eq_rect; repeat match goal with
  | [ |- exec_stmt _ _ _ _ _ (match ?e with _ => _ end _) _ _ _ _ ] => destruct e
  | [ |- execinf_stmt _ _ _ _ _ (match ?e with _ => _ end _) _ _ ] => destruct e
end.

Ltac destruct_conditions solve_trivial :=
  destruct (for_loop_dec _) as [[[[[init cond] latch] body]]|]; [| solve_trivial ];
  destruct (constant_init_dec _) as [[[id v0]]|]; [| solve_trivial ];
  destruct (constant_comp_dec cond) as [[[id' vmax]]|]; [| solve_trivial ];
  destruct (increment_dec latch) as [[id'']|]; [| solve_trivial ];
  destruct (no_exit_dec body); [| solve_trivial ];
  destruct (doesnt_use_assigned_vars_dec cond body); [| solve_trivial ];
  destruct (peq id id'); [| solve_trivial ];
  destruct (peq id id''); [| solve_trivial ];
  destruct (should_unroll_loop body) eqn:?; [| unfold_eq_rect; solve_trivial ];
  destruct (Z_le_dec (vmax-v0) max_unroll_depth) eqn:?; [| unfold_eq_rect; solve_trivial ].


Definition transl_function (f: function) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_vars)
    f.(fn_stackspace)
    (transform_stmt f.(fn_body)).

Definition transl_fundef (f: fundef) : fundef :=
  transf_fundef transl_function f.

Definition transl_program (p: program) : program :=
  transform_program transl_fundef p.

Definition match_prog (p: program) (tp: program) :=
  match_program (fun cu f tf => tf = transl_fundef f) eq p tp.


Section TRANSLATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge : genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma function_ptr_translated:
  forall b (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transl_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transl_fundef f).
Proof (Genv.find_funct_transf TRANSL).


Lemma sig_preserved:
  forall f,
  funsig (transl_fundef f) = funsig f.
Proof.
  intros. unfold transl_fundef, transf_fundef, transl_function. now case f.
Qed.

Ltac solve_transl_extend :=
  solve_transl TRANSL;
  try (rewrite sig_preserved; eauto).

Ltac solve_trivial := econstructor; eauto; solve_transl_extend; fail.

Ltac here_transl := try (intros; split; econstructor; eauto; solve_transl_extend; fail).

Lemma transl_exec_correct:
   (forall m1 f vargs t m2 vres out,
    eval_funcall ge m1 f vargs t m2 vres out ->
    eval_funcall tge m1 (transl_fundef f) vargs t m2 vres out)
/\ (forall f v e1 m1 s t e2 m2 out,
    exec_stmt ge f v e1 m1 s t e2 m2 out ->
    exec_stmt tge (transl_function f) v e1 m1 s t e2 m2 out /\ exec_stmt tge (transl_function f) v e1 m1 (transform_stmt s) t e2 m2 out).
Proof.
  eapply eval_funcall_exec_stmt_ind2; here_transl; intros.
  * constructor. 
  * inv H2. econstructor; eauto.
  * econstructor; eauto; solve_transl_extend.
  * econstructor; eauto; solve_transl_extend.
  * split; eapply exec_Scall with (fd:=transl_fundef fd); solve_transl_extend; eauto.
  * split; econstructor; eauto; solve_transl_extend; case b in *; apply H2.
  * inv H0. inv H2.
    split. now econstructor; eauto.
    unfold transform_stmt; fold transform_stmt.
    destruct_conditions solve_trivial. unfold_eq_rect.
    inv y. eapply unroll_spec; eauto.
    inv y1. apply Int.signed_range.
    inv y0. apply Int.signed_range.
    eapply exec_Sseq_continue; eauto.
  * inv H0.
    split. now econstructor; eauto.
    unfold transform_stmt; fold transform_stmt.
    destruct_conditions solve_trivial. unfold_eq_rect.
    inv y. eapply unroll_spec; eauto.
    inv y1. apply Int.signed_range.
    inv y0. apply Int.signed_range.
    eapply exec_Sseq_stop; eauto.
  * inv H0. inv H2. here_transl.
  * inv H0. here_transl.
  * inv H0. here_transl.
  * inv H0. here_transl.
  * split; eapply exec_Stailcall with (fd:=transl_fundef fd); eauto; solve_transl_extend.
Qed.

Ltac solve_inf :=
  solve_transl_extend;
  eauto;
  try (eapply transl_exec_correct; eauto; fail).

Lemma transl_execinf_correct:
  forall m f vargs n t,
  evalinf_funcall ge m f vargs n t ->
  evalinf_funcall tge m (transl_fundef f) vargs n t.
Proof.
  cofix CIH_FUN.
  assert (CIHST2: forall f v e m s t n,
    execinf_stmt ge f v e m s n t ->
    execinf_stmt tge (transl_function f) v e m (transform_stmt s) n t).
  cofix CIH_STMT.
  assert (CIHST1: forall f v e m s t n,
    execinf_stmt ge f v e m s n t ->
    execinf_stmt tge (transl_function f) v e m s n t).
  cofix CIH_ORIG.
  intros. destruct H; (econstructor; solve_inf; fail).
  + intros. destruct H; try (econstructor; solve_inf; fail).
  * econstructor; solve_inf; eauto. case b in *; now apply CIH_STMT.
  * unfold transform_stmt; fold transform_stmt.
    destruct_conditions solve_trivial. unfold_eq_rect.
    exfalso. inv y. inv y0. inv H0.
  * unfold transform_stmt; fold transform_stmt.
    destruct_conditions ltac:(eapply execinf_Sseq_2; eauto; solve_inf; fail). inv y.
    eapply execinf_Sseq_2 with (M:=M); solve_inf.
    eapply unroll_spec_execinf in H1; eauto.
    inv y1. apply Int.signed_range.
    inv y0. apply Int.signed_range.
  * eapply execinf_Sloop_loop; solve_inf. eapply CIH_STMT in H1; eauto.
  + intros. inv H. econstructor; eauto. eapply CIHST2; eauto.
Qed.

Theorem forward_preservation:
  bigstep_semantics prog ⇉ bigstep_semantics tprog.
Proof.
  apply make_forward_transformation.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_exec_correct; eauto.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_execinf_correct with (n:=N). auto.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_exec_correct; eauto.
    apply bigstep_nonempty.
  * apply (Genv.senv_transf TRANSL).
Qed.

Theorem backward_preservation:
  bigstep_semantics prog ⇇ bigstep_semantics tprog.
Proof.
  apply forward_to_backward.
  apply bigstep_semantics_determinate.
  apply bigstep_semantics_receptive.
  apply bigstep_semantics_nonempty.
  apply forward_preservation.
Qed.

End TRANSLATION.

End Transformation.