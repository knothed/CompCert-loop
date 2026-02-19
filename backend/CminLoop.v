(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
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

(** Abstract syntax and semantics for the CminLoop language.
    CminLoop is identical to Cminor with the difference that it does not have goto statements.
    This makes its bigstep and smallstep semantics behaviorally equivalent. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Foreverx.
Require Import SemanticsSmallBig.
Require Import Bigstep.
Require Import Semantics.
Require Import Tracex.
Require Import Switch.
Require Import Cminor.
Require Import Classical.
Export Cminor.

(** * Abstract syntax *)

(** Statements include expression evaluation, assignment to local variables,
  memory stores, function calls, an if/then/else conditional, infinite
  loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1]
  enclosing [Sblock] statements. *)

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Stailcall: signature -> expr -> list expr -> stmt
  | Sbuiltin : option ident -> external_function -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sdummy: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt.

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics (small-step) *)

(** Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
*)

Definition genv := Genv.t fundef unit.
Definition env := PTree.t val.

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. *)

Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
  | _, _ => PTree.empty val
  end.

Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.

Definition set_optvar (optid: option ident) (v: val) (e: env) : env :=
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> val -> env -> cont -> cont.
                                        (**r return to caller *)

(** States *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: env)                   (**r current local environment *)
             (m: mem),                  (**r current memory state *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont)                  (**r what to do next  *)
             (m: mem),                  (**r memory state *)
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont)                  (**r what to do next *)
             (m: mem),                  (**r memory state *)
      state.


(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.


Section RELSEM.

Variable ge: genv.

(** One step of execution *)

Inductive step: state -> trace -> state -> Prop :=

  | step_skip_seq: forall f s k sp e m,
      step (State f Sskip (Kseq s k) sp e m)
        E0 (State f s k sp e m)
  | step_skip_block: forall f k sp e m,
      step (State f Sskip (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
  | step_skip_call: forall f k sp e m m',
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f Sskip k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate Vundef k m')

  | step_assign: forall f id a k sp e m v,
      eval_expr ge sp e m a v ->
      step (State f (Sassign id a) k sp e m)
        E0 (State f Sskip k sp (PTree.set id v e) m)

  | step_store: forall f chunk addr a k sp e m vaddr v m',
      eval_expr ge sp e m addr vaddr ->
      eval_expr ge sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr a) k sp e m)
        E0 (State f Sskip k sp e m')

  | step_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k sp e m)
        E0 (Callstate fd vargs (Kcall optid f sp e k) m)

  | step_tailcall: forall f sig a bl k sp e m vf vargs fd m',
      eval_expr ge (Vptr sp Ptrofs.zero) e m a vf ->
      eval_exprlist ge (Vptr sp Ptrofs.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Stailcall sig a bl) k (Vptr sp Ptrofs.zero) e m)
        E0 (Callstate fd vargs (call_cont k) m')

  | step_builtin: forall f optid ef bl k sp e m vargs t vres m',
      eval_exprlist ge sp e m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef bl) k sp e m)
         t (State f Sskip k sp (set_optvar optid vres e) m')

  | step_seq: forall f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e m)
        E0 (State f s1 (Kseq s2 k) sp e m)

  | step_ifthenelse: forall f a s1 s2 k sp e m v b,
      eval_expr ge sp e m a v ->
      Val.bool_of_val v b ->
      step (State f (Sifthenelse a s1 s2) k sp e m)
        E0 (State f (if b then s1 else s2) k sp e m)

  | step_loop: forall f s k sp e m,
      step (State f (Sloop s) k sp e m)
        E0 (State f s (Kseq (Sloop s) k) sp e m)

  | step_block: forall f s k sp e m,
      step (State f (Sblock s) k sp e m)
        E0 (State f s (Kblock k) sp e m)

  | step_dummy: forall f s k sp e m,
      step (State f (Sdummy s) k sp e m)
        E0 (State f s k sp e m)

  | step_exit_seq: forall f n s k sp e m,
      step (State f (Sexit n) (Kseq s k) sp e m)
        E0 (State f (Sexit n) k sp e m)
  | step_exit_block_0: forall f k sp e m,
      step (State f (Sexit O) (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
  | step_exit_block_S: forall f n k sp e m,
      step (State f (Sexit (S n)) (Kblock k) sp e m)
        E0 (State f (Sexit n) k sp e m)

  | step_switch: forall f islong a cases default k sp e m v n,
      eval_expr ge sp e m a v ->
      switch_argument islong v n ->
      step (State f (Sswitch islong a cases default) k sp e m)
        E0 (State f (Sexit (switch_target n default cases)) k sp e m)

  | step_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k sp e m v m',
      eval_expr ge (Vptr sp Ptrofs.zero) e m a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn (Some a)) k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate v (call_cont k) m')

  | step_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k (Vptr sp Ptrofs.zero) e m')
  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')

  | step_return: forall v optid f sp e k m,
      step (Returnstate v (Kcall optid f sp e k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m).

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p (Callstate f nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

(** The corresponding small-step semantics. *)

Definition semantics (p: program) :=
  Smallstep.Semantics step (initial_state p) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program), Smallstep.receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (State f Sskip k sp (set_optvar optid vres2 e) m2). econstructor; eauto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate vres2 k m2). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try lia; eapply external_call_trace_length; eauto.
Qed.

(** This semantics is determinate. *)

Lemma eval_expr_determ:
  forall ge sp e m a v, eval_expr ge sp e m a v ->
  forall v', eval_expr ge sp e m a v' -> v' = v.
Proof.
  induction 1; intros v' E'; inv E'.
- congruence.
- congruence.
- assert (v0 = v1) by eauto. congruence.
- assert (v0 = v1) by eauto. assert (v3 = v2) by eauto. congruence.
- assert (vaddr0 = vaddr) by eauto. congruence.
Qed.

Lemma eval_exprlist_determ:
  forall ge sp e m al vl, eval_exprlist ge sp e m al vl ->
  forall vl', eval_exprlist ge sp e m al vl' -> vl' = vl.
Proof.
  induction 1; intros vl' E'; inv E'.
  - auto.
  - f_equal; eauto using eval_expr_determ.
Qed.

Ltac Determ :=
  try congruence;
  match goal with
  | [ |- match_traces _ E0 E0 /\ (_ -> _) ]  =>
          split; [constructor|intros _; Determ]
  | [ H: is_call_cont ?k |- _ ] =>
          contradiction || (clear H; Determ)
  | [ H1: eval_expr _ _ _ _ ?a ?v1, H2: eval_expr _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply eval_expr_determ; eauto);
          clear H1 H2; Determ
  | [ H1: eval_exprlist _ _ _ _ ?a ?v1, H2: eval_exprlist _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply eval_exprlist_determ; eauto);
          clear H1 H2; Determ
  | _ => idtac
  end.

Lemma semantics_single_events:
  forall (p: program), single_events (semantics p).
Proof.
  red; simpl. destruct 1; simpl; try lia;
  eapply external_call_trace_length; eauto.
Qed.

Lemma semantics_determinate:
  forall (p: program), Smallstep.determinate (semantics p).
Proof.
  intros. constructor; set (ge := Genv.globalenv p); simpl; intros.
- (* determ *)
  inv H; inv H0; Determ.
  + subst vargs0. exploit external_call_determ. eexact H2. eexact H13.
    intros (A & B). split; intros; auto.
    apply B in H; destruct H; congruence.
  + subst v0. assert (b0 = b) by (inv H2; inv H13; auto). subst b0; auto.
  + assert (n0 = n) by (inv H2; inv H14; auto). subst n0; auto.
  + exploit external_call_determ. eexact H1. eexact H7.
    intros (A & B). split; intros; auto.
    apply B in H; destruct H; congruence.
- (* single event *)
  apply semantics_single_events.
- (* initial states *)
  inv H; inv H0. unfold ge0, ge1 in *. congruence.
- (* nostep final state *)
  red; intros; red; intros. inv H; inv H0.
- (* final states *)
  inv H; inv H0; auto.
Qed.

Definition beh_semantics (p: program) :=
  Build_SmallstepBehSem (semantics p) (semantics_determinate p).

(** * Alternate operational semantics (big-step) *)

(** We now define another semantics for CminLoop that follows
  the ``big-step'' style of semantics, also known as natural semantics.
  In this style, just like expressions evaluate to values,
  statements evaluate to``outcomes'' indicating how execution should
  proceed afterwards. *)

Inductive outcome: Type :=
  | Out_partial: outcome
  | Out_normal: outcome                (**r continue in sequence *)
  | Out_exit: nat -> outcome           (**r terminate [n+1] enclosing blocks *)
  | Out_return: option val -> outcome  (**r return immediately to caller *)
  | Out_tailcall_return: val -> outcome. (**r already returned to caller via a tailcall *)

Definition outcome_eq_dec: forall (o1 o2: outcome),
  {o1 = o2} + {o1 <> o2}.
Proof.
  pose proof Val.eq. repeat decide equality.
Qed.

Definition outcome_block (out: outcome) : outcome :=
  match out with
  | Out_exit O => Out_normal
  | Out_exit (S n) => Out_exit n
  | out => out
  end.

Definition outcome_funcall (out: outcome) : outcome :=
  match out with
  | Out_partial => Out_partial
  | _ => Out_normal
  end.

Definition outcome_result_value
    (out: outcome) (vres: val) : Prop :=
  match out with
  | Out_partial => True
  | Out_normal => vres = Vundef
  | Out_return None => vres = Vundef
  | Out_return (Some v) => vres = v
  | Out_tailcall_return v => vres = v
  | _ => False
  end.

Definition outcome_free_mem
    (out: outcome) (m: mem) (sp: block) (sz: Z) (m': mem) :=
  match out with
  | Out_partial => True
  | Out_tailcall_return _ => m' = m
  | _ => Mem.free m sp 0 sz = Some m'
  end.

Inductive tailcall_return_out: outcome -> outcome -> val -> Prop :=
  | tro_partial: forall vres, tailcall_return_out Out_partial Out_partial vres
  | tro_tailcall: forall vres, tailcall_return_out Out_normal (Out_tailcall_return vres) vres.

Inductive outcome_optvar (optid: option ident) (vres: val) (e1 e2: env): outcome -> Prop :=
  | normal_optvar: e2 = set_optvar optid vres e1 -> outcome_optvar optid vres e1 e2 Out_normal
  | partial_optvar: outcome_optvar optid vres e1 e2 Out_partial.

Section NATURALSEM.

Variable ge: genv.

(** Full or partial evaluation of a function invocation:
  - [eval_funcall ge m f args t m' res Full]
    means that the function [f], applied to the arguments [args] in
    memory state [m], returns the value [res] in modified memory state [m'].
    [t] is the trace of observable events generated during the invocation.
  - [eval_funcall ge m f args t m' res Partial]
    means that the function [f], applied to the arguments [args] in
    memory state [m], generates the trace [t] during partial execution.
    [res] and [m'] are arbitrary in this case.
*)

Inductive eval_funcall:
        mem -> fundef -> list val -> trace ->
        mem -> val -> outcome -> Prop :=
  | eval_partial_E0:
      forall m1 m2 f vargs vres,
      eval_funcall m1 f vargs E0 m2 vres Out_partial
  | eval_funcall_internal:
      forall m f vargs m1 sp e t e2 m2 out vres m3,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      exec_stmt f (Vptr sp Ptrofs.zero) e m1 f.(fn_body) t e2 m2 out ->
      outcome_result_value out vres ->
      outcome_free_mem out m2 sp f.(fn_stackspace) m3 ->
      eval_funcall m (Internal f) vargs t m3 vres (outcome_funcall out)
  | eval_funcall_external:
      forall ef m args t res m',
      external_call ef ge args m t res m' ->
      eval_funcall m (External ef) args t m' res Out_normal
  | eval_funcall_external_partial:
      forall ef m args t res m' m'' res',
      external_call ef ge args m t res m' ->
      eval_funcall m (External ef) args t m'' res' Out_partial

(** Full or partial execution of a statement:
  - [exec_stmt ge f sp e m s t e' m' out Full]
    means that statement [s] executes with outcome [out].
    [e] is the initial environment and [m] is the initial memory state.
    [e'] is the final environment, reflecting variable assignments performed
    by [s].  [m'] is the final memory state, reflecting memory stores
    performed by [s].  [t] is the trace of I/O events performed during
    the execution.  The other parameters are as in [eval_expr].
  - [exec_stmt ge f sp e m s t e' m' out Partial]
    means that the trace [t] is emitted during partial execution
    of statement [s]. [e'], [m'] and [out] are arbitrary in this case. *)

with exec_stmt:
         function -> val ->
         env -> mem -> stmt -> trace ->
         env -> mem -> outcome -> Prop :=
  | exec_partial_E0:
      forall f sp e1 m1 e2 m2 s,
      exec_stmt f sp e1 m1 s E0 e2 m2 Out_partial
  | exec_Sskip:
      forall f sp e m,
      exec_stmt f sp e m Sskip E0 e m Out_normal
  | exec_Sassign:
      forall f sp e m id a v,
      eval_expr ge sp e m a v ->
      exec_stmt f sp e m (Sassign id a) E0 (PTree.set id v e) m Out_normal
  | exec_Sstore:
      forall f sp e m chunk addr a vaddr v m',
      eval_expr ge sp e m addr vaddr ->
      eval_expr ge sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      exec_stmt f sp e m (Sstore chunk addr a) E0 e m' Out_normal
  | exec_Scall:
      forall f sp e m optid sig a bl vf vargs fd t m' vres e' out,
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      eval_funcall m fd vargs t m' vres out ->
      outcome_optvar optid vres e e' out ->
      exec_stmt f sp e m (Scall optid sig a bl) t e' m' out
  | exec_Sbuiltin:
      forall f sp e m optid ef bl t m' vargs vres e',
      eval_exprlist ge sp e m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      e' = set_optvar optid vres e ->
      exec_stmt f sp e m (Sbuiltin optid ef bl) t e' m' Out_normal
  | exec_Sbuiltin_partial:
      forall f sp e m optid ef bl t m' vargs vres e' e'' m'',
      eval_exprlist ge sp e m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      e' = set_optvar optid vres e ->
      exec_stmt f sp e m (Sbuiltin optid ef bl) t e'' m'' Out_partial
  | exec_Sifthenelse:
      forall f sp e m a s1 s2 v b t e' m' out,
      eval_expr ge sp e m a v ->
      Val.bool_of_val v b ->
      exec_stmt f sp e m (if b then s1 else s2) t e' m' out ->
      exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out
  | exec_Sseq_continue:
      forall f sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out,
      exec_stmt f sp e m s1 t1 e1 m1 Out_normal ->
      exec_stmt f sp e1 m1 s2 t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt f sp e m (Sseq s1 s2) t e2 m2 out
  | exec_Sseq_stop:
      forall f sp e m t s1 s2 e1 m1 out,
      exec_stmt f sp e m s1 t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt f sp e m (Sseq s1 s2) t e1 m1 out
  | exec_Sloop_loop:
      forall f sp e m s t t1 e1 m1 t2 e2 m2 out,
      exec_stmt f sp e m s t1 e1 m1 Out_normal ->
      exec_stmt f sp e1 m1 (Sloop s) t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt f sp e m (Sloop s) t e2 m2 out
  | exec_Sloop_stop:
      forall f sp e m t s e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt f sp e m (Sloop s) t e1 m1 out
  | exec_Sblock:
      forall f sp e m s t e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out ->
      exec_stmt f sp e m (Sblock s) t e1 m1 (outcome_block out)
  | exec_Sdummy:
      forall f sp e m s t e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out ->
      exec_stmt f sp e m (Sdummy s) t e1 m1 out
  | exec_Sexit:
      forall f sp e m n,
      exec_stmt f sp e m (Sexit n) E0 e m (Out_exit n)
  | exec_Sswitch:
      forall f sp e m islong a cases default v n,
      eval_expr ge sp e m a v ->
      switch_argument islong v n ->
      exec_stmt f sp e m (Sswitch islong a cases default)
                E0 e m (Out_exit (switch_target n default cases))
  | exec_Sreturn_none:
      forall f sp e m,
      exec_stmt f sp e m (Sreturn None) E0 e m (Out_return None)
  | exec_Sreturn_some:
      forall f sp e m a v,
      eval_expr ge sp e m a v ->
      exec_stmt f sp e m (Sreturn (Some a)) E0 e m (Out_return (Some v))
  | exec_Stailcall:
      forall f sp e m sig a bl vf vargs fd t m' m'' vres out out' e',
      eval_expr ge (Vptr sp Ptrofs.zero) e m a vf ->
      eval_exprlist ge (Vptr sp Ptrofs.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      eval_funcall m' fd vargs t m'' vres out ->
      tailcall_return_out out out' vres ->
      (out = Out_partial \/ e = e') ->
      exec_stmt f (Vptr sp Ptrofs.zero) e m (Stailcall sig a bl) t e' m'' out'.

Scheme eval_funcall_ind2 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind2 := Minimality for exec_stmt Sort Prop.
Combined Scheme eval_funcall_exec_stmt_ind2
  from eval_funcall_ind2, exec_stmt_ind2.

Lemma eval_funcall_outcomes:
  forall m1 fd args t m2 res out,
    eval_funcall m1 fd args t m2 res out ->
    out = Out_normal \/ out = Out_partial.
Proof.
  intros. inv H; auto; destruct out0; auto.
Qed.

Lemma implies_partial_strong:
  (forall m1 fd args t m2 res out,
    eval_funcall m1 fd args t m2 res out ->
    forall m2 res, eval_funcall m1 fd args t m2 res Out_partial) /\
  (forall f sp e1 m1 s t e2 m2 out,
    exec_stmt f sp e1 m1 s t e2 m2 out ->
    forall e2 m2, exec_stmt f sp e1 m1 s t e2 m2 Out_partial).
Proof.
  apply eval_funcall_exec_stmt_ind2; intros; try (econstructor; eauto; fail).
  * replace Out_partial with (outcome_funcall Out_partial) by auto. econstructor; eauto; constructor.
  * econstructor; eauto. replace Out_partial with (outcome_funcall Out_partial) by auto. econstructor; eauto.
  * constructor; auto. congruence.
  * constructor; auto. congruence.
  * replace Out_partial with (outcome_block Out_partial) by auto; econstructor; auto.
  * econstructor; eauto. constructor.
  Unshelve. all: eauto.
Qed.

Lemma implies_partial:
  (forall m1 fd args t m2 res out,
    eval_funcall m1 fd args t m2 res out ->
    eval_funcall m1 fd args t m2 res Out_partial) /\
  (forall f sp e1 m1 s t e2 m2 out,
    exec_stmt f sp e1 m1 s t e2 m2 out ->
    exec_stmt f sp e1 m1 s t e2 m2 Out_partial).
Proof.
  split; intros; eapply implies_partial_strong; eauto.
Qed.

(** Coinductive semantics for divergence.
  [evalinf_funcall ge m f args n t]
  means that the function [f] diverges when applied to the arguments [args] in
  memory state [m]. The trace [t] is the trace of observable events
  generated during the invocation. The counter [n] enforces
  all events of [t] to actually be emitted.
*)

CoInductive evalinf_funcall:
        mem -> fundef -> list val -> Z -> tracex -> Prop :=
  | evalinf_funcall_internal:
      forall m f vargs m1 sp e n t,
      silent_guard t n ->
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      execinf_stmt f (Vptr sp Ptrofs.zero) e m1 f.(fn_body) (n-1) t ->
      evalinf_funcall m (Internal f) vargs n t

(** [execinf_stmt ge sp e m s n t] means that statement [s] diverges.
  [e] is the initial environment, [m] is the initial memory state,
  and [t] the trace of observable events performed during the execution.
  [n] is a counter that enforces all events of [t] to actually be emitted. *)

with execinf_stmt:
         function -> val -> env -> mem -> stmt -> Z -> tracex -> Prop :=
  | execinf_Scall:
      forall f sp e m optid sig a bl vf vargs fd n t,
      silent_guard t n ->
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      evalinf_funcall m fd vargs (n-1) t ->
      execinf_stmt f sp e m (Scall optid sig a bl) n t
  | execinf_Sifthenelse:
      forall f sp e m a s1 s2 v b n t,
      silent_guard t n ->
      eval_expr ge sp e m a v ->
      Val.bool_of_val v b ->
      execinf_stmt f sp e m (if b then s1 else s2) (n-1) t ->
      execinf_stmt f sp e m (Sifthenelse a s1 s2) n t
  | execinf_Sseq_1:
      forall f sp e m t s1 s2 n,
      silent_guard t n ->
      execinf_stmt f sp e m s1 (n-1) t ->
      execinf_stmt f sp e m (Sseq s1 s2) n t
  | execinf_Sseq_2:
      forall f sp e m t t1 t2 s1 e1 m1 s2 n M,
      event_guard t n t1 M ->
      exec_stmt f sp e m s1 t1 e1 m1 Out_normal ->
      execinf_stmt f sp e1 m1 s2 M t2 ->
      t = t1 °° t2 ->
      execinf_stmt f sp e m (Sseq s1 s2) n t
  | execinf_Sloop_body:
      forall f sp e m s n t,
      silent_guard t n ->
      execinf_stmt f sp e m s (n-1) t ->
      execinf_stmt f sp e m (Sloop s) n t
  | execinf_Sloop_loop:
      forall f sp e m s t t1 t2 e1 m1 n M,
      event_guard t n t1 M ->
      exec_stmt f sp e m s t1 e1 m1 Out_normal ->
      execinf_stmt f sp e1 m1 (Sloop s) M t2 ->
            t = t1 °° t2 ->
      execinf_stmt f sp e m (Sloop s) n t
  | execinf_Sblock:
      forall f sp e m s n t,
      silent_guard t n ->
      execinf_stmt f sp e m s (n-1) t ->
      execinf_stmt f sp e m (Sblock s) n t
  | execinf_Sdummy:
      forall f sp e m s n t,
      silent_guard t n ->
      execinf_stmt f sp e m s (n-1) t ->
      execinf_stmt f sp e m (Sdummy s) n t
  | execinf_Stailcall:
      forall f sp e m sig a bl vf vargs fd m' t n,
      silent_guard t n ->
      eval_expr ge (Vptr sp Ptrofs.zero) e m a vf ->
      eval_exprlist ge (Vptr sp Ptrofs.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      evalinf_funcall m' fd vargs (n-1) t ->
      execinf_stmt f (Vptr sp Ptrofs.zero) e m (Stailcall sig a bl) n t.

Lemma execinf_guard: forall f sp e m s n t,
  execinf_stmt f sp e m s n t ->
  silent_guard t n.
Proof.
  intros. inv H; auto. eapply event_to_silent; eauto. eapply event_to_silent; eauto.
Qed.

Lemma evalinf_guard: forall m f vargs n t,
  evalinf_funcall m f vargs n t ->
  silent_guard t n.
Proof.
  intros. inv H; auto.
Qed.

Lemma execinf_X0_irrel: forall f sp e m s n1 n2,
  execinf_stmt f sp e m s n1 X0 ->
  execinf_stmt f sp e m s n2 X0.
Proof.
  cofix CIH. intros.
  assert (forall m fd vargs n1 n2,
    evalinf_funcall m fd vargs n1 X0 ->
    evalinf_funcall m fd vargs n2 X0).
  cofix CIH_FUN. intros. inv H0. econstructor; eauto. now left.
  inv H.
  all: try (econstructor; eauto; now left).
Qed.

Lemma evalinf_X0_irrel: forall m fd vargs n1 n2,
  evalinf_funcall m fd vargs n1 X0 ->
  evalinf_funcall m fd vargs n2 X0.
Proof.
  intros. inv H. eapply execinf_X0_irrel in H3. econstructor; eauto. now left.
Qed.

Lemma execinf_mon: forall f sp e m s n1 n2 t,
  n1 <= n2 ->
  execinf_stmt f sp e m s n1 t ->
  execinf_stmt f sp e m s n2 t.
Proof.
  cofix CIH. intros.
  assert (forall m fd vargs n1 n2 t,
    n1 <= n2 ->
    evalinf_funcall m fd vargs n1 t ->
    evalinf_funcall m fd vargs n2 t).
  cofix CIH_FUN. intros. inv H2. econstructor; eauto. eapply guard_incr; eauto. eapply CIH; eauto. lia.
  inv H0.
  all: try (econstructor; eauto; [ eapply guard_incr; eauto | eapply CIH; eauto; lia ]).
  * econstructor; eauto. eapply guard_incr; eauto. eapply H1; eauto. lia.
  * eapply execinf_Sseq_2; eauto. eapply event_incr_left; eauto.
  * eapply execinf_Sloop_loop; eauto. eapply event_incr_left; eauto.
  * econstructor; eauto. eapply guard_incr; eauto. eapply H1; eauto. lia.
Qed.

Lemma evalinf_mon: forall m fd vargs n1 n2 t,
  n1 <= n2 ->
  evalinf_funcall m fd vargs n1 t ->
  evalinf_funcall m fd vargs n2 t.
Proof.
  cofix CIH_FUN.
  assert (forall f sp e m s n1 n2 t,
    n1 <= n2 ->
    execinf_stmt f sp e m s n1 t ->
    execinf_stmt f sp e m s n2 t).
  cofix CIH_STMT. intros. inv H0.
  all: try (econstructor; eauto; [ eapply guard_incr; eauto | eapply CIH_STMT; eauto; lia ]).
  * econstructor; eauto. eapply guard_incr; eauto. eapply CIH_FUN; eauto. lia.
  * eapply execinf_Sseq_2; eauto. eapply event_incr_left; eauto.
  * eapply execinf_Sloop_loop; eauto. eapply event_incr_left; eauto.
  * econstructor; eauto. eapply guard_incr; eauto. eapply CIH_FUN; eauto. lia.
  * intros. inv H1. econstructor; eauto. eapply guard_incr; eauto. eapply H; eauto. lia.
Defined.

End NATURALSEM.

(** Big-step execution of a whole program *)

Inductive bigstep_initial_state (p: program): mem -> fundef -> Prop :=
  | bigstep_intro:
    forall b m f,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    funsig f = signature_main ->
    bigstep_initial_state p m f.

Inductive bigstep_program_terminates (p: program): trace -> int -> Prop :=
  | bigstep_program_terminates_intro:
      forall f m0 m t r,
      let ge := Genv.globalenv p in
      bigstep_initial_state p m0 f ->
      eval_funcall ge m0 f nil t m (Vint r) Out_normal ->
      bigstep_program_terminates p t r.

Inductive bigstep_program_forever (p: program): tracex -> Prop :=
  | bigstep_program_diverges_intro:
      forall f m t N,
      let ge := Genv.globalenv p in
      bigstep_initial_state p m f ->
      evalinf_funcall ge m f nil N t ->
      bigstep_program_forever p t.

Inductive bigstep_program_partial (p: program): trace -> Prop :=
  | bigstep_program_partial_intro:
      forall f m0 m t r,
      let ge := Genv.globalenv p in
      bigstep_initial_state p m0 f ->
      eval_funcall ge m0 f nil t m r Out_partial ->
      bigstep_program_partial p t
  | bigstep_program_no_initial_state:
      (~ exists f m, bigstep_initial_state p m f) ->
      bigstep_program_partial p E0.

Definition bigstep_semantics (p: program) :=
  Bigstep.Semantics (bigstep_program_terminates p) (bigstep_program_forever p) (bigstep_program_partial p) (Genv.globalenv p).

Lemma bigstep_nonempty: forall p, bigstep_program_partial p E0.
Proof.
  intros. destruct (classic (exists f m, bigstep_initial_state p m f)) as [[f [m]]|].
  * econstructor; eauto. constructor.
  * now constructor.
  Unshelve. exact m. exact Vundef.
Qed.