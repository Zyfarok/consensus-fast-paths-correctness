(** * Authored by Clément Burgelin, 2026-05

    This file defines the generic adopt-commit that we will later instantiate,
    as well as the core properties that we want to prove.

    This work is in part inspired by Giuliano Losa's
    Abortable linearizable modules in Isabelle/HOL,
    available on the Archive of Formal Proofs website:
    https://isa-afp.org/browser_info/current/AFP/Abortable_Linearizable_Modules/
    (Which itself is part of larger work on Speculative linearizability,
    published at PLDI 2012: https://dl.acm.org/doi/abs/10.1145/2345156.2254072)

    We adopt a similar reachability-based approach to defining safety properties,
    but we focus on the adopt-commit problem rather than abortable linearizability,
    and we use Rocq rather than Isabelle/HOL.

    By Assuming that messages are never lost, duplicated or reordered (which can
    be implemented via TCP for example), we can simply model a single type
    of step: the delivery of a message by a process.
    *)

From Stdlib Require Import List.
Import ListNotations.

(** Process identifiers also serve as proposed values for simplicity:
  each proposer's value is its own ID, so two distinct proposers necessarily conflict. *)
Definition ProcessId := nat.

(** Adopt-commit output: a process either commits or adopts a value (= ProcessId). *)
Inductive ACOutput :=
  | Commit : ProcessId -> ACOutput
  | Adopt  : ProcessId -> ACOutput.

(* ================================================================
   System Model
   Protocol-specific definitions (message format, local state,
   initial condition, transition relation) are left abstract and will
   be instantiated by the concrete adopt-commit protocol.
   ================================================================ *)

Section AC.

(** Number of processes; IDs 0 .. n-1 are valid. *)
Variable n : nat.
Hypothesis n_pos : 0 < n.

(** Number of tolerated process failures. *)
Variable f : nat.
Hypothesis f_lt_n : f < n.

Definition valid_pid (p : ProcessId) : Prop := p < n.

Variable Msg        : Type.
Variable LocalState : Type.

(** Global state: per-process local state + per-(src, dst) FIFO message queues.
    [network s src dst] is the queue of messages sent by src to dst,
    head = oldest (next to deliver). *)
Record GlobalState := mkGlobalState {
  local   : ProcessId -> LocalState;
  network : ProcessId -> ProcessId -> list Msg;
}.

(** Equality on global states: two states are equivalent when
    all local states and all network queues agree pointwise. *)
Definition state_eq (s s' : GlobalState) : Prop :=
  (forall q, local s' q = local s q) /\
  (forall q_src q_dst, network s' q_src q_dst = network s q_src q_dst).

(** A protocol instance bundles the four protocol-specific parameters:
    how to extract a decision, which processes are proposers, the initial
    state predicate, and the pure local transition function. *)
Record ACProtocol := mkACProtocol {
  acp_proc_output : LocalState -> option ACOutput;
  acp_is_proposer : ProcessId -> Prop;
  acp_init        : GlobalState -> Prop;
  acp_step_fn     : ProcessId -> LocalState -> Msg ->
                    LocalState * (ProcessId -> list Msg);
}.

Variable P : ACProtocol.

Hypothesis exists_proposer :
  exists p, valid_pid p /\ acp_is_proposer P p.

(** acp_step_fn never discards an existing output decision. *)
Hypothesis step_fn_output_stable :
  forall p ls m o,
    acp_proc_output P ls = Some o ->
    acp_proc_output P (fst (acp_step_fn P p ls m)) = Some o.

(** Shorthand: output of process p in state s. *)
Definition output_of (s : GlobalState) (p : ProcessId) : option ACOutput :=
  acp_proc_output P (local s p).

(** [step p src s s'] holds when src != p and s' is the state obtained after
    p processes the next message from src.
    - If the queue is empty the step is a no-op (s' = s componentwise).
    - Otherwise p's local state is updated by acp_step_fn; the consumed slot
      (src->p) loses its head; p's outgoing queues grow by the messages
      prescribed by acp_step_fn; all other queues are unchanged. *)
Definition step (p src : ProcessId) (s s' : GlobalState) : Prop :=
  (src <> p /\ src < n /\ p < n) /\
  match network s src p with
  | [] => state_eq s s'
  | m :: rest =>
      (local s' p = fst (acp_step_fn P p (local s p) m) /\
      (forall q, q <> p -> local s' q = local s q)) /\
      network s' src p = rest /\
      (forall dst, network s' p dst = network s p dst ++ snd (acp_step_fn P p (local s p) m) dst) /\
      (forall other_src other_dst,
        other_src <> p -> (other_dst <> p \/ other_src <> src) ->
        network s' other_src other_dst = network s other_src other_dst)
  end.

(** The set of reachable global states. *)
Inductive Reachable : GlobalState -> Prop :=
  | Reach_init : forall s, acp_init P s -> Reachable s
  | Reach_step : forall p src s s',
      Reachable s -> step p src s s' -> Reachable s'.

(* ================================================================
   Adopt-Commit Safety Properties
   ================================================================ *)

(** Validity: every output has been proposed by someone (thus it must be the ID of some proposer). *)
Definition Validity : Prop :=
  forall s p v,
    Reachable s ->
    valid_pid p ->
    (output_of s p = Some (Commit v) \/ output_of s p = Some (Adopt v)) ->
    acp_is_proposer P v.

(** Agreement: if process p commits v, every terminating process q outputs v
    (whether committing or adopting). *)
Definition Agreement : Prop :=
  forall s p q v w,
    Reachable s ->
    valid_pid p -> valid_pid q ->
    output_of s p = Some (Commit v) ->
    (output_of s q = Some (Commit w) \/ output_of s q = Some (Adopt w)) ->
    w = v.

(** Convergence: with a unique proposer p, every terminating process commits p
    (adopting is not acceptable when there is no conflict). *)
Definition Convergence : Prop :=
  forall s p q o,
    Reachable s ->
    valid_pid p -> valid_pid q ->
    acp_is_proposer P p ->
    (forall p', acp_is_proposer P p' -> p' = p) ->
    output_of s q = Some o ->
    o = Commit p.

(** Recoverability: any n-f surviving processes hold enough evidence to rule out
    any committed value other than the actual one.
    Formally, no two reachable states that agree on (at least) n-f process
    local states can commit different values.
    The surviving set is represented as a duplicate-free list so that its
    cardinality is given directly by [List.length]. *)
Definition Recoverability : Prop :=
  forall s s' alive v w,
    Reachable s -> Reachable s' ->
    List.NoDup alive ->
    n - f <= List.length alive ->
    (forall p, List.In p alive -> valid_pid p) ->
    (forall p, List.In p alive -> local s p = local s' p) ->
    (exists p, output_of s p = Some (Commit v)) ->
    (exists q, output_of s' q = Some (Commit w)) ->
    v = w.

End AC.

Arguments local           {Msg LocalState}.
Arguments network         {Msg LocalState}.
Arguments ACProtocol      {Msg LocalState}.
Arguments mkACProtocol    {Msg LocalState}.
Arguments acp_proc_output {Msg LocalState}.
Arguments acp_is_proposer {Msg LocalState}.
Arguments acp_init        {Msg LocalState}.
Arguments acp_step_fn     {Msg LocalState}.
Arguments Reachable       n {Msg LocalState}.
Arguments Validity        n {Msg LocalState}.
Arguments Agreement       n {Msg LocalState}.
Arguments Convergence     n {Msg LocalState}.
Arguments Recoverability  n f {Msg LocalState}.
