(** * FastPaxos Fast-Path Adopt-Commit
    This file instantiates the abstract adopt-commit framework from
    AdoptCommit.v with the fast path of FastPaxos (Lamport, 2006).

    Fast path overview:
    - Each proposer p broadcasts Proposal(p, p) to all other processes.
      This broadcast is part of the initial state rather than a step, since our
      step model only covers message delivery. A proposer also pre-accepts its
      own value (with itself as the sole acceptor).
    - When a process receives Proposal(sender, proposer) and has not yet
      accepted any value, it accepts proposer's value and replies to proposer
      with Proposal(self, proposer).
    - When a process has already accepted value v and receives Proposal(sender, v),
      it records sender as a new acceptor of v and commits once fp_quorum
      acceptors have been collected (counting itself).
    - Messages about a proposer other than the one already accepted are ignored. *)

From Stdlib Require Import List Arith Bool Classical.
Import ListNotations.

Require Import AdoptCommit.

(* ================================================================
   Messages and Local State
   ================================================================ *)

(* Messages can encode either a proposer's request to accept, 
   or the confirmation that a process accepted. *)
Record FPMsg := mkFPMsg {
  source   : ProcessId; (* sender of the message *)
  proposer : ProcessId; (* Value the source accepted. *)
}.

Record FPState := mkFPState {
  fp_accepted  : option ProcessId;   (* proposer whose value we have accepted *)
  fp_acceptors : list ProcessId;     (* processes that acknowledged our accepted value back to us *)
  fp_output    : option ACOutput;
}.

(* ================================================================
   Protocol Instantiation
   ================================================================ *)

Section FP.

Variable n : nat.
Hypothesis n_pos : 0 < n.
Variable f : nat.
Hypothesis f_lt_n : f < n.

Variable is_proposer : ProcessId -> Prop.
Hypothesis exists_proposer : exists p, p < n /\ is_proposer p.

(** Quorum size: If n=2f+1, the quorum size if floor(3n/4)+1.
    We need to make sure that if f processes fail, the remainder
    of the quorum is still a strict majority: (n-f)/2 + 1 *)
Definition fp_quorum : nat := f + (n - f) / 2 + 1.

(** Local transition function.
    When process p receives Proposal(sender, proposer):
    - If already decided, the message is ignored.
    - If p has not accepted any value yet, p accepts proposer's value and
      replies Proposal(p, proposer) to proposer.
    - If p already accepted value v:
        - proposer = v: record sender as a new acceptor; commit if fp_quorum
          acceptors have been collected.
        - proposer != v: ignore. *)
Definition fp_step_fn
    (p : ProcessId) (ls : FPState) (m : FPMsg)
    : FPState * (ProcessId -> list FPMsg) :=
  match fp_output ls with
  | Some _ => (ls, fun _ => [])
  | None => match fp_accepted ls with
      | None =>
          (mkFPState (Some (proposer m)) [] None,
            fun dst => if Nat.eqb dst (proposer m) then [mkFPMsg p (proposer m)] else [])
      | Some v =>
          if Nat.eqb (proposer m) v then
            let new_acceptors :=
              if existsb (Nat.eqb (source m)) (fp_acceptors ls)
              then fp_acceptors ls
              else (source m) :: fp_acceptors ls
            in
            let new_output :=
              if fp_quorum <=? List.length new_acceptors then Some (Commit v)
              else None
            in
            (mkFPState (Some v) new_acceptors new_output, fun _ => [])
          else
            (ls, fun _ => [])
      end
  end.

(** Initial state predicate.
    - All processes start undecided.
    - Each proposer p has accepted its own value and lists itself as the
      sole acceptor (a proposer cannot receive its own broadcast, since
      our step relation requires src != p).
    - Non-proposers start with no accepted value and no acceptors.
    - Each proposer p has queued Proposal(p, p) to every other process q.
    - Non-proposers have no outgoing messages. *)
Definition fp_init (s : GlobalState FPMsg FPState) : Prop :=
  ((forall p, p < n ->
      fp_output (local s p) = None) /\
  ((forall p, p < n -> is_proposer p ->
      fp_accepted  (local s p) = Some p) /\
  (forall p, p < n -> ~ is_proposer p ->
      fp_accepted  (local s p) = None)) /\
  ((forall p, p < n -> is_proposer p ->
      fp_acceptors (local s p) = [p]) /\
  (forall p, p < n -> ~ is_proposer p ->
      fp_acceptors (local s p) = []))) /\
  (((forall p q, p < n -> q < n -> p <> q -> is_proposer p ->
      network s p q = [mkFPMsg p p]) /\
  (forall p q, p < n -> q < n -> ~ is_proposer p ->
      network s p q = [])) /\
  (forall p, p < n -> network s p p = [])).

(** Bundle of all protocol-specific parameters for this instantiation. *)
Definition fp_instance : ACProtocol :=
  mkACProtocol fp_output is_proposer fp_init fp_step_fn.

(* ================================================================
   Shorthands for the Instantiated Definitions
   ================================================================ *)

Definition FP_GlobalState := GlobalState FPMsg FPState.
Definition FP_Reachable   := Reachable n fp_instance.

(* ================================================================
   Proofs
   ================================================================ *)

(** fp_step_fn never discards an existing output. *)
Lemma fp_step_fn_output_stable :
  forall p ls m o,
    fp_output ls = Some o ->
    fp_output (fst (fp_step_fn p ls m)) = Some o.
Proof.
  intros p ls m o H.
  unfold fp_step_fn. rewrite H. simpl. exact H.
Qed.

Lemma all_message_values_valid :
  forall s,
    FP_Reachable s ->
    (forall src dest,
      src < n -> dest < n -> Forall (fun msg => is_proposer (proposer msg)) (network s src dest)).
Proof.
  intros s Hs. induction Hs; simpl in H.
  - (* init-case: only proposers have sent messages with their own value. *)
    unfold fp_init in H; destruct H as [_ [[init_net_prop init_net_nonprop] init_net_self]].
    intros src dest src_valid dest_valid. destruct (classic (is_proposer src)) as [Hprop | Hprop].
    + destruct (classic (src = dest)) as [Heq | Hneq].
      * (* no messages are sent to self *)
        destruct Heq. rewrite (init_net_self src src_valid). constructor.
      * (* proposer sending to others *)
        rewrite (init_net_prop src dest src_valid dest_valid Hneq Hprop). constructor; auto.
    + (* non-proposers send nothing initially *)
      rewrite (init_net_nonprop src dest src_valid dest_valid Hprop). constructor; auto.
  - (* step-case: try to dequeue a message and potentially send new ones *)
    intros src0 dest. unfold step, fp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p_valid]] H]. destruct (network s src p) eqn:src_net.
    + (* empty queue: nothing was done. *)
      unfold state_eq in H. destruct H as [state_eq net_eq].
      rewrite net_eq. auto.
    + destruct H as [_ [H_net_p_in [H_net_p_out H_net_other]]].
      intros src0_valid dest_valid.
      destruct (classic (src = src0)).
      * destruct H. destruct (classic (dest = p)).
        -- (* Queue from which p consumed the message. *)
          destruct H.
          pose (IHHs src dest src0_valid dest_valid) as H.
          rewrite src_net in H.
          apply Forall_inv_tail in H.
          destruct H_net_p_in. auto.
        -- (* Other queues from the same source: unchanged. *)
          rewrite H_net_other; auto.
      * destruct (classic (p = src0)).
        -- (* p's outgoing queues: gained the replies from fp_step_fn. *)
          destruct H0.
          rewrite H_net_p_out.
          apply Forall_app. split.
          ++ (* Pre-existing messages: valid by IHHs. *)
            auto.
          ++ (* New messages emitted by fp_step_fn: *)
            unfold fp_step_fn.
            destruct (fp_output (local s p)); auto. (* output already set: no new messages *)
            destruct (fp_accepted (local s p)).
            ** (* Already accepted: no new messages (or sends nothing new). *)
              destruct (proposer f0 =? p0); simpl; auto.
            ** (* Not yet accepted: sends replies to proposer (with same value). *)
              simpl. destruct (dest =? proposer f0); auto.
              rewrite Forall_cons_iff; split; auto.
              simpl.
              pose (IHHs src p src_valid p_valid) as Hmsg.
              rewrite src_net in Hmsg.
              apply Forall_inv in Hmsg.
              apply Hmsg.
        -- (* All the other queues: unchanged. *)
          rewrite H_net_other; auto.
Qed.

Lemma all_accepted_values_valid :
  forall s,
    FP_Reachable s -> 
    (forall p, p < n -> match fp_accepted (local s p) with
        | None => True
        | Some(value) => is_proposer value
      end).
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - unfold fp_init in H; destruct H as [[_ [[prop_acc nonprop_acc] _]] _].
    destruct (classic (is_proposer p)) as [prop | not_prop].
    + rewrite (prop_acc p p_valid prop). auto.
    + rewrite (nonprop_acc p p_valid not_prop). auto.
  - unfold step, fp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H]. destruct (network s src p0) eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * destruct H. rewrite p0_state.
        unfold fp_step_fn.
        destruct (fp_output (local s p)); auto.
        destruct (fp_accepted (local s p)) eqn:prev_acc.
        -- (* already accepted value before: Use IHHs *)
          destruct (Nat.eqb (proposer f0) p0); simpl.
          ++ exact IHHs.
          ++ rewrite prev_acc. exact IHHs.      
        -- (* will accept the message's value. *)
          simpl.
          pose proof (all_message_values_valid s Hs src p src_valid p_valid) as Hmsg.
          rewrite src_net in Hmsg.
          exact (Forall_inv Hmsg).
      * (* p != p0: other processes local state are unchanged *)
        rewrite (other_state p H).
        exact IHHs.
Qed.

Lemma all_outputs_valid :
  forall s,
    FP_Reachable s ->
    forall p, p < n ->
      match fp_output (local s p) with
      | None => True
      | Some (Commit v) => is_proposer v
      | Some (Adopt v) => is_proposer v
      end.
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - (* Init: all outputs are None. *)
    unfold fp_init in H. destruct H as [[init_noout _] _].
    rewrite (init_noout p p_valid). auto.
  - (* Step: p0 receives the head message f0 from src. *)
    unfold step, fp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + (* Empty queue: no message delivered, local states unchanged. *)
      unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * (* p = p0: p's local state was updated by fp_step_fn. *)
        destruct H. rewrite p0_state.
        destruct (fp_output (local s p)) as [o|] eqn:prev_out.
        -- (* Output already set: fp_step_fn leaves local state unchanged. *)
           rewrite (fp_step_fn_output_stable p (local s p) f0 o prev_out).
           exact IHHs.
        -- (* No output yet: inspect accepted value. *)
           unfold fp_step_fn. rewrite prev_out.
           destruct (fp_accepted (local s p)) as [v|] eqn:prev_acc.
           ++ destruct (Nat.eqb (proposer f0) v).
              ** (* Accepted value matches: might commit. *)
                 simpl.
                 pose proof (all_accepted_values_valid s Hs p p_valid) as Hacc.
                 rewrite prev_acc in Hacc.
                 destruct (fp_quorum <=? _); auto.
              ** (* Accepted value does not match: state unchanged. *)
                 simpl. rewrite prev_out. auto.
           ++ (* Not yet accepted: will accept proposer f0, output stays None. *)
              simpl. auto.
      * (* p != p0: p's local state is unchanged. *)
        rewrite (other_state p H).
        exact IHHs.
Qed.

Lemma fp_acceptors_nodup :
  forall s,
    FP_Reachable s ->
    forall p, p < n -> NoDup (fp_acceptors (local s p)).
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - (* Init *)
    unfold fp_init in H. destruct H as [[_ [_ [init_prop_acc init_nonprop_acc]]] _].
    destruct (classic (is_proposer p)) as [Hprop | Hprop].
    + (* Proposers. *)
      rewrite (init_prop_acc p p_valid Hprop).
      apply NoDup_cons; [intro Hin; exact Hin | constructor].
    + (* Non-proposers. *)
      rewrite (init_nonprop_acc p p_valid Hprop). constructor.
  - (* Step *)
    unfold step, fp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + (* No message delivered. *)
      unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * (* state of the running process. *)
        destruct H. rewrite p0_state. unfold fp_step_fn.
        destruct (fp_output (local s p)).
        -- (* Output already set. *)
           simpl. exact IHHs.
        -- destruct (fp_accepted (local s p)) eqn:prev_acc.
          ++ destruct (Nat.eqb (proposer f0) p0).
            ** (* Proposer matches. *)
              simpl.
              destruct (existsb (Nat.eqb (source f0)) (fp_acceptors (local s p))) eqn:Hexists; try exact IHHs.
              apply NoDup_cons; try exact IHHs.
              intro Hin.
              assert (existsb (Nat.eqb (source f0)) (fp_acceptors (local s p)) = true)
                as Hcontra
                by (apply existsb_exists; exists (source f0);
                    split; [exact Hin | apply Nat.eqb_refl]).
              rewrite Hexists in Hcontra. discriminate.
            ** (* Proposer doesn't match. *)
                simpl. exact IHHs.
          ++ (* Not yet accepted: new acceptors list is []. *)
            simpl. constructor.
      * (* other process states are unchanged. *)
        rewrite (other_state p H). exact IHHs.
Qed.

Theorem FastPaxos_Validity        : Validity n fp_instance.
Proof.
  unfold Validity, fp_instance, output_of, valid_pid; simpl.
  intros s p v Hs p_valid [Hout | Hout];
    pose proof (all_outputs_valid s Hs p p_valid) as Hvalid;
    rewrite Hout in Hvalid; exact Hvalid.
Qed.

Theorem FastPaxos_Agreement       : Agreement n fp_instance.
Proof. Admitted.

Theorem FastPaxos_Convergence     : Convergence n fp_instance.
Proof. Admitted.

Theorem FastPaxos_Recoverability  : Recoverability n f fp_instance.
Proof. Admitted.

End FP.
