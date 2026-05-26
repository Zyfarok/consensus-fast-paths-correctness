# Consensus fast-paths correctness in Rocq

The end-goal of this project is to prove the that the fast-path of consensus protocols like FastPaxos, EPaxos and SwiftPaxos are safe and recoverable.
By recoverable, we mean that if one process commited, enough evidence should exist at any subset of `n - f` processes to allow other processes to adopt safely (in a system of `n` processes with up to `f` failures).

To represent the fast-paths, we use the adopt-commit abstraction.
However, we do not attempt to prove liveness properties, and we will not implement the recovery procedure (adoption) of these protocols. Though, we note that the recovery property implies that one could derive a recovery protocol that ensures liveness while preserving safety (i.e. that we can always adopt something safe).

In `AdoptCommit.v` we model the adopt-commit abstraction and the arbitrary executions allowed by asynchronous networks.

In `FastPaxos.v`, we instantiate the model with the fast-path of Fast-Paxos and prove its safety and recoverability.