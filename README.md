# Consensus fast-paths correctness in Rocq

The end-goal of this project is to prove the that the fast-path of consensus protocols like EPaxos and FastPaxos are recoverable.
By recoverable, we mean that if one process commited, enough evidence should exist at any subset of `n - f` processes to be able to adopt safely (in a system of `n` processes with up to `f` failures).

To represent the fast-paths, we use the adopt-commit abstraction.
However, we do not attempt to prove liveness properties, and we will not implement the recovery procedure of these protocols. Though, we note that the recovery property implies that one could derive a recovery protocol that ensures liveness.