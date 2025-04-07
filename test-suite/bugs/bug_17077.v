Goal True.
Proof.
pose (T := forall A, A).
repeat step cbv in T.
(* Anomaly "the kernel does not support sort variables" *)
Abort.
