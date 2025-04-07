Record T : Type := Build_T { f : unit; g := pair f f; }.

Definition t : T := {| f := tt; |}.

Goal match t return unit with Build_T f g => f end = tt.
Proof.
  repeat step cbv.
reflexivity.
Qed.

Goal match t return prod unit unit with Build_T f g => g end = pair tt tt.
Proof.
  repeat step cbv.
reflexivity.
Qed.

Goal forall (x : T),
  match x return prod unit unit with Build_T f g => g end =
  pair match x return unit with Build_T f g => fst g end match x return unit with Build_T f g => snd g end.
Proof.
  repeat step cbv.
destruct x.
reflexivity.
Qed.

Record U : Type := Build_U { h := tt }.

Definition u : U := Build_U.

Goal match u with Build_U h => h end = tt.
Proof.
  repeat step cbv.
reflexivity.
Qed.
