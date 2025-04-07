Set Primitive Projections.
CoInductive Foo := B { p : bool }.

Definition f (x:=B false) (y:Foo) : Foo := cofix f := y.

Definition v := (f (B true)).(p).

Lemma v_true : v = true.
Proof. reflexivity. Qed.

(* bad! *)
Lemma v_false : v = false.
Proof. repeat step cbv. Fail reflexivity. Abort.

Lemma v_false : v = false.
Proof. repeat step cbv. Fail reflexivity. Abort.
