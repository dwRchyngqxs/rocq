Set Primitive Projections.
Set Implicit Arguments.
Set Nonrecursive Elimination Schemes.
Record prod A B := pair { fst : A ; snd : B }.
Definition f : Set -> Type := fun x => x.

Goal (fst (pair (fun x => x + 1) nat) 0) = 0.
repeat step cbv.
Undo.
repeat step cbv.
Undo.
Opaque fst.
repeat step cbv.
Transparent fst.
repeat step cbv.
Undo.
simpl.
Undo.
Abort.

Goal f (fst (pair nat nat)) = nat.
compute.
  match goal with
    | [ |- fst ?x = nat ] => fail 1 "compute failed"
    | [ |- nat = nat ] => idtac
  end.
  reflexivity.
Defined.

Goal fst (pair nat nat) = nat.
  unfold fst.
  match goal with
    | [ |- fst ?x = nat ] => fail 1 "compute failed"
    | [ |- nat = nat ] => idtac
  end.
  reflexivity.
Defined.

Lemma eta A B : forall x : prod A B, x = pair (fst x) (snd x). reflexivity. Qed.
