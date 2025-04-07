Import Nat.
Definition option_bind [T U] (o: option T) (f: T -> option U) :=
  match o with
  | Some x => f x
  | None => None
  end.

Notation "'Let' x ':=' y 'in' z" := (option_bind y (fun x => z)) (x ident, at level 200).

Notation eval_in redt tm := (ltac:(let tm' := (eval redt in tm) in exact tm')).

Arguments option_bind [T U] !o f : simpl nomatch.

Inductive PureLambda :=
| var : nat -> PureLambda
| lambda : PureLambda -> PureLambda
| appl : PureLambda -> PureLambda -> PureLambda
.

Fixpoint lift k t :=
  match t with
  | var n => var (k + n)
  | lambda t => lambda (lift k t)
  | appl t u => appl (lift k t) (lift k u)
  end.

Fixpoint replace x k t :=
  match t with
  | var n => if n =? k then var n else lift k x
  | lambda t => lambda (replace x (k + 1) t)
  | appl t u => appl (replace x k t) (replace x k u)
  end.

(* number one, reduce until no more visible or immediately created redexes *)
Fixpoint reduce_redexes_bottom_up t :=
  match t with
  | var n => var n
  | lambda t => lambda (reduce_redexes_bottom_up t)
  | appl (lambda t) x => replace (reduce_redexes_bottom_up x) O (reduce_redexes_bottom_up t)
  | appl t x =>
    let x := reduce_redexes_bottom_up x in
    match reduce_redexes_bottom_up t with
    | lambda t => replace x O t
    | t => appl t x
    end
  end.

Fixpoint unlift t :=
  match t with
  | var O => None
  | var (S n) => Some (var n)
  | lambda t => option_map lambda (unlift t)
  | appl t u =>
    Let t := unlift t in
    option_map (appl t) (unlift u)
  end.

Fixpoint ensure_normal_form k t :=
  match t with
  | var n => if n <? k then Some (var n) else None (* open term *)
  | lambda t =>
      Let t := ensure_normal_form (k + 1) t in
      let t :=
        match t with
        | appl t' (var O) =>
          match unlift t' with
          | Some t => t (* eta reduce *)
          | None => t
          end
        | _ => t
        end
      in Some (lambda t)
  | appl t x =>
    Let t := ensure_normal_form k t in
    match t with
    | lambda _ => None (* visible redex *)
    | _ => option_map (appl t) (ensure_normal_form k x)
    end
  end.

(* call of nature, repeat bottom-up redexes *)
Fixpoint call_of_nature n t :=
  match n with
  | O => ensure_normal_form O t
  | S n => call_of_nature n (reduce_redexes_bottom_up t)
  end.

Fixpoint nat_to_term_helper n :=
  match n with
  | O => var 0
  | S n => appl (var 1) (nat_to_term_helper n)
  end.

Definition nat_to_term n := lambda (lambda (nat_to_term_helper n)).

(* \f\x f x *)
Definition one := lambda (lambda (appl (var 1) (var 0))).
(* \f\x f (f x) *)
Definition two := lambda (lambda (appl (var 1) (appl (var 1) (var 0)))).
(* \n\m\f\x (n f) (m f x) *)
Definition plus :=
  lambda (lambda (lambda (lambda (
    appl (appl (var 3) (var 1))
      (appl (appl (var 2) (var 1)) (var 0))
   ))))
.
Definition one_plus_one := appl (appl plus one) one.

Eval vm_compute in call_of_nature 2 one_plus_one.
(* = None
 "call_of_nature 3 one_plus_one" takes forever
*)

Goal call_of_nature 2 one_plus_one = Some two.
(* Your job is to debug, glhf
   You can use `change pat with (eval_in red (val))`
   and reductions such as unfold, fold, simpl, cbv, lazy, cbn, red, hnf...
*)
  (* fold does thing you may not expect *)
  unfold two.
  fold (nat_to_term_helper 2).
  fold (nat_to_term 2).
  (* delta reduction on call_of_nature? *)







































  cbv delta [call_of_nature]. Undo.
  unfold call_of_nature.
  (* Your goal is to slowly reduce ensure_normal form without exposing too much *)
  simpl ensure_normal_form. Undo.
  simpl reduce_redexes_bottom_up.
  do 3 (cbn fix delta [ensure_normal_form]; cbn match; cbn [Nat.add]).
  (* reduce first ensure normal form *)
  unfold ensure_normal_form at 1. Undo.
  Ltac step_in target :=
    (cbn fix delta [ensure_normal_form] in target; cbn match in target; cbn [Nat.add] in target).
  set (e0 := ensure_normal_form 2 _).
  do 3 step_in e0.
  set (e1 := ensure_normal_form 4 _) in e0.
  step_in e1.
  set (e2 := ensure_normal_form 4 _) in e1.
  do 3 step_in e2.
  set (e3 := ensure_normal_form 6 _) in e2.
  do 3 step_in e3.
  step_in e3.
  cbn [ltb leb option_bind] in e3.
  (* who can tell me why it appeared? *)
  Restart.
  
  unfold call_of_nature.
  cbn [reduce_redexes_bottom_up one_plus_one].
  change (reduce_redexes_bottom_up one) with one.
  change (reduce_redexes_bottom_up plus) with plus.
    unfold plus at 1.
  (* replace one 0
      (reduce_redexes_bottom_up
         (lambda
            (lambda (lambda (appl (appl (var 3) (var 1)) (appl (appl (var 2) (var 1)) (var 0)))))))
  *)
    Undo.
  set (e := match plus with lambda t => _ | _ => _ end) at 1.
  cbv delta [plus] in e.
  cbv match in e.
  (* Turns out we did not go too far *)
  cbn [reduce_redexes_bottom_up] in e.
  subst e.
    cbn [replace]. Undo.
    unfold replace at 1. Undo.
  cbn delta [replace].
  set (e := replace _ _ _).
  cbn -[one] in e.
  subst e.
  cbn match.
  (* VAR 3 ??? LIFT 3 ??? appl (lift 3 one) (lift 3 one) ??? *)
  Restart.

























  Tactic Notation "eval_in" tactic(red) open_constr(p) :=
    let tm := eval red in p in exact tm.
  Tactic Notation "red_at" tactic(red) open_constr(p) :=
  match goal with
  | [ |- context C[p as tm] ] =>
    let tm0 := eval red in tm in
    let tm1 := context C[tm0] in
    change _ with tm1
  end.
(*
  step delta at 1.
  change call_of_nature as tm with ltac:(eval_in (step delta) tm).
*)
  red_at (step delta) call_of_nature. Undo.
  unfold call_of_nature.
  red_at (step delta) one_plus_one.
  red_at (step delta) ensure_normal_form. Undo.
  red_at (step delta) (reduce_redexes_bottom_up (appl _ _)).
  red_at (step delta) reduce_redexes_bottom_up.
Abort.
