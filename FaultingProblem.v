Parameter Software : Type. (* Define the type of software *)

Parameter decides_bug : Software -> Prop. (* Predicate for deciding if software has bugs *)

Definition bug_existence_problem : Prop :=
  (exists s, decides_bug s) -> False.

Definition bug_existence_problem' : Prop :=
  forall s, decides_bug s -> False.

Theorem statements_equivalent_bug_existence :
  bug_existence_problem <-> bug_existence_problem'.
Proof.
  unfold bug_existence_problem, bug_existence_problem'; split; intros.
  - exact (H (ex_intro decides_bug s H0)).
  - destruct H0.
    exact (H x H0).
Qed.
