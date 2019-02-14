namespace and.rassoc
  variables P Q R: Prop
  #check P ∧ Q ∧ R
  #check P ∧ (Q ∧ R)
end and.rassoc

lemma my_and_intro{P Q: Prop}(pfP: P)(pfQ: Q): P ∧ Q :=
begin
    exact and.intro pfP pfQ
end

example: ∀{P Q: Prop}(pfPandQ: P ∧ Q),
  P :=
begin
  intros,
  exact pfPandQ.left,
  -- can use (and.elim_left pfPandQ) or
  -- pfPandQ.1 instead of pfPandQ.left
end

lemma my_and_assoc{P Q R: Prop}:
  P ∧ (Q ∧ R) = (P ∧ Q) ∧ R :=
begin
  sorry
end

lemma my_and_reflex{P: Prop}:
  P ∧ P :=
begin
  sorry
end

-- Also commutativity
lemma my_and_sym{P Q: Prop}:
  P ∧ Q = Q ∧ P :=
begin
  sorry
end

lemma my_and_trans{P Q R: Prop}:
  P ∧ Q → Q ∧ R → P ∧ R :=
begin
  sorry
end

lemma non_contradiction{P: Prop}:
  ¬(P ∧ ¬P) :=
begin
  sorry
end
