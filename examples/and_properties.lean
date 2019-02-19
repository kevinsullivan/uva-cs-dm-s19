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

lemma my_and_assoc(P Q R: Prop):
  P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R :=
begin
  split,
    assume pfPandQandR,
    have pfP := and.elim_left pfPandQandR,
    have pfQ := pfPandQandR.right.left,
    have pfPandQ := and.intro pfP pfQ,
    have pfR := pfPandQandR.right.right,
    exact and.intro pfPandQ pfR,

    assume pfPandQ_andR,
    have pfQ := (and.elim_right (and.elim_left pfPandQ_andR)),
    have pfR := pfPandQ_andR.right,
    have pfQandR := and.intro pfQ pfR,
    have pfP := pfPandQ_andR.left.left,
    exact and.intro pfP pfQandR,
end

lemma my_and_assoc'{P Q R: Prop}:
  (P ∧ (Q ∧ R)) = ((P ∧ Q) ∧ R) :=
begin
  have pfAssoc := my_and_assoc P Q R,
  rw pfAssoc,
end

lemma my_and_assoc''{P Q R: Prop}:
  (P ∧ (Q ∧ R)) = ((P ∧ Q) ∧ R) :=
begin
  have pfAssoc: P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R := 
    begin
      split,
      assume pfPandQandR,
      have pfP := and.elim_left pfPandQandR,
      have pfQ := pfPandQandR.right.left,
      have pfPandQ := and.intro pfP pfQ,
      have pfR := pfPandQandR.right.right,
      exact and.intro pfPandQ pfR,

      assume pfPandQ_andR,
      have pfQ := (and.elim_right (and.elim_left pfPandQ_andR)),
      have pfR := pfPandQ_andR.right,
      have pfQandR := and.intro pfQ pfR,
      have pfP := pfPandQ_andR.left.left,
      exact and.intro pfP pfQandR,
    end,
  rw pfAssoc,
end

-- Also commutativity
lemma my_and_sym{P Q: Prop}:
  P ∧ Q ↔ Q ∧ P :=
begin
  split,
    assume pfPandQ,
    have pfP := pfPandQ.left,
    have pfQ := pfPandQ.right,
    exact and.intro pfQ pfP,

    assume pfQandP,
    have pfP := pfQandP.right,
    have pfQ := pfQandP.left,
    exact and.intro pfP pfQ,
end

lemma my_and_trans{P Q R: Prop}:
  P ∧ Q → Q ∧ R → P ∧ R :=
begin
  assume pfPandQ,
  assume pfQandR,
  have pfP := pfPandQ.left,
  have pfR := pfQandR.right,
  exact and.intro pfP pfR,
end

lemma my_and_trans'{P Q R: Prop}:
  (P ∧ Q) ∧ (Q ∧ R) → (P ∧ R) :=
begin
  assume pfPandQ_and_QandR,
  have pfP := pfPandQ_and_QandR.left.left,
  have pfR := pfPandQ_and_QandR.right.right,
  exact and.intro pfP pfR,
end

lemma my_and_trans''{P Q R: Prop}:
  P ∧ Q → Q ∧ R → P ∧ R :=
begin
  assume pfPandQ,
  assume pfQandR,
  split,
    exact pfPandQ.left,
    exact pfQandR.right,
end

lemma non_contradiction{P: Prop}:
  ¬(P ∧ ¬P) :=
begin
  assume pfPandNotP,
  have pfNotP := pfPandNotP.right,
  have pfP := pfPandNotP.left,
  have pfFalse := (pfNotP pfP),
  assumption,
end

lemma true_identity_right:
  ∀(P: Prop), (P ∧ true ↔ P) :=
begin
  intros,
  split,
    -- P ∧ true → P
    assume pfPandTrue,
    exact pfPandTrue.left,
    -- P → P ∧ true
    assume pfP,
    have pfTrue := true.intro,
    exact and.intro pfP pfTrue,
end

lemma true_identity_left:
  ∀(P: Prop), (true ∧ P ↔ P) :=
begin
  intros,
  split,
    -- true ∧ P → P
    assume pfTrueandP,
    exact pfTrueandP.right,
    -- P → true ∧ P
    assume pfP,
    have pfTrue := true.intro,
    exact and.intro pfTrue pfP,
end

lemma false_absorption_right:
  ∀(P: Prop), ¬(P ∧ false) :=
begin
  intros,
  assume pfPandFalse,
  exact pfPandFalse.right,
end

lemma false_absorption_left:
  ∀(P: Prop), ¬(false ∧ P) :=
begin
  intros,
  assume pfFalseandP,
  exact pfFalseandP.left,
end
