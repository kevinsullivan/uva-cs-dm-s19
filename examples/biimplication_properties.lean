-- Reflexive
-- Does A ↔ A?
example: ∀(A: Prop), A ↔ A :=
begin
  sorry
end

-- Symmetric (exercise)
-- Does (A ↔ B) → (B ↔ A)?
example: ∀(A B: Prop),
  (A ↔ B) → (B ↔ A) :=
begin
  sorry
end

-- Associative
-- Does ((A ↔ B) ↔ C) ↔ (A ↔ (B ↔ C))?
-- No
example: ¬∀(A B C: Prop), 
  ((A ↔ B) ↔ C) ↔ (A ↔ (B ↔ C))
begin
end

-- Transitive (exercise)
-- Does (A ↔ B) → (B ↔ C) → (A ↔ C)?
example: ∀(A B C: Prop),
  (A ↔ B) → (B ↔ C) → (A ↔ C) :=
begin
  assume A B C,
  assume pf_A_iff_B pf_B_iff_C,
  split,
    -- prove A → C
    have pf_A_to_B := (iff.elim_left pf_A_iff_B),
    have pf_B_to_C := (iff.elim_left pf_B_iff_C),
    assume pf_A,
    have pf_B := pf_A_to_B pf_A,
    exact pf_B_to_C pf_B,
    -- prove C → A
    have pf_C_to_B := (iff.elim_right pf_B_iff_C),
    have pf_B_to_A := (iff.elim_right pf_A_iff_B),
    assume pf_C,
    have pf_B := pf_C_to_B pf_C,
    exact pf_B_to_A pf_B,
end

-- Connected
-- Does (A ≠ B) → ((A ↔ B) ∨ (B ↔ A))?
-- No
example: ¬∀(A B: Prop),
  (A ≠ B) → ((A ↔ B) ∨ (B ↔ A)) :=
begin
  sorry
end

-- Exercise
example: ∀(P Q: Prop),
   P ∧ Q ↔ Q ∧ P :=
begin
  assume P Q,
  split,
    -- P ∧ Q → Q ∧ P
    assume pf_P_and_Q,
    have pf_Q := pf_P_and_Q.right,
    have pf_P := pf_P_and_Q.left,
    exact and.intro pf_Q pf_P,
    -- Q ∧ P → P ∧ Q
    assume pf_Q_and_P,
    have pf_P := pf_Q_and_P.right,
    have pf_Q := pf_Q_and_P.left,
    exact and.intro pf_P pf_Q,
end

-- Exercise
lemma a_imp_b_imp_c_iff_a_and_b_imp_c:
  ∀(A B C: Prop), A → B → C ↔ A ∧ B → C :=
begin
  sorry
end
