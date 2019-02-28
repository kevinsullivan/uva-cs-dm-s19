-- Reflexive
-- Does A ↔ A?
example: ∀(A: Prop), A ↔ A :=
begin
  sorry
end

-- Symmetric
-- Does (A ↔ B) → (B ↔ A)?
example: ∀(A B: Prop),
  (A ↔ B) → (B ↔ A) :=
begin
  sorry
end

-- Transitive (exercise)
-- Does (A ↔ B) → (B ↔ C) → (A ↔ C)?
example: ∀(A B C: Prop),
  (A ↔ B) → (B ↔ C) → (A ↔ C) :=
begin
  sorry
end

-- Connected
-- Does (A ≠ B) → ((A ↔ B) ∨ (B ↔ A))?
example: ∀(A B: Prop),
  (A ≠ B) → ((A ↔ B) ∨ (B ↔ A)) :=
begin
  sorry
end

-- Exercise
example: ∀(P Q: Prop),
   P ∧ Q ↔ Q ∧ P :=
begin
  sorry
end

-- Exercise
lemma a_imp_b_imp_c_iff_a_and_b_imp_c:
  ∀(A B C: Prop), A → B → C ↔ A ∧ B → C :=
begin
  sorry
end