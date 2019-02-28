axiom em: ∀(P: Prop), P ∨ ¬P

-- Does (A → B) ↔ (¬B → ¬A)?
example: ∀(A B: Prop),
  (A → B) ↔ (¬B → ¬A) :=
begin
  sorry
end

-- Does (A → B) ↔ (¬A ∨ B)?
lemma alt_implication: ∀(A B: Prop),
  (A → B) ↔ (¬A ∨ B) :=
begin
  sorry
end

-- Does (A → B → C) ↔ (A ∧ B → C)?
example: ∀(A B C: Prop),
  (A → B → C) ↔ (A ∧ B → C) :=
begin
  sorry
end

-- Does ((A → B) → C) ↔ (A ∧ B → C)?
example: ∀(A B C: Prop),
  ((A → B) → C) ↔ (A ∧ B → C) :=
begin
  sorry
end

-- Reflexive
-- Does A → A?
example: ∀(A: Prop), A → A :=
begin
  sorry
end

-- Symmetric
-- Does (A → B) → (B → A)?
example: ∀(A B: Prop),
  (A → B) → (B → A) :=
begin
  sorry
end

-- Transitive
-- Does (A → B) → (B → C) → (A → C)?
example: ∀(A B C: Prop),
  (A → B) → (B → C) → (A → C) :=
begin
  sorry
end

-- Connected
-- Does (A ≠ B) → ((A → B) ∨ (B → A))?
example: ∀(A B: Prop),
  (A ≠ B) → ((A → B) ∨ (B → A)) :=
begin
  sorry
end
