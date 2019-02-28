axiom em: ∀(P: Prop), P ∨ ¬P

-- Does (A → B) ↔ (¬B → ¬A)?
example: ∀(A B: Prop),
  (A → B) ↔ (¬B → ¬A) :=
begin
  sorry
end

-- Does (A → B) ↔ (¬A ∨ B)?
example: ∀(A B: Prop),
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

