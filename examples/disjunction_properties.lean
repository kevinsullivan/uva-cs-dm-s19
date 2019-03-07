theorem absorb_right_or: ∀(P : Prop), P ∨ true :=
begin
  sorry
end

theorem absorb_left_or: ∀(P : Prop), true ∨ P :=
begin
  sorry
end

theorem id_right_or: ∀(P: Prop), P ∨ false ↔ P :=
begin
  sorry
end

theorem id_left_or: ∀(P: Prop), false ∨ P ↔ P :=
begin
  sorry
end

theorem disjunctiveSyllogism :
  ∀(P Q: Prop), P ∨ Q → ¬Q → P :=
begin
  intros P Q pfPOrQ pfNotQ, -- assumptions
  cases pfPOrQ with pfP pfQ, -- now by cases
    assumption, -- case where p is true,
    exact false.elim (pfNotQ pfQ) -- or q true
end

theorem DeMorganOne: ∀(P Q: Prop), ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
begin
  sorry
end

theorem DeMorganTwo: ∀(P Q: Prop), ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
begin
  sorry
end

-- Is disjunction reflexive?
-- Is A ∨ A true?
-- No
example: ¬∀(A: Prop), A ∨ A :=
begin
  sorry
end

-- Is disjunction symmetric?
-- Does A ∨ B imply B ∨ A?
example: ∀(A B: Prop),
  (A ∨ B) → (B ∨ A) :=
begin
  sorry
end

-- Is disjunction associative?
-- Are (A ∨ B) ∨ C and A ∨ (B ∨ C) the same?
example: ∀(A B C: Prop),
  (A ∨ B) ∨ C ↔ A ∨ (B ∨ C) :=
begin
  sorry
end

-- Is disjunction transitive?
-- Does (A ∨ B) and (B ∨ C) imply (A ∨ C)?
-- No
example: ¬∀(A B C: Prop),
  (A ∨ B) → (B ∨ C) → (A ∨ C) :=
begin
  sorry
end

-- Distribution over ∧
example: ∀(A B C: Prop),
  A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) :=
begin
  assume A B C,
  sorry
end

-- Distribution over ∨
example: ∀(A B C: Prop),
  A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
begin
  assume A B C,
  sorry
end

