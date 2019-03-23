axiom em: ∀(P: Prop), P ∨ ¬P

-- Does (A → B) ↔ (¬B → ¬A)?
example: ∀(A B: Prop),
  (A → B) ↔ (¬B → ¬A) :=
begin
  intros,
  split,
    -- (A → B) → ¬B → ¬A
    assume pf_A_to_B,
    assume pf_not_B,
    assume pf_A,
    have pf_B := pf_A_to_B pf_A,
    contradiction,

    -- ¬B → ¬A → (A → B)
    assume pf_not_B_to_not_A,
    assume pf_A,
    cases (em B) with pf_B pf_not_B,
      -- pf_B
      assumption,
      -- pf_not_B
      have pf_not_A := pf_not_B_to_not_A pf_not_B,
      have pf_false := pf_not_A pf_A,
      exact false.elim pf_false,
end

-- Does (A → B) ↔ (¬A ∨ B)?
lemma alt_implication: ∀(A B: Prop),
  (A → B) ↔ (¬A ∨ B) :=
begin
  assume A B,
  split,
    -- (A → B) → (¬A ∨ B)
    assume pf_A_imp_B,
    have pf_A_or_not_A := em A,
    cases pf_A_or_not_A with pf_A pf_not_A,
      -- assume pf_A
      have pf_B := pf_A_imp_B pf_A,
      exact or.inr pf_B,

      -- assume pf_not_A,
      exact or.inl pf_not_A,
    
    -- (¬A ∨ B) → (A → B)
    assume pf_not_A_or_B,
    assume pf_A,
    cases pf_not_A_or_B with pf_not_A pf_B,
      -- assume pf_not_A
      have f := (pf_not_A pf_A),
      exact false.elim f,

      -- assume pf_B
      assumption,
end

-- Does (A → B → C) ↔ (A ∧ B → C)?
example: ∀(A B C: Prop),
  (A → B → C) ↔ (A ∧ B → C) :=
begin
  assume A B C,
  split,
    -- (A → B → C) → (A ∧ B → C)
    assume pf_A_to_B_to_C,
    assume pf_A_and_B,
    have pf_A := pf_A_and_B.left,
    have pf_B := pf_A_and_B.right,
    have pf_B_to_C := pf_A_to_B_to_C pf_A,
    exact pf_B_to_C pf_B,

    -- (A ∧ B → C) → (A → B → C)
    assume pf_A_and_B_to_C,
    assume pf_A,
    assume pf_B,
    have pf_A_and_B := and.intro pf_A pf_B,
    exact pf_A_and_B_to_C pf_A_and_B,
end

-- Does ((A → B) → C) ↔ (A ∧ B → C)?
-- No, proof of opposite:
example: ¬(∀(A B C: Prop),
  ((A → B) → C) ↔ (A ∧ B → C)) :=
begin
  assume pf_forall,
  have pf_with_false := pf_forall false false false,
  have half_pf_with_false := (iff.elim_right pf_with_false),
  have pf_false_and_false_to_false: false ∧ false → false :=
    begin
      assume pf_false_and_false,
      exact pf_false_and_false.left,
    end,
  have pf_false_to_false__to_false :=
    half_pf_with_false pf_false_and_false_to_false,
  have pf_false_to_false: false → false :=
    λ(f: false), f,
  exact pf_false_to_false__to_false pf_false_to_false,
end

-- Reflexive
-- Does A → A?
example: ∀(A: Prop), A → A :=
begin
  assume A,
  assume pf_A,
  assumption,
end

-- Symmetric
-- Does (A → B) → (B → A)?
-- No, proof of opposite:
example: ¬∀(A B: Prop),
  (A → B) → (B → A) :=
begin
  assume pf_forall,
  have pf_false_to_true_to_true_to_false :=
    pf_forall false true,
  have pf_false_to_true :=
    λ(f: false), true.intro,
  have pf_true_to_false :=
    pf_false_to_true_to_true_to_false pf_false_to_true,
  exact pf_true_to_false true.intro,
end

-- Transitive
-- Does (A → B) → (B → C) → (A → C)?
example: ∀(A B C: Prop),
  (A → B) → (B → C) → (A → C) :=
begin
  assume A B C,
  assume pf_A_to_B,
  assume pf_B_to_C,
  assume pf_A,
  have pf_B := pf_A_to_B pf_A,
  exact pf_B_to_C pf_B,
end

-- Connected, with axiom of excluded middle
-- Does (A ≠ B) → ((A → B) ∨ (B → A))?
example: ∀(A B: Prop),
  (A ≠ B) → ((A → B) ∨ (B → A)) :=
begin
  assume A B,
  assume pf_A_neq_B,
  cases (em A) with pf_A pf_not_A,
    -- assume pf_A
    have pf_B_to_A: B → A :=
      λ(pf_B: B), pf_A,
    exact or.inr pf_B_to_A,

    -- assume pf_not_A
    have pf_not_A_or_B: ¬A ∨ B := or.inl pf_not_A,
    -- (A → B) ↔ (¬A ∨ B)
    have pf_A_to_B_iff_not_A_or_B :=
      alt_implication A B,
    have pf_not_A_or_B_to_A_to_B :=
      (iff.elim_right pf_A_to_B_iff_not_A_or_B),
    have pf_A_to_B := 
      pf_not_A_or_B_to_A_to_B pf_not_A_or_B,
    exact or.inl pf_A_to_B
end
