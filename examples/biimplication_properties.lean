-- Reflexive
-- Does A ↔ A?
example: ∀(A: Prop), A ↔ A :=
begin
  assume A,
  split,
    assume pf_A,
    assumption,
    assume pf_A,
    assumption,
end

-- Symmetric (exercise)
-- Does (A ↔ B) → (B ↔ A)?
example: ∀(A B: Prop),
  (A ↔ B) → (B ↔ A) :=
begin
  assume A B,
  assume pf_A_iff_B,
  have pf_A_to_B := (iff.elim_left pf_A_iff_B),
  have pf_B_to_A := (iff.elim_right pf_A_iff_B),
  exact iff.intro pf_B_to_A pf_A_to_B,
end

axiom em: ∀(P: Prop), P ∨ ¬P

-- Uses axiom of the excluded middle (classical)
theorem implicationToDisjunction{P Q: Prop}:
  (P → Q) → (¬P ∨ Q) :=
begin
  assume pf_P_to_Q,
  cases (em P) with pf_P pf_not_P,
    -- pf_P
    have pf_Q := pf_P_to_Q pf_P,
    exact or.inr pf_Q,
    -- pf_not_P
    exact or.inl pf_not_P,
end

-- constructive
theorem modusTollens{P Q: Prop}:
  (P → Q) → (¬Q → ¬P) :=
begin
  assume pf_P_to_Q,
  assume pf_not_Q,
  assume pf_P,
  have pf_Q := pf_P_to_Q pf_P,
  exact pf_not_Q pf_Q,
end

-- Associative
-- Does ((A ↔ B) ↔ C) ↔ (A ↔ (B ↔ C))?
example: ∀(A B C: Prop), 
  ((A ↔ B) ↔ C) ↔ (A ↔ (B ↔ C)) :=
begin
  assume A B C,
  split,
    -- ((A ↔ B) ↔ C) → (A ↔ (B ↔ C))
    assume pf_A_iff_B_iff_C,
    split,
      -- A → (B ↔ C)
      assume pf_A,
      split,
        -- B → C
        assume pf_B,
        have pf_A_iff_B_to_C := 
          (iff.elim_left pf_A_iff_B_iff_C),
        have pf_A_to_B: A → B :=
          begin
            assume pf_A',
            assumption,
          end,
        have pf_B_to_A :=
          λ(pf_B: B), pf_A,
        have pf_A_iff_B :=
          (iff.intro pf_A_to_B pf_B_to_A),
        exact pf_A_iff_B_to_C pf_A_iff_B,
        
        -- C → B
        assume pf_C,
        have pf_C_to_A_iff_B := 
          (iff.elim_right pf_A_iff_B_iff_C),
        have pf_A_iff_B := pf_C_to_A_iff_B pf_C,
        have pf_A_to_B := (iff.elim_left pf_A_iff_B),
        exact pf_A_to_B pf_A,
      -- (B ↔ C) → A
      assume pf_B_iff_C,
      have pf_C_to_A_iff_B := 
        (iff.elim_right pf_A_iff_B_iff_C),
      cases (em C) with pf_C pf_not_C,
        -- pf_C
        have pf_A_iff_B := pf_C_to_A_iff_B pf_C,
        have pf_B_to_A := (iff.elim_right pf_A_iff_B),
        cases (em B) with pf_B pf_not_B,
          -- pf_B
          exact pf_B_to_A pf_B,
          -- pf_not_B
          have pf_C_to_B := (iff.elim_right pf_B_iff_C),
          have pf_B := pf_C_to_B pf_C,
          exact false.elim (pf_not_B pf_B),
        -- pf_not_C
        cases (em B) with pf_B pf_not_B,
          -- pf_B
          have pf_B_to_C := (iff.elim_left pf_B_iff_C),
          have pf_C := pf_B_to_C pf_B,
          exact false.elim (pf_not_C pf_C),
          -- pf_not_B
          cases (em A) with pf_A pf_not_A,
            -- pf_A
            assumption,
            -- pf_not_A,
            have pf_A_iff_B_to_C := (iff.elim_left pf_A_iff_B_iff_C),
            have pf_A_to_B: A → B :=
              λ(pf_A: A), false.elim (pf_not_A pf_A),
            have pf_B_to_A: B → A :=
              λ(pf_B: B), false.elim (pf_not_B pf_B),
            have pf_A_iff_B := iff.intro pf_A_to_B pf_B_to_A,
            have pf_C := pf_A_iff_B_to_C pf_A_iff_B,
            exact false.elim (pf_not_C pf_C),
    -- (A ↔ (B ↔ C)) → ((A ↔ B) ↔ C)
    assume pf_A_iff__B_iff_C,
    split,
      -- (A ↔ B) → C
      assume pf_A_iff_B,
      cases (em A) with pf_A pf_not_A,
        -- pf_A
        -- Note the shorthand used here
        have pf_B := (iff.elim_left pf_A_iff_B) pf_A,
        have pf_B_iff_C := (iff.elim_left pf_A_iff__B_iff_C) pf_A,
        exact (iff.elim_left pf_B_iff_C) pf_B,
        -- pf_not_A
        cases (em B) with pf_B pf_not_B,
          -- pf_B
          -- Note the shorthand used here
          have pf_A := (iff.elim_right pf_A_iff_B) pf_B,
          exact false.elim (pf_not_A pf_A),
          -- pf_not_B
          cases (em C) with pf_C pf_not_C,
            -- pf_C
            assumption,
            -- pf_not_C
            have pf_B_to_C: B → C :=
              λ(pf_B: B), false.elim (pf_not_B pf_B),
            have pf_C_to_B: C → B :=
              λ(pf_C: C), false.elim (pf_not_C pf_C),
            have pf_B_iff_C := iff.intro pf_B_to_C pf_C_to_B,
            have pf_A := (iff.elim_right pf_A_iff__B_iff_C) pf_B_iff_C,
            exact false.elim (pf_not_A pf_A),
      -- C → (A ↔ B)
      assume pf_C,
      split,
        -- A → B
        assume pf_A,
        have pf_B_iff_C := (iff.elim_left pf_A_iff__B_iff_C) pf_A,
        have pf_C_to_B := (iff.elim_right pf_B_iff_C),
        exact pf_C_to_B pf_C,
        -- B → A
        assume pf_B,
        have pf_B_iff_C__to_A := (iff.elim_right pf_A_iff__B_iff_C),
        -- Note the shorthand used here
        have pf_B_iff_C := (iff.intro (λ(pfB: B), pf_C) (λ(pfC: C), pf_B)),
        exact pf_B_iff_C__to_A pf_B_iff_C,
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
  assume pf_forall,
  have pf_false_true := pf_forall false true,
  have pf_false_neq_true: false ≠ true :=
    begin
      assume pf_false_is_true,
      have t := true.intro,
      have pf_true_is_false := eq.symm pf_false_is_true,
      rewrite pf_true_is_false at t,
      assumption,
    end,
  have pf_false_iff_true := pf_false_true pf_false_neq_true,
  cases pf_false_iff_true,
    -- false ↔ true
    have pf_true_to_false := (iff.elim_right pf_false_iff_true),
    exact pf_true_to_false true.intro,
    -- true ↔ false
    have pf_true_to_false := (iff.elim_left pf_false_iff_true),
    exact pf_true_to_false true.intro,
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
  assume A B C,
  split,
    -- (A → B → C) → A ∧ B → C
    assume pf_A_to_B_to_C,
    assume pf_A_and_B,
    have pf_A := pf_A_and_B.left,
    have pf_B_to_C := pf_A_to_B_to_C pf_A,
    have pf_B := pf_A_and_B.right,
    exact pf_B_to_C pf_B,
    -- (A ∧ B → C) → A → B → C 
    assume pf_A_and_B_to_C,
    assume pf_A,
    assume pf_B,
    have pf_A_and_B := and.intro pf_A pf_B,
    exact pf_A_and_B_to_C pf_A_and_B,
end

