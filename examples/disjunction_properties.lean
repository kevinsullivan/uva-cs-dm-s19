theorem absorb_right_or: ∀(P : Prop), P ∨ true :=
begin
  assume P,
  exact or.inr true.intro
end

theorem absorb_right_or': ∀(P : Prop), P ∨ true :=
  λ(P), or.inr true.intro

theorem absorb_left_or: ∀(P : Prop), true ∨ P :=
begin
  assume P,
  exact or.inl true.intro
end

theorem wet'' : 
  ∀(R S W: Prop), 
    (R ∨ S) → (R → W) → (S → W) → W :=
begin
  assume R S W,
  assume pf_R_or_S,
  assume pf_R_to_W,
  assume pf_S_to_W,
  exact or.elim pf_R_or_S pf_R_to_W pf_S_to_W,
end

theorem wet''' : 
  ∀(R S W: Prop), 
    (R ∨ S) → (R → W) → (S → W) → W :=
begin
  assume R S W,
  assume pf_R_or_S,
  assume pf_R_to_W,
  assume pf_S_to_W,
  cases pf_R_or_S with pf_R pf_S,
    -- case R
    exact pf_R_to_W pf_R,
    -- case S
    exact pf_S_to_W pf_S,
end

theorem id_right_or: ∀(P: Prop), P ∨ false ↔ P :=
begin
  assume P,
  split,
    -- P ∨ false → P
    assume pf_P_or_false,
    cases pf_P_or_false with pf_P pf_false,
      -- pf_P
      assumption,
      -- pf_false
      exact false.elim pf_false,
    -- P → P ∨ false
    assume pf_P,
    exact or.inl pf_P,
end

theorem id_left_or: ∀(P: Prop), false ∨ P ↔ P :=
begin
  assume P,
  split,
    -- false ∨ P → P
    assume pf_false_or_P,
    cases pf_false_or_P with pf_false pf_P,
      -- pf_false
      exact false.elim pf_false,
      -- pf_P
      assumption,
    -- P → false ∨ P
    assume pf_P,
    exact or.intro_right false pf_P,
end

theorem disjunctiveSyllogism:
  ∀(P Q: Prop), P ∨ Q → ¬Q → P :=
begin
  assume P Q,
  assume pfPOrQ,
  assume pfNotQ,
  cases pfPOrQ with pfP pfQ, -- now by cases
    assumption, -- case where p is true,
    exact false.elim (pfNotQ pfQ), -- or q true
end

axiom em: ∀(P: Prop), P ∨ ¬P

theorem DeMorganOne: ∀(P Q: Prop), ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
begin
  assume P Q,
  split,
    -- ¬(P ∨ Q) → ¬P ∧ ¬Q
    assume pf_not__P_or_Q,
    split,
      -- prove ¬P
      cases (em P) with pf_P pf_not_P,
        -- pf_P
        have pf_P_or_Q: P ∨ Q := or.inl pf_P,
        exact false.elim (pf_not__P_or_Q pf_P_or_Q),
        -- pf_not_P
        assumption,
      -- prove ¬Q
      cases (em Q) with pf_Q pf_not_Q,
        -- pf_Q
        have pf_P_or_Q: P ∨ Q := or.inr pf_Q,
        exact false.elim (pf_not__P_or_Q pf_P_or_Q),
        -- pf_not_Q,
        assumption,
    -- ¬P ∧ ¬Q → ¬(P ∨ Q)
    assume pf_not_P_and_not_Q,
    assume pf_P_or_Q,
    cases pf_P_or_Q with pf_P pf_Q,
      -- pf_P
      have pf_not_P: ¬P := pf_not_P_and_not_Q.left,
      exact pf_not_P pf_P,
      -- pf_Q
      have pf_not_Q: ¬Q := pf_not_P_and_not_Q.right,
      exact pf_not_Q pf_Q,
end

theorem DeMorganTwo: ∀(P Q: Prop), ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
begin
  assume P Q,
  split,
    -- ¬(P ∧ Q) → ¬P ∨ ¬Q
    assume pf_not__P_and_Q,
    cases (em P) with pf_P pf_not_P,
      -- pf_P
      cases (em Q) with pf_Q pf_not_Q,
        -- pf_Q
        have pf_P_and_Q := and.intro pf_P pf_Q,
        exact false.elim (pf_not__P_and_Q pf_P_and_Q),
        -- pf_not_Q
        exact or.inr pf_not_Q,
      -- pf_not_P
      exact or.inl pf_not_P,
    -- ¬P ∨ ¬Q → ¬(P ∧ Q)
    assume pf_not_P_or_not_Q,
    assume pf_P_and_Q,
    cases pf_not_P_or_not_Q with pf_not_P pf_not_Q,
      -- pf_not_P
      have pf_P := pf_P_and_Q.left,
      exact pf_not_P pf_P,
      -- pf_not_Q
      have pf_Q := pf_P_and_Q.right,
      exact pf_not_Q pf_Q,
end

-- Is disjunction reflexive?
-- Is A ∨ A true?
-- No
example: ¬∀(A: Prop), A ∨ A :=
begin
  assume pf_forall,
  have pf_false_or_false := pf_forall false,
  cases pf_false_or_false,
    assumption, assumption,
end

-- Is disjunction symmetric?
-- Does A ∨ B imply B ∨ A?
example: ∀(A B: Prop),
  (A ∨ B) → (B ∨ A) :=
begin
  assume A B,
  assume pf_A_or_B,
  cases pf_A_or_B with pf_A pf_B,
    exact or.inr pf_A,
    exact or.inl pf_B,
end

-- Is disjunction associative?
-- Are (A ∨ B) ∨ C and A ∨ (B ∨ C) the same?
example: ∀(A B C: Prop),
  (A ∨ B) ∨ C ↔ A ∨ (B ∨ C) :=
begin
  assume A B C,
  split,
    -- (A ∨ B) ∨ C → A ∨ (B ∨ C)
    assume pf_A_or_B__or_C,
    cases pf_A_or_B__or_C with pf_A_or_B pf_C,
      -- pf_A_or_B
      cases pf_A_or_B with pf_A pf_B,
        -- pf_A
        exact or.inl pf_A,
        -- pf_B
        have pf_B_or_C: B ∨ C := or.inl pf_B,
        exact or.inr pf_B_or_C,
      -- pf_C
      have pf_B_or_C: B ∨ C := or.inr pf_C,
      exact or.inr pf_B_or_C,
    -- A ∨ (B ∨ C) → (A ∨ B) ∨ C
    assume pf_A_or__B_or_C,
    cases pf_A_or__B_or_C with pf_A pf_B_or_C,
      -- pf_A
      have pf_A_or_B := or.intro_left B pf_A,
      exact or.inl pf_A_or_B,
      -- pf_B_or_C
      cases pf_B_or_C with pf_B pf_C,
        -- pf_B
        have pf_A_or_B := or.intro_right A pf_B,
        exact or.inl pf_A_or_B,
        -- pf_C
        exact or.inr pf_C,
end

-- Is disjunction transitive?
-- Does (A ∨ B) and (B ∨ C) imply (A ∨ C)?
-- No
example: ¬∀(A B C: Prop),
  (A ∨ B) → (B ∨ C) → (A ∨ C) :=
begin
  assume pf_forall,
  have pf_falseness := pf_forall false true false,
  have pf_f_or_t := or.intro_right false true.intro,
  have pf_t_or_f := or.intro_left false true.intro,
  have pf_f_or_f := (pf_falseness pf_f_or_t) pf_t_or_f,
  cases pf_f_or_f with pf_f pf_f,
    assumption, assumption,
end

-- Distribution over ∧
example: ∀(A B C: Prop),
  A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) :=
begin
  assume A B C,
  split,
    -- A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
    assume pf_A_or__B_and_C,
    cases pf_A_or__B_and_C with pf_A pf_B_and_C,
      -- pf_A
      have pf_A_or_B: A ∨ B := or.inl pf_A,
      have pf_A_or_C := or.intro_left C pf_A,
      exact and.intro pf_A_or_B pf_A_or_C,
      -- pf_B_and_C
      have pf_C := pf_B_and_C.left,
      have pf_A_or_B: A ∨ B := or.inr pf_C,
      have pf_B := pf_B_and_C.right,
      have pf_A_or_C: A ∨ C := or.inr pf_B,
      exact and.intro pf_A_or_B pf_A_or_C,
    -- (A ∨ B) ∧ (A ∨ C) → A ∨ (B ∧ C)
    assume pf_A_or_B__and__A_or_C,
    cases pf_A_or_B__and__A_or_C.left with pf_A pf_B,
      -- pf_A
      exact or.inl pf_A,
      -- pf_B
      cases pf_A_or_B__and__A_or_C.right with pf_A pf_C,
        -- pf_A
        exact or.inl pf_A,
        -- pf_C
        have pf_B_and_C := and.intro pf_B pf_C,
        exact or.inr pf_B_and_C,
end

-- Distribution over ∨
example: ∀(A B C: Prop),
  A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
begin
  assume A B C,
  split,
    -- A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
    assume pf_A__and_B_or_C,
    cases pf_A__and_B_or_C.right with pf_B pf_C,
      -- B
      have pf_A := pf_A__and_B_or_C.left,
      have pf_A_and_B := and.intro pf_A pf_B,
      exact or.inl pf_A_and_B,
      -- C
      have pf_A := pf_A__and_B_or_C.left,
      have pf_A_and_C := and.intro pf_A pf_C,
      exact or.inr pf_A_and_C,
    -- (A ∧ B) ∨ (A ∧ C) → A ∧ (B ∨ C)
    assume pf_A_and_B__or__A_and_C,
    cases pf_A_and_B__or__A_and_C with pf_A_and_B pf_A_and_C,
      -- A ∧ B
      have pf_B := pf_A_and_B.right,
      have pf_B_or_C: B ∨ C := or.inl pf_B,
      have pf_A := pf_A_and_B.left,
      exact and.intro pf_A pf_B_or_C,
      -- A ∧ C
      have pf_C := pf_A_and_C.right,
      have pf_B_or_C: B ∨ C := or.inr pf_C,
      have pf_A := pf_A_and_C.left,
      exact and.intro pf_A pf_B_or_C,
end

