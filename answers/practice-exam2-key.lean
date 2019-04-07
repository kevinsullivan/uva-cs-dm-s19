
/-
Conjunctions, disjunctions, implication, iff,
negation
-/

/-
1. Prove that 3 + 3 = 6 and 2 + 6 = 8 implies
that 1 + 1 = 2.
-/

-- answer:
example: 3 + 3 = 6 ∧ 2 + 6 = 8 → 1 + 1 = 2
:=
begin
  assume pf_conj,
  exact rfl,
end

/-
2. Prove that 2 + 5 = 3 or 9 + 1 = 5 implies
that 2 + 3 = 9.
-/

-- answer:
example: 2 + 5 = 0 ∨ 9 + 1 = 0 → 2 + 3 = 9
:=
begin
  assume pf_disj,
  cases pf_disj,
    -- 2 + 5 = 0
    have pf_contra: 2 + 5 ≠ 0 :=
    begin
      apply nat.no_confusion,
    end,
    contradiction,
    -- 9 + 1 = 0
    have pf_contra: 9 + 1 ≠ 0 :=
    begin
      apply nat.no_confusion,
    end,
    contradiction,
end

/-
3. Prove that ¬(A ∧ B ∧ C) ↔ (¬A ∨ ¬B ∨ ¬C).
You may use the axiom of the excluded middle.
-/

axiom em: ∀(P: Prop), P ∨ ¬P

-- answer:
example: ∀(A B C: Prop),
  ¬(A ∧ B ∧ C) ↔ (¬A ∨ ¬B ∨ ¬C) :=
begin
  assume P Q R,
  split,
    -- ¬(P ∧ Q ∧ R) → ¬P ∨ ¬Q ∨ ¬R
    assume pf_not_conj,
    cases (em P) with pf_p pf_not_p,
      cases (em Q) with pf_q pf_not_q,
        cases (em R) with pf_r pf_not_r,
          -- P ∧ Q ∧ R
          have pf_conj: P ∧ Q ∧ R := ⟨pf_p, ⟨pf_q, pf_r⟩⟩,
          contradiction,
          -- ¬R
          exact or.inr (or.inr pf_not_r),
        -- ¬Q
        exact or.inr (or.inl pf_not_q),
      -- ¬P
      exact or.inl pf_not_p,
    -- ¬P ∨ ¬Q ∨ ¬R → ¬(P ∧ Q ∧ R)
    assume pf_disj_not,
    assume pf_conj,
    cases pf_disj_not with pf_not_p pf_disj_not,
      -- ¬P
      have pf_p := pf_conj.left,
      contradiction,
      -- ¬Q ∨ ¬R
      cases pf_disj_not with pf_not_q pf_not_r,
        -- ¬Q
        have pf_q := pf_conj.right.left,
        contradiction,
        -- ¬R
        have pf_r := pf_conj.right.right,
        contradiction,
end

/-
4. Prove that ¬(A ∨ B ∨ C) ↔ (¬A ∧ ¬B ∧ ¬C).
You may *NOT* use the axiom of the excluded middle.
-/

-- answer:
example: ∀(A B C: Prop),
  ¬(A ∨ B ∨ C) ↔ (¬A ∧ ¬B ∧ ¬C) :=
begin
  intros,
  split,
    -- ¬(A ∨ B ∨ C) → ¬A ∧ ¬B ∧ ¬C
    assume pf_not_disj,
    split,
      -- ¬A
      assume pf_A,
      have pf_disj: A ∨ B ∨ C :=
        or.inl pf_A,
      contradiction,
      split,
        -- ¬B
        assume pf_B,
        have pf_disj: A ∨ B ∨ C :=
          or.inr (or.inl pf_B),
        contradiction,
        -- ¬C
        assume pf_C,
        have pf_disj: A ∨ B ∨ C :=
          or.inr (or.inr pf_C),
        contradiction,
    -- ¬A ∧ ¬B ∧ ¬C → ¬(A ∨ B ∨ C)
    assume pf_conj_not,
    assume pf_disj,
    cases pf_disj with pf_A pf_disj,
      -- A
      have pf_not_A := pf_conj_not.left,
      contradiction,
      cases pf_disj with pf_B pf_C,
        -- B
        have pf_not_B := pf_conj_not.right.left,
        contradiction,
        -- C
        have pf_not_C := pf_conj_not.right.right,
        contradiction,
end

/-
5a. Prove that ¬(A ∨ ¬B) ↔ (¬A ∧ B).
You may use the axiom of the excluded middle.
-/

-- answer:
example: ∀(A B: Prop),
  ¬(A ∨ ¬B) ↔ (¬A ∧ B) :=
begin
  assume X Y,
  split,
    -- ¬(X ∨ ¬Y) → ¬X ∧ Y
    assume pf_not_disj,
    split,
      -- ¬X
      assume pf_X,
      have pf_disj: X ∨ ¬Y := or.inl pf_X,
      contradiction,
      -- Y
      cases (em Y) with pf_Y pf_not_Y,
        -- Y,
        assumption,
        -- ¬Y
        have pf_disj: X ∨ ¬Y := or.inr pf_not_Y,
        contradiction,
    -- ¬X ∧ Y → ¬(X ∨ ¬Y)
    assume pf_not_X_and_Y,
    assume pf_X_or_not_Y,
    cases pf_X_or_not_Y with pf_X pf_not_Y,
      -- X
      have pf_not_X := pf_not_X_and_Y.left,
      contradiction,
      -- ¬Y
      have pf_Y := pf_not_X_and_Y.right,
      contradiction,
end

/-
5b. Prove that ¬(A ∧ ¬B) ↔ (¬A ∨ B).
You may use the axiom of the excluded middle.
-/

-- answer:
example: ∀(A B: Prop),
  ¬(A ∧ ¬B) ↔ (¬A ∨ B) :=
begin
  intros,
  split,
    -- ¬(A ∧ ¬B) → ¬A ∨ B
    assume pf_not_conj,
    cases (em A) with pf_A pf_not_A,
      -- A
      cases (em B) with pf_B pf_not_B,
        -- B
        exact or.inr pf_B,
        -- ¬B
        have pf_conj: A ∧ ¬B := ⟨pf_A, pf_not_B⟩,
        contradiction,
      -- ¬A
      exact or.inl pf_not_A,
    -- ¬A ∨ B → ¬(A ∧ ¬B)
    assume pf_disj,
    assume pf_conj,
    cases pf_disj with pf_not_A pf_B,
      -- ¬A
      have pf_A := pf_conj.left,
      contradiction,
      -- B
      have pf_not_B := pf_conj.right,
      contradiction,
end

/-
6. Prove that ¬P ∨ ¬Q ∨ R is true if and only
if P → Q → R. You may use the axiom of the
excluded middle.
-/

-- answer:
example: ∀(P Q R: Prop),
  (¬P ∨ ¬Q ∨ R) ↔ (P → Q → R) :=
begin
  intros,
  split,
    -- ¬P ∨ ¬Q ∨ R → (P → Q → R)
    assume pf_disj,
    assume pf_P,
    assume pf_Q,
    cases pf_disj with pf_not_P pf_disj,
      -- ¬P
      contradiction,
      cases pf_disj with pf_not_Q pf_R,
        -- ¬Q
        contradiction,
        -- R
        assumption,
    -- (P → Q → R) → ¬P ∨ ¬Q ∨ R
    assume pf_impl,
    cases (em P) with pf_P pf_not_P,
      -- P
      have pf_Q_to_R := pf_impl pf_P,
      cases (em Q) with pf_Q pf_not_Q,
        -- Q
        have pf_R := pf_Q_to_R pf_Q,
        exact or.inr (or.inr pf_R),
        -- ¬Q
        exact or.inr (or.inl pf_not_Q),
      -- ¬P
      exact or.inl pf_not_P,
end

/-
7. Prove that ¬¬¬P → ¬P. You may use the axiom
of the excluded middle.
-/

-- answer:
example: ∀(P: Prop), ¬¬¬P → ¬P :=
begin
  assume P,
  assume pf_trip_neg,
  assume pf_P,
  cases (em ¬P) with pf_not_P pf_nn_P,
    -- ¬P
    contradiction, -- contradicts P
    -- ¬¬P
    contradiction, -- contradicts ¬¬¬P
end

/-
Universal Quantifiers, Existential Quantifiers, and
Satisfiability.
-/

/-
8. Prove the following statements are satisfiable
or prove that they are not. You may use the axiom
of the excluded middle to prove cases where the
statements are not satisfiable.
-/

/-
8a. (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q)
-/

-- answer:
example: ∃(P Q: Prop),
  (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) :=
begin
  apply exists.intro true,
  apply exists.intro true,
  split,
    -- P ∨ Q
    exact or.inl true.intro,
    split,
      -- ¬P ∨ Q
      exact or.inr true.intro,
      -- P ∨ ¬Q
      exact or.inl true.intro,
end

/-
8b. (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) ∧ (¬P ∨ ¬Q)
-/

-- answer:
example: ¬∃(P Q: Prop),
  (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) ∧ (¬P ∨ ¬Q) :=
begin
  assume pf_exists,
  apply exists.elim pf_exists,
  assume P pf_w',
  apply exists.elim pf_w',
  assume Q pf_w,
  cases (em P) with pf_P pf_not_P,
    cases (em Q) with pf_Q pf_not_Q,
      -- P, Q
      have pf_not_P_or_not_Q := pf_w.right.right.right,
      cases pf_not_P_or_not_Q with pf_not_P pf_not_Q,
        contradiction, contradiction,
      -- P, ¬Q
      have pf_not_P_or_Q := pf_w.right.left,
      cases pf_not_P_or_Q with pf_not_P pf_Q,
        contradiction, contradiction,
    cases (em Q) with pf_Q pf_not_Q,
      -- ¬P, Q
      have pf_P_or_not_Q := pf_w.right.right.left,
      cases pf_P_or_not_Q with pf_P pf_not_Q,
        contradiction, contradiction,
      -- ¬P, ¬Q
      have pf_P_or_Q := pf_w.left,
      cases pf_P_or_Q with pf_P pf_Q,
        contradiction, contradiction,
end

/-
8c. (P ∨ Q ∨ R) ∧ (¬P ∨ Q ∨ R) ∧
     (P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ ¬Q ∨ ¬R)
-/

-- answer:
example: ∃(P Q R: Prop),
  (P ∨ Q ∨ R) ∧ (¬P ∨ Q ∨ R) ∧
    (P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ ¬Q ∨ ¬R) :=
begin
  apply exists.intro true,
  apply exists.intro true,
  apply exists.intro false,
  split,
    -- P ∨ Q ∨ R
    exact or.inl true.intro,
    split,
      -- ¬P ∨ Q ∨ R
      exact or.inr (or.inl true.intro),
      split,
        -- P ∨ ¬Q ∨ ¬R
        exact or.inl true.intro,
        -- ¬P ∨ ¬Q ∨ ¬R
        exact or.inr (or.inr false.elim),
end

/-
9. Prove that exists a number such that
it is both even and a multiple of 3.
Use the supplied definitions of even and prime.
-/

def isEven(n: ℕ) := (∃(m: ℕ), m * 2 = n)

def isMult3(n: ℕ) := (∃(m: ℕ), m * 3 = n)

-- answer
example:
  ∃(n: ℕ), isEven n ∧ isMult3 n :=
begin
  have isEven6: isEven 6 := ⟨3, rfl⟩,
  have isPrime6: isMult3 6 := ⟨2, rfl⟩,
  have both := and.intro isEven6 isPrime6,
  exact ⟨6, both⟩,
end

/-
10a. Write the lemma that if there exists 
 someone that you can fool all of the time, 
 then there always exists someone you can fool.
 Use the supplied axioms, and make sure you use
 at least as many parentheses as needed. (It's
 okay to use more than you need.)
10b. Prove the above lemma.
-/

axioms Person Time: Type
axiom fool: Person → Time → Prop

-- answers:
example:
  (∃(p: Person), ∀ (t: Time), fool p t) →
  (∀(t: Time), ∃(p: Person), fool p t) :=
begin
  assume pfIdiotExists,
  assume t,
  apply exists.elim pfIdiotExists,
  assume witness pf_witness,
  have pfCurIdiot := pf_witness t,
  exact ⟨witness, pfCurIdiot⟩,
end

