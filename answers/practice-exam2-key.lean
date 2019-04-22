
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
example: 2 + 5 = 3 ∨ 9 + 1 = 5 → 2 + 3 = 9
:=
begin
  assume pf_disj,
  cases pf_disj with left right,
    -- 2 + 5 = 0
    /-
    have pf_contra: 2 + 5 ≠ 0 :=
    begin
      apply nat.no_confusion,
    end,
    contradiction,
    -/
    cases left,
    -- 9 + 1 = 0
    /-
    have pf_contra: 9 + 1 ≠ 0 :=
    begin
      apply nat.no_confusion,
    end,
    contradiction,
    -/
    cases right, 
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
      /-
      Think about what we just proved and how we proved
      it. The em principle allowed us to consider two cases
      for each of P, Q, and R. In case any one of them is
      false, the an ease "or introduction" will prove the
      goal. In the case all of them are true, well, that
      contradicts the assumption, and (using false elim)
      we can ignore cases with contradictory assumptions
      because they can't actually happen.
      -/


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

    /-
    In this case, we've assumed all of P, Q, and R
    are true. In this context, the assumption that at
    least one of them is false is contradictory. What
    the proof script confirms is that this intuition 
    can be proved formally.
    -/
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
      /-
      Here again the key insight is that from a proof
      of just A we can construct proof of a contradiction
      that directly contradicts an assumption, at which
      point we have shown that this case can be dismissed
      using false elimination (via the contradiction tactic).
      -/
      have pf_disj: A ∨ B ∨ C :=
        or.inl pf_A,
      contradiction,
      split,        -- short for apply and.intro _ _,
        -- ¬B
        assume pf_B,
        -- same trick 
        have pf_disj: A ∨ B ∨ C :=
          or.inr (or.inl pf_B),
        contradiction,
        -- ¬C
        assume pf_C,
        -- same trick 
        have pf_disj: A ∨ B ∨ C :=
          or.inr (or.inr pf_C),
        contradiction,

    -- ¬A ∧ ¬B ∧ ¬C → ¬(A ∨ B ∨ C)
    assume pf_conj_not,
    assume pf_disj,
    -- each one false + at least one true = contradiction
    cases pf_disj with pf_A pf_disj,
      -- A
      -- basically same trick: expose direct contradition
      have pf_not_A := pf_conj_not.left,
      contradiction,
      -- repeat until done
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
  split,        -- short for "apply IFF.intro _ _"
    -- ¬(X ∨ ¬Y) → ¬X ∧ Y
    assume pf_not_disj,
    split,      -- short for "apply AND.intro _ _"
      -- ¬X
      assume pf_X,
      -- here's that same trick again
      have pf_disj: X ∨ ¬Y := or.inl pf_X,
      contradiction,
      -- Y
      /-
      Case analysis on (Y ∨ ¬ Y). Think about the two
      cases before proceeding "blindly". In the case that
      Y is true, then the goal is proved. What happens in
      the case where Y is false? Yep: that's a contradiction,
      which you can expose with the same trick we've seen
      several times here already.
      -/
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
    /-
    At this point there's nothing we can do *unless*
    we use excluded middle to consider only two cases,
    one where we have a proof that A is true and one 
    where we have a proof that it is not true. Then we
    do the same kind of case analysis for B. In effect
    we're *just looking at the truth table*. There are
    four cases: A true, B true; A true, A false; B true,
    A false; B false. Before proceeding, just think 
    about what happens in each case. Write out the
    truth table.
    -/
    cases (em A) with pf_A pf_not_A,
      -- A
      cases (em B) with pf_B pf_not_B,
        -- B
        exact or.inr pf_B,
        -- ¬B
        -- here's that trick again!
        have pf_conj: A ∧ ¬B := ⟨pf_A, pf_not_B⟩,
        contradiction,
      -- ¬A
      exact or.inl pf_not_A,


    -- ¬A ∨ B → ¬(A ∧ ¬B)
    assume pf_disj,
    assume pf_conj,
    /-
    Look at and *think about* what's in the context.
    You must be able to reason logically at this point.
    If ¬ A or B is true, it is true because at least one
    of them is true. If ¬ A is true, that contradicts the
    other assumption, that both A and ¬ B are true. If B
    is true, on the other hand, that's also a contradiction.
    -/
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
    /-
    Beyond just mechanically applying tactics,
    stop now and think about what you've got. As
    a mathematician, you want to start to "look
    ahead" to see "what will happen" if you try
    different approaches. Here, for example, you
    can see that if the disjunction is true because
    ¬ P is true, that will immediately give you a
    contradiction that you can use to be done with
    that case. Think ahead about the other case.
    Start to see beyond the current instant, to 
    see what's coming if you take certain paths. 
    -/
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
    /-
    There's no way forward constructively.
    But if we can assume that there are only
    two possible cases for P, Q, and R, then
    we can just consider each case in turn,
    again using what amounts to the method
    of "truth tables".
    -/
    cases (em P) with pf_P pf_not_P,
      -- P
      /-
      Right here you use another absolutely (!!)
      fundamental insight. If you have a proof
      of an implication and you have a proof of
      its premise you can derive a proof of its
      conclusion. In constructive logic this is
      done by "applying" the implication proof
      (a function!) to the premise proof (a valid
      argument).
      -/
      have pf_Q_to_R := pf_impl pf_P,
      cases (em Q) with pf_Q pf_not_Q,
        -- Q
        have pf_R := pf_Q_to_R pf_Q,
        /-
        We have a proof of R and now only 
        need to prove a disjunction in which
        R is one of the disjunctions. You have
        to understand the associativity of ∨.
        It's right associative.
        -/
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
  /-
  How to proceed here is a little tricky. A key
  insight is that you can apply em to whatever
  proposition you want, to get a proof that is is
  either true or a proof that it is false. Here,
  applying em to ¬ P does the trick. Think ahead
  to see if you can see why. Then *confirm* what
  you see by going through the proof script.
  -/
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

/-
Note: Problems that start with ∃ are basically
search problems: you have to "searcg for, find,
and then use a witness that makes the proposition
true." In the worse case, use a truth table. That
is the way to systematically consider all possible
solutions. A problem with two "variables" will have
only four cases to consider. You can of course try
a value, and if you get stuck, "backtrack" (go back
and change your choice then try going forward again).

Also note that ∃(P Q: Prop), _ is short for
∃( P : Prop), ∃ (Q : Prop), _.
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
  have isEven6: isEven 6 := ⟨3, rfl⟩,   -- exists.intro
  have isPrime6: isMult3 6 := ⟨2, rfl⟩, -- exists.intro
  have both := and.intro isEven6 isPrime6,
  exact ⟨6, both⟩,                      -- exists.intro
end

/-
10a. Write the lemma that if there exists 
 someone that you can fool all of the time, 
 then there always exists someone you can fool.
 Use the supplied axioms, and make sure you use
 at least as many parentheses as needed. (It's
 okay to use more than you need.)
10b. Prove the above lemma.

Note that this problem really requires that 
you be able not only to prove but to write
propositions involving several quantifiers,
translating from English into the correct
logical formalism.
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


