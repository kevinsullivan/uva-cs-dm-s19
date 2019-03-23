
theorem same{P: Prop}: (¬P) = (P → false) := rfl

theorem zneqo : 0 ≠ 1.
#check zneqo

theorem zneqoeqzneqo : (0 ≠ 1) = ¬(0 = 1) := rfl

theorem zneqo' : 0 = 1 → false := 
    λ h : (0 = 1), 
        nat.no_confusion h

theorem zneqo'' : ¬ 0 = 1 := 
begin
    assume h : (0 = 1),
    show false,
    from nat.no_confusion h
end

theorem ttneqff : ¬tt = ff := 
begin
    assume h : (tt = ff),
    show false,
    from bool.no_confusion h
end

theorem ttneqff' : tt ≠ ff.

theorem ex2 : 2 ≠ 1.

theorem proof_by_negation : ∀(P : Prop),
    (P → false) → ¬P :=
        λ P p, p

lemma zneqo''': ¬(0 = 1) :=
begin
    apply proof_by_negation,
    assume h: (0 = 1),
    show false,
    from (nat.no_confusion h)
end

theorem qAndNotQfalse{P Q: Prop}
  (pf: Q ∧ ¬Q): false := 
    pf.right pf.left

theorem no_contra : 
∀(Q: Prop), ¬(Q ∧ ¬Q) :=
    λ (Q : Prop) (pf : Q ∧ ¬Q), 
        pf.right pf.left

theorem ncab{a b: nat}: ¬((a = b) ∧ (a ≠ b)) :=
begin
    apply no_contra
end

theorem ncab'{a b: nat}: ¬((a = b) ∧ (a ≠ b)) :=
begin
  assume c : ((a = b) ∧ (a ≠ b)),
  have pf_eq := c.left,
  have pf_neq := c.right,
  have f := pf_neq pf_eq,
  assumption
end

-- classical logic
axiom em: ∀(P: Prop), P ∨ ¬P

example: ¬¬true :=
begin
  sorry
end

theorem double_neg_elim: ∀{P: Prop}, ¬¬P → P := 
begin
  assume P : Prop,
  assume pfNotNotP : ¬¬P,
  cases (em P) with pf_P pf_not_P,
    show P, from pf_P,

    have f: false := pfNotNotP pf_not_P,
    exact false.elim f
end

theorem prove_P: ∀{P: Prop}, ¬¬P → P :=
  λ(P)(pf_not_not_P),
    double_neg_elim pf_not_not_P

theorem proof_by_contradiction : ∀(P : Prop),
  (¬P → false) → P := 
    @double_neg_elim

theorem zeqz : 0 = 0 :=
begin
  apply proof_by_contradiction,
  assume pf: 0 = 0 → false,
  show false,
  from pf (eq.refl 0)
end

example{P Q: Prop} 
  (pf: ¬P → (Q ∧ ¬ Q)): P :=
begin
  apply proof_by_contradiction,
  assume notP: ¬P,
  have contra := (pf notP),
  show false,
  from no_contra Q contra
end

theorem proof_by_contrapositive: 
  ∀(P Q : Prop), (¬Q → ¬P) → (P → Q) :=
begin
  assume P Q: Prop,
  assume pf_not_Q_to_not_P: (¬Q → ¬P),
  assume pf_P : P,
  have pf_not_Q_to_false: ¬Q → false :=
    λ(pf_not_Q: ¬Q),
      no_contra P (and.intro pf_P (pf_not_Q_to_not_P pf_not_Q)),
  have pf_not_not_Q: ¬¬Q := pf_not_Q_to_false,
  show Q,
  from double_neg_elim pf_not_not_Q
end

theorem proof_by_contrapositive': 
  ∀(P Q : Prop), (¬Q → ¬P) → (P → Q) :=
begin
  assume P Q,
  assume pf_not_Q_to_not_P: (¬Q → ¬P),
  assume pf_P : P,
  have pf_not_Q_to_false: ¬Q → false :=
    begin
      assume pf_not_Q,
      have pf_not_P := pf_not_Q_to_not_P pf_not_Q,
      exact pf_not_P pf_P
    end,
  have pf_not_not_Q: ¬¬Q := pf_not_Q_to_false,
  show Q,
  from double_neg_elim pf_not_not_Q
end

theorem proof_by_contrapositive'': 
  ∀(P Q : Prop), (¬Q → ¬P) → (P → Q) :=
begin
  assume P Q,
  assume pf_not_Q_to_not_P: (¬Q → ¬P),
  assume pf_P : P,
  cases (em Q) with pf_Q pf_not_Q,
    -- Q
    assumption,
    -- ¬Q
    have pf_not_P := pf_not_Q_to_not_P pf_not_Q,
    exact false.elim (pf_not_P pf_P)
end

theorem zeqz' : 0 = 0 → true :=
begin
  apply proof_by_contrapositive,
  assume nt : ¬true,
  have pff := nt true.intro,
  show ¬ 0 = 0,
  from false.elim pff
end

