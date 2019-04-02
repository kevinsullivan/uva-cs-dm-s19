
/-
Introduction rule requires a witness where a predicate
can be proven to be true for that witness
-/
def existsIntro 
  (T: Type) 
  (pred: T → Prop) 
  (witness : T) 
  (proof : pred witness) 
  : ∃(w: T), pred w
  := exists.intro witness proof

example{T: Type}{witness: T}
  {predicate: T → Prop}
  {proof: predicate witness}:
  ∃ m, predicate m := 
    ⟨ witness, proof ⟩

def isEven(n : nat) : Prop :=
  ∃(m : nat), m + m = n

lemma pf8is4twice: 4 + 4 = 8 := rfl

theorem even8: isEven 8 :=
  exists.intro 4 pf8is4twice

theorem even8': ∃(m : nat), m + m = 8 :=
  exists.intro 4 pf8is4twice

theorem even8'': isEven 8 := 
  ⟨ 4, pf8is4twice ⟩ 

theorem even8''' : isEven 8 := 
begin
  unfold isEven, -- not necessary
  exact ⟨ 4, pf8is4twice ⟩ 
end 

theorem isNonZ : exists n : nat, 0 ≠ n :=
  exists.intro 1 (λ pf : (0 = 1), 
    nat.no_confusion pf)

theorem isNonZ' : exists n : nat, 0 ≠ n :=
begin
  have pf0isnt1: (0 ≠ 1),
    apply nat.no_confusion,
    
  exact ⟨ 1, pf0isnt1 ⟩,
end

theorem isNonZ'' : exists n : nat, 0 ≠ n :=
begin
  have pf0isnt1: (0 ≠ 1) :=
  begin
    apply nat.no_confusion,
  end,
    
  exact ⟨ 1, pf0isnt1 ⟩,
end

def existsElim 
  { Q : Prop }
  { T : Type } 
  { P : T → Prop }
  ( ex : exists x, P x) 
  ( pw2q : ∀ a : T, P a → Q) 
  : Q
  := exists.elim ex pw2q

theorem forgetAProperty'{P S: ℕ → Prop}: 
  (∃ n, P n ∧ S n) → (∃ n, P n) :=
   -- here Q, the conclusion, is
   -- (exists n, P n)
begin
  assume ex,
  apply exists.elim ex,
  assume w Pw,
  exact ⟨w, Pw.left⟩,
end

theorem forgetAProperty{P S: ℕ → Prop}: 
  (∃ n, P n ∧ S n) → (∃ n, P n) :=
   -- here Q, the conclusion, is (exists n, P n)
begin
  assume ex,
  show ∃ (n : ℕ), P n,
  from
    begin
      apply exists.elim ex, -- give one arg, build other
      assume w Pw, -- assume w and proof of P w
      show ∃ (n : ℕ), P n,
      from exists.intro w Pw.left,
    end,
end

example: ∀(P Q: Prop), P → Q → P ∧ Q
:= begin
  assume P Q,
  assume pfP pfQ,
  exact ⟨pfP, pfQ⟩, 
end

theorem reverseProperty{P S: ℕ → Prop}: 
  (∃ n, P n ∧ S n) → (∃ n, S n ∧ P n) :=
begin
  assume ex,
  apply exists.elim ex,
  assume w Pw,
  have pfWReverse: S w ∧ P w :=
    and.intro Pw.right Pw.left,
  exact exists.intro w pfWReverse,
end

theorem reverseProperty'{P S: ℕ → Prop}: 
  (∃ n, P n ∧ S n) → (∃ n, S n ∧ P n) :=
begin
  assume ex,
  apply exists.elim ex,
  assume w Pw,
  apply exists.intro w,
  exact and.intro Pw.right Pw.left,
end

theorem reverseProperty''{P S: ℕ → Prop}: 
  (∃ n, P n ∧ S n) → (∃ n, S n ∧ P n) :=
begin
  assume ex,
  have pfw2q: ∀(w : ℕ), P w ∧ S w →
     (∃ (n : ℕ), S n ∧ P n) :=
  begin
    assume w Pw,
    have pfWReverse: S w ∧ P w :=
      and.intro Pw.right Pw.left,
    exact ⟨w, pfWReverse⟩,
  end,
  exact exists.elim ex pfw2q,
end

def isASquare: ℕ → Prop :=
  λ n, exists m, n = m ^ 2

def isASquare'(n: ℕ) :=
  ∃ m, n = m ^ 2

theorem isPS9 : isASquare 9 :=
begin
  unfold isASquare,
  exact exists.intro 3 (eq.refl 9),
end

axiom mypred: ℕ → Prop
#reduce (λ n, mypred n) 3

theorem not_exists_t_iff_always_not_t
  {T: Type}{pred: (T → Prop)}:
    (¬(∃ t: T, pred(t))) ↔
      ∀ t: T, ¬pred(t) :=
begin
  apply iff.intro,
    -- ¬(∃ t: T, pred(t)) → ∀ t: T, ¬pred(t)
    assume pf_not_exists_t,
    assume t,
    assume Q,
    have pf_exists_t := exists.intro t Q,
    contradiction,

    -- ∀ t: T, ¬pred(t) → ¬(∃ t: T, pred(t))
    assume pf_forall_t_not,
    assume pf_exists_t,
    apply exists.elim pf_exists_t,
    assume w,
    assume pf_w,
    have pf_not_w := pf_forall_t_not w,
    contradiction,
end

example: ∃(P Q: Prop),
  (P ∨ Q) ∧ (¬P ∨ ¬Q) :=
begin
  apply exists.intro true,
  apply exists.intro false,
  have pf_not_f := λ(f: false), f,
  have pf_not_t_or_not_f :=
    or.intro_right (¬true) pf_not_f,
  have pf_t_or_f :=
    or.intro_left false true.intro,
  have pf_t_or_f' : true ∨ false :=
    or.inl true.intro,
  exact and.intro pf_t_or_f pf_not_t_or_not_f,
end

example: ∃(P Q: Prop), 
  (P ∨ Q) ∧ (¬P ∨ ¬Q) ∧ (¬P ∨ Q) :=
begin
  apply exists.intro false,
  apply exists.intro true,
  split,
    -- P ∨ Q
    exact or.inr true.intro,
    split,
      -- ¬P ∨ ¬Q
      apply or.inl,
      assume f,
      assumption,
      -- ¬P ∨ Q
      apply or.inr,
      exact true.intro,
end

example: ¬(∃(P Q: Prop), 
  (P ∨ Q) ∧ (¬P ∨ ¬Q) ∧ (¬P ∨ Q) ∧ (¬Q)) :=
begin
  assume pf_exists,
  apply exists.elim pf_exists,
  assume P pw',
  apply exists.elim pw',
  assume Q pw,
  have pf_not_q := pw.right.right.right,
  have pf_not_p_or_q := pw.right.right.left,
  cases pf_not_p_or_q with pf_not_p pf_q,
    -- ¬P
    have pf_p_or_q := pw.left,
    cases pf_p_or_q with pf_p pf_q,
      -- P
      contradiction,
      -- Q
      contradiction,
    -- Q
    contradiction,
end

example: ∃(P Q R: Prop), 
  (P ∨ Q ∨ R) ∧ (¬P ∨ ¬Q ∨ ¬R) ∧
    (¬P ∨ Q ∨ R) ∧ (¬Q ∨ ¬R) := 
begin
  apply exists.intro false,
  apply exists.intro true,
  apply exists.intro false,
  split,
    -- P ∨ Q ∨ R
    exact or.inr (or.inl true.intro),
    have f := λ(f: false), f, 
    split,
      -- ¬P ∨ ¬Q ∨ ¬R
      exact or.inl f,
      split,
        -- ¬P ∨ Q ∨ R
        exact or.inl f,
        -- ¬Q ∨ ¬R
        exact or.inr f,
end

example: ∀(T: Type)(pred: T → Prop),
  ¬(∃(t: T), pred t) ↔
    ∀(t: T), ¬(pred t) :=
begin
  intros,
  split,
    -- forward
    assume pf_notexists,
    assume t,
    assume pf_predt,
    have pf_exists := exists.intro t pf_predt,
    contradiction,
    -- backward
    assume pf_forall,
    assume pf_exists,
    apply exists.elim pf_exists,
    assume w pw,
    have pf_npredw := pf_forall w,
    contradiction,
end

axiom em: ∀(P: Prop), P ∨ ¬P

example: ∀(T: Type)(pred: T → Prop),
  ¬(∀(t: T), pred t) ↔
    ∃(t: T), ¬(pred t) :=
begin
  intros,
  split,
    -- forward
    assume pf_notforall,
    cases (em (∃ (t : T), ¬pred t)) with
        pf_exists pf_notexists,
      -- exists
      assumption,
      -- doesn't exist
      have pf_forall_doubleneg: ∀(t: T), ¬¬(pred t) :=
      begin
        assume t,
        assume pf_neg,
        have pf_exists := exists.intro t pf_neg,
        contradiction,
      end,
      have pf_forall: ∀(t: T), pred t :=
      begin
        assume t,
        have pf_doubleneg := pf_forall_doubleneg t,
        cases (em (pred t)) with pf_pred pf_npred,
          -- pred t
          assumption,
          -- ¬pred t
          contradiction,
      end,
     contradiction,
    -- backward
    assume pf_existsnot,
    assume pf_forall,
    apply exists.elim pf_existsnot,
    assume w pw,
    have pf_predw := pf_forall w,
    contradiction,
end
