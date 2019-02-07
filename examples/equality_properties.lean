example: ∀ (P Q R: Prop), (P → Q → R) → (P ∧ Q → R) :=
begin
  assume P Q R,
  assume pfPimpQimpR,
  assume pfPandQ,
  have pfQimpR := pfPimpQimpR pfPandQ.1,
  exact pfQimpR pfPandQ.2,
end

example: ∀ (P Q R: Prop),  (P ∧ Q → R) → (P → Q → R) :=
begin
  assume P Q R,
  assume pfPandQimpR,
  assume pfP,
  assume pfQ,
  have pfPandQ := and.intro pfP pfQ,
  exact pfPandQimpR pfPandQ,
end

example: ∀ (P Q R: Prop), (P → Q → R) ↔ (P ∧ Q → R) :=
begin
  assume P Q R,
  split,
    -- (P → Q → R) → (P ∧ Q → R)
    assume pfPimpQimpR,
    assume pfPandQ,
    have pfQimpR := pfPimpQimpR pfPandQ.1,
    exact pfQimpR pfPandQ.2,
    -- (P ∧ Q → R) → (P → Q → R)
    assume pfPandQimpR,
    assume pfP,
    assume pfQ,
    have pfPandQ := and.intro pfP pfQ,
    exact pfPandQimpR pfPandQ,
end

#reduce 3 - 1

axioms A B C: Prop
#check A → (B → C)
#check (A → B) → C

def sameParity(a b: ℕ): Prop :=
  (a % 2) = (b % 2)

example: 1 = 1 := 
begin
  exact rfl,
end

example: ∀(x: ℕ), (sameParity x x) :=
begin
  intros,
  unfold sameParity,
end

example: ∀(x y: ℕ), (sameParity x y) ↔ (sameParity y x) :=
begin
  intros,
  split,
    -- case sameParity x y → sameParity y x
    assume pfSameParityXY,
    unfold sameParity at *,
    rewrite pfSameParityXY,

    -- case sameParity y x → sameParity x y
    assume pfSameParityYX,
    unfold sameParity at *,
    rewrite pfSameParityYX,
end

example: ∀(x y z: ℕ), (sameParity x y) ∧ (sameParity y z) → 
  (sameParity x z) :=
begin
  assume x y z,
  assume pfSameParityXYandSameParityYZ,
  have pfSameParityXY := 
    and.elim_left pfSameParityXYandSameParityYZ,
  have pfSameParityYZ := pfSameParityXYandSameParityYZ.2,
  unfold sameParity,
  unfold sameParity at pfSameParityXY,
  unfold sameParity at pfSameParityYZ,
  rewrite pfSameParityXY,
  assumption,
end