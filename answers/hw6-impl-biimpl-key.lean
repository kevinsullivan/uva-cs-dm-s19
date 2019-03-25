/-
Grading rubric. 10 points per question. Partial
credit on sub-part basis.

 NOTE: There are many ways to write these proofs.
 We give you examples that show you particularly 
 good ways to write them. But we'll take any proof
 that Lean accepts.
-/

/-
Read and reread the chapters on implication and
bi-implication. Be sure to understand that a proof
of an implication is a function from proofs of the
premise to proofs of the conclusion, and that you
use such a function by applying it to a proof of a
premise to derive a proof of a conclusion. To build
your understanding, prove each of the following 
conjectures using first a tactic script and then 
in term-style.
-/

/- 1. -/
example : ∀ (P Q : Prop), P → Q → P ∧ Q :=
begin
intros P Q,
assume p q,
exact and.intro p q,
end


example : ∀ (P Q : Prop), P → Q → P ∧ Q :=
λ P Q,
    λ p q, 
        and.intro p q

/- 2. -/
example : ∀ (P Q R : Prop), (P ∧ Q) → R → (P ∧ R) :=
begin
intros P Q R,
assume pq r,
exact and.intro pq.left r
end



example : ∀ (P Q R : Prop), (P ∧ Q) → R → (P ∧ R) :=
λ P Q R pq r,
    and.intro pq.left r


/- 3. -/
example : ∀ (P Q R : Prop), (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
intros P Q R,
assume pq qr,
have p := pq.left,
have r := qr.right,
exact ⟨ p, r ⟩
end


example : ∀ (P Q R : Prop), (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
λ P Q R pq qr,
   let p := pq.left in
   let r := qr.right in
   ⟨ p, r ⟩ 

/- 4. -/
theorem and_comm' : 
    ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
λ P Q,
    let f :=  
        λ pq : P ∧ Q, and.intro pq.right pq.left in
    let b := 
        λ pq : Q ∧ P, and.intro pq.right pq.left in
    iff.intro f b



theorem and_comm'' : 
    ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
begin
intros P Q,
apply (iff.intro _ _),
exact λ pq : P ∧ Q, and.intro pq.right pq.left,
exact λ pq : Q ∧ P, and.intro pq.right pq.left,
end


/- 5. -/
example : ∀ (P : Prop), P ∧ false → 0 = 1 :=
begin
intro P, 
assume h,
exact false.elim h.right,
end


example : ∀ (P : Prop), P ∧ false → 0 = 1 :=
λ P h, false.elim h.right


/- 6. -/
example : ∀ (P : Prop), true ∧ P → P :=
λ P h, h.right


example : ∀ (P : Prop), true ∧ P → P :=
begin
intro P,
assume h,
exact h.right
end


/- 7. Try using the rw tactic. -/
example : ∀ (n m k : ℕ), n = m → m = k → n = k :=
begin
intros n m k,
assume nm mk,
rw nm,
rw mk,
end

-- Here's another version

example : ∀ (n m k : ℕ), n = m → m = k → n = k :=
begin
intros n m k,
assume nm mk,
exact eq.subst mk nm,
end


example : ∀ (n m k : ℕ), n = m → m = k → n = k :=
λ n m k nm mk,
    eq.subst mk nm


/- 8. -/
example : ∀ (s t : string), s = t ↔ t = s :=
λ s t, 
iff.intro 
    (λ st, eq.symm st)
    (λ ts, eq.symm ts)


example : ∀ (s t : string), s = t ↔ t = s :=
begin
intros s t,
apply iff.intro _ _, -- underscores can be omitted
exact λ st, eq.symm st,
exact λ ts, eq.symm ts,
end



/- 9. -/
example : 
    ∀ (T : Type) (t1 t2 : T) (P : T → Prop),
        P t1 ∧ t1 = t2 → P t2 :=
λ T t1 t2 P h,
    eq.subst h.right h.left


example : 
    ∀ (T : Type) (t1 t2 : T) (P : T → Prop),
        P t1 ∧ t1 = t2 → P t2 :=
begin
intros T t1 t2 P,
assume h,
exact eq.subst h.right h.left
end


/- 10. -/
theorem and_assoc' : 
    ∀ (P Q R : Prop), 
        P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
begin
intros P Q R,
apply iff.intro,
assume pqr,
exact and.intro 
            (and.intro pqr.left pqr.right.left) pqr.right.right,
assume h,
exact and.intro h.left.left 
      (and.intro h.left.right h.right)
end


theorem and_assoc'' : 
    ∀ (P Q R : Prop), 
        P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
λ P Q R,
    iff.intro
        (λ h,
            and.intro 
            (and.intro h.left h.right.left) h.right.right)
        (λ h, and.intro h.left.left 
      (and.intro h.left.right h.right))