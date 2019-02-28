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
_


example : ∀ (P Q : Prop), P → Q → P ∧ Q :=
_ 

/- 2. -/
example : ∀ (P Q R : Prop), (P ∧ Q) → R → (P ∧ R) :=
_


example : ∀ (P Q R : Prop), (P ∧ Q) → R → (P ∧ R) :=
_


/- 3. -/
example : ∀ (P Q R : Prop), (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
_


example : ∀ (P Q R : Prop), (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
_

/- 4. -/
theorem and_comm' : 
    ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
_


theorem and_comm'' : 
    ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
_


/- 5. -/
example : ∀ (P : Prop), P ∧ false → 0 = 1 :=
_


example : ∀ (P : Prop), P ∧ false → 0 = 1 :=
_


/- 6. -/
example : ∀ (P : Prop), true ∧ P → P :=
_


example : ∀ (P : Prop), true ∧ P → P :=
_


/- 7. Try using the rw tactic. -/
example : ∀ (n m k : ℕ), n = m → m = k → n = k :=
_


example : ∀ (n m k : ℕ), n = m → m = k → n = k :=
_


/- 8. -/
example : ∀ (s t : string), s = t ↔ t = s :=
_


example : ∀ (s t : string), s = t ↔ t = s :=
_


/- 9. -/
example : 
    ∀ (T : Type) (t1 t2 : T) (P : T → Prop),
        P t1 ∧ t1 = t2 → P t2 :=
_


example : 
    ∀ (T : Type) (t1 t2 : T) (P : T → Prop),
        P t1 ∧ t1 = t2 → P t2 :=

_


/- 10. -/
theorem and_assoc' : 
    ∀ (P Q R : Prop), 
        P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
_


theorem and_assoc'' : 
    ∀ (P Q R : Prop), 
        P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
_