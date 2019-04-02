
/-
Conjunctions, disjunctions, implication, iff,
negation
-/

/-
1. Prove that 3 + 3 = 6 and 2 + 6 = 8 implies
that 1 + 1 = 2.
-/

-- answer:

/-
2. Prove that 2 + 5 = 3 or 9 + 1 = 5 implies
that 2 + 3 = 9.
-/

-- answer:

/-
3. Prove that ¬(A ∧ B ∧ C) ↔ (¬A ∨ ¬B ∨ ¬C).
You may use the axiom of the excluded middle.
-/

axiom em: ∀(P: Prop), P ∨ ¬P

-- answer:

/-
4. Prove that ¬(A ∨ B ∨ C) ↔ (¬A ∧ ¬B ∧ ¬C).
You may *NOT* use the axiom of the excluded middle.
-/

-- answer:

/-
5a. Prove that ¬(A ∨ ¬B) ↔ (¬A ∧ B).
You may use the axiom of the excluded middle.
-/

-- answer:

/-
5b. Prove that ¬(A ∧ ¬B) ↔ (¬A ∨ B).
You may use the axiom of the excluded middle.
-/

-- answer:

/-
6. Prove that ¬P ∨ ¬Q ∨ R is true if and only
if P → Q → R. You may use the axiom of the
excluded middle.
-/

-- answer:

/-
7. Prove that ¬¬¬P → ¬P. You may use the axiom
of the excluded middle.
-/

-- answer:

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

/-
8b. (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) ∧ (¬P ∨ ¬Q)
-/

-- answer:

/-
8c. (P ∨ Q ∨ R) ∧ (¬P ∨ Q ∨ R) ∧
     (P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ ¬Q ∨ ¬R)
-/

-- answer:

/-
9. Prove that exists a number such that
it is both even and a multiple of 3.
Use the supplied definitions of even and prime.
-/

def isEven(n: ℕ) := (∃(m: ℕ), m * 2 = n)

def isMult3(n: ℕ) := (∃(m: ℕ), m * 3 = n)

-- answer

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

