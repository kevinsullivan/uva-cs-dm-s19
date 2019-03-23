/-
Read, and if you have already read, then re-read, the 
chapters in the notes on proofs of disjunctions and negations. 
We have added some new material, especially under negation
elimination.

In proofs of bi-implications, use comments to mark the start of
the proofs of the implications in each direction. Label one as
"forward" the other other as "backward."

The collaboration policy for this homework is "no collaboration
allowed." You may study and discuss the underlying concepts with
anyone.

You may provide proofs in the style of your choice: term-style,
tactic style, or mixed. Yes, you can using tactic scripts within
terms and terms within tactic scripts. You may use any tactics 
you know of. As a courtesy, we provide begin/end pairs, in case
you should want to use them. Otherwise you may delete them.
-/

/- 
1. 15 points
-/
example : ∀ (P Q : Prop), P ∧ Q → P ∨ Q :=
begin
end


/-
2. 15 points
-/
example : 
    ∀ (P Q R : Prop), (P ∨ Q) → (Q ∨ R) → ¬ Q → (P ∧ R) :=
begin
end 

/-
3. 15 points
-/
example : 
    ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
end


/-
4. 10 points
-/

example : ∀ (P Q R : Prop), P → Q → R → ¬ Q → (Q ∨ ¬ Q) :=
begin
end

open classical      -- hint: you can now use em easily

/-
4a. 5 points. Write *your own* proof of this conjecture.
-/

example : ∀ (P Q : Prop), ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
end

/-
4b. 5 points. Is this theorem classically true in neither, one, or
both directions. Explain your answer in relation to your proof. 

Answer: 
-/

/-
5. 5 points. Write *your own proof* of this conjecture.
-/
example : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) :=
begin
end


/-
6. 10 points
-/

example : ∀ (P : Prop), (¬ ¬ P → P) ↔ (P ∨ ¬ P) :=
begin
end


/-
7. 5 points

Tranlate the preceding proposition into English,
referring explicitly to the principles of negation 
elimination and excluded middle. Write your sentence
here:

-/


/-
8. [10 points]
-/

example : 
    (∀ ( P Q : Prop ), (P → Q) ↔ (¬ Q → ¬ P)) → 
        ∀ (Raining Wet : Prop), (¬ Wet → ¬ Raining) → 
            (Raining → Wet) :=
begin
end


/-
9. [5 points]

What is the name of the principle expressed by the
premise, (P → Q) ↔ (¬ Q → ¬ P)), in the preceding
problem? Answer here:


-/