
/-
POINTS: Welcome to the first CS2102 exam. The exam has 12 
questions. Points for each question are as indicated, for a
total of 100 points.

READ CAREFULLY: If you are unable to answer a question in 
a way that Lean accepts as syntactically correct, *comment 
out your malformed answer*. Otherwise an error in your answer 
can cause Lean not to recognize correct answers to other 
questions. If you are sure an answer is correct but Lean is
not accepting it, look for problems in the preceding logic.

Do not change or delete any of the questions.

WHAT TO DO: Complete the exam by following the instructions 
for each question. Save your file then upload the completed 
and saved file to Collab. You have 75 minutes from the start 
of the exam to the time where it must be uploaded to Collab.

OPEN NOTES: You may use the class notes for this exam, whether
provided to you by the instructors or taken by you (or for you).

STRICTLY INDIVIDUAL EFFORT: This is a strictly individual exam,
taken under the honor system. Do not communicate with anyone except
for the instructor about the content of this exam, by any means,
until you are sure that each person you are communicating with 
has already completed the test.
-/

/- 1. (5 points)
What is the type of function1 (just below)? Give you answer by
replacing the hole (underscore) in the subsequent definition 
with your answer.
-/

def function1 (f: ℕ → ℕ) (g: ℕ → ℕ) := 
  λ (x: ℕ), 3

#check function1

def function1_type : Type := 
  (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ






/- 2. (10 points)
Define three equivalent functions, called product1, 
product2, and product3. Each must take two natural 
numbers as its arguments and return their product.  
Define the first version using C-style notation, 
the second using a lambda abstraction, and the third
using a tactic script.
-/

-- Answer below:

-- ANSWER

-- C-style here

def product1 (n m : ℕ) : ℕ := n * m


-- Lambda abstraction here
def product2: ℕ → ℕ → ℕ :=
λ n m, n * m


-- Tactic script here
def product3: ℕ → ℕ → ℕ :=
begin
intros n m,
exact n * m,
end




/- 3. (5 points)

Given the definition of product1, what function 
is (product1 5)? Answer by replacing the hole in 
the following definition with a lambda abstraction.
-/

def product1_5 := λ m, 5 * m





/- 4. (5 points)
Which of the following properties does "product1_5" have?
Answer by placing a Y (for yes, it has this property), or
N (for no, it doesn't have this property), BEFORE the name
of each property, just after the dash.


-- ANSWER 

- Y injective
- N surjective
- N one-to-many
- N strictly partial
- N bijective
-/





/- 5. (5 points)
Complete the  proof of the following conjecture, that
(product1 4 6) = 24. Fill in the proposition to be
proved in the first hole (underscore) and a proof in
the second hole.
-/

-- ANSWER 
example : (product1 4 6) = 24 := rfl



/- 6. (10 points)
State and prove the proposition that, for any natural 
numbers, a, b, and c, if b = a, then if c = b, then a = c.
Fill in the holes in the following example accordingly, 
replacing the underscores first with a formal statement 
of the proposition, and then a proof of it, respectively.
-/

-- Complete  by replacing the hole with a proof:
example: ∀ a b c: ℕ, b = a → c = b → a = c := 
begin
intros a b c,
assume ba cb,
have ab := eq.symm ba,
have bc := eq.symm cb,
exact eq.trans ab bc
end






/- 7. (10 points)
In the context of the following assumptions, use
"example" to formally state and prove the proposition
that "Jane is nice."
-/

axiom Person : Type
axioms Jill Jane : Person
axiom IsNice : Person → Prop
axiom JillIsNice : IsNice Jill
axiom JillIsJane : Jill = Jane

-- Fill in the holes with your proposition and proof
example : IsNice Jane := 
    eq.subst JillIsJane JillIsNice


/- 8. (10 points)
Use "example" to prove that true ∧ true is true.  Give two proofs, the first using a term-style 
proof, the second using a tactic script.
-/

-- Your answers here

-- either one of the following would be ok

example : true ∧ true → true :=
λ tt, tt.left 

example : true ∧ true :=
and.intro true.intro true.intro



/- 9. (10 points)
Define a function, called exfalso, that takes a proof 
of false as an argument, and that returns a proof of 
3 = 7 as a result.
-/

-- ANSWER

def exfalse (f : false) : 3 = 7 := false.elim f


/- 10. (10 points)
Formally state and prove the proposition, 
that, for any propositions, A, B, and C, 
A ∧ B ∧ C → C ∧ A ∧ B. You may write the
proof in any style you wish. One way to do it 
would be to define a function that takes the
propositions, A, B, and C, and a proof of the 
premise as its arguments and that returns a 
proof of the conclusion as a result. You 
might also use a tactic script. 
-/

-- ANSWER 

example : ∀ A B C : Prop, A ∧ B ∧ C → C ∧ A ∧ B :=
begin
intros A B C,
assume h,
have a := h.left,
have bc := h.right,
have b := bc.left,
have c := bc.right,
have ab := and.intro a b,
exact and.intro c ab,
end




/- 11. (10 points)
Formally (in Lean), prove that if A, B, and C
are any propositions, and if C is true, then 
A ∧ B ∧ C → B ∧ A.
-/

-- Complete the following by replacing _ with a proof:
example: ∀(A B C: Prop), C → (A ∧ B ∧ C → B ∧ A) :=
begin
intros A B C,
assume c,
assume abc,
have a := abc.left,
have b := abc.right.left,
exact and.intro b a,
end






/- 12. (10 points)

Define a predicate, gt5, that is true for all and only for
natural numbers greater than 5. You may use the expression,
n > 5, in your answer. Then fill in the hole in the following
definition with the type of the term (gt5 4).
-/

-- ANSWER
def gt5 : ℕ → Prop := 
λ n, n > 5



-- ANSWER
#check gt5 4

def type_of_gt5_4 := Prop



/- 13. EXTRA CREDIT 5 points

Give brief natural-language (in English) rendition
of the following formal propositions.

∃ n, m : ℕ, isPrime n ∧ isPrime m ∧ m = n + 2

Answer: There are natural numbers, n and m, such that both
n and m are prime and m is just two larger than n. (Note: 
such a pair of prime numbers is called a "prime pair" in
the mathematical literature.)

If by isPrime we mean the ordinary concept of primeness 
from basic arithmetic, then the second proposition is true.
Prove it by giving values for n and m that satisfy the 
predicate along with a very brief argument that the two
numbers do actually satisfy the predicate.

Answer: 

n = 5
m = 7

Argument: Both 5 and 7 are prime (obvious) and 7 is two larger
than 5 (also trivial).


-/
