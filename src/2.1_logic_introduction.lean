/-
Copyright 2019 Kevin Sullivan and Ben Hocking.  
-/

/-
Inference rules. Introduction rules construct proofs that you don't yet have. Elimination rules extract information from proofs that you already have.
-/
namespace Introduction.ex1
-- introduction: construct a proof
def construct_a_proof
(P Q : Prop)
(p : P)
(q : Q)
: P ∧ Q
:= and.intro p q

-- elimination: use a proof
def use_a_proof
(P Q : Prop)
(p_and_q : P ∧ Q)
: P
:= and.elim_left p_and_q
end Introduction.ex1


/-
Binding of names to values and the evaluation of names that are already bound to values. Names can be bound to values only once. There are no "variables" (no "mutable state") in Lean.
-/
namespace Introduction.ex2
def x : nat := 5  -- bind the name x to the value, 5
#check x          -- the type of the term x is now nat
#reduce x         -- evaluating x yields the value 5
def x := 6        -- we cannot bind a new value to x
end Introduction.ex2


-- Function application expressions and evaluation
#reduce 3 * 4



/-
Terms have types, too.
-/
#check 3
#check 3 * 4



/-
Lean is stronly and statically typed. It will issue an error for the following code.
-/
#check 3 * "Hello, Lean!"



  /-
 Lean does type inference. Type inference means that you can leave out explicit type declarations in cases where Lean can figure out what the types must be from context.
  -/
namespace Introduction.ex3
def x : nat := (1 : nat)
def x' : nat := 1
def x'' := 1
#check x
#check x'
#check x''
end Introduction.ex3



/-
All terms in Lean have types.
-/
#check tt
#check ff
#check "Hello, Lean!"



/-
Types are values (terms) too
-/
#check nat
#check bool
#check string


/-
You can check out the entire type hierarchy yourself.
-/
#check 3
#check nat
#check Type
#check Type 0
#check Type 1



/-
Propositions are types and proofs are values of these types. This principle is the basis for automated proof checking in Lean and in other constructive logic proof assistants such as Coq and Agda.
-/
namespace Introduction.ex4
def p : true := true.intro
end Introduction.ex4



/-
Lean rejects proof terms that do not type check, just as it rejects ordinary computational values that do not typecheck, as illustrated in the example above. You will thus see an error in the following code.
-/
namespace Introduction.ex5
def p : false := true.intro
end Introduction.ex5



/-
A formalized rendition of the famous example in which it is deduced that Socrates is mortal. You are not expected to fully understand this code at this point.
-/
namespace Introduction.ex6
def modus_ponens
    (α : Type)
    (M : α → Prop)
    (h : ∀ a : α, M a)
    (w : α)
    : (M w)
    := (h w)

axiom Person : Type
axiom Mortal : Person → Prop
axiom EveryoneIsMortal : ∀ p : Person, Mortal p
axiom Socrates : Person

theorem aProof : Mortal Socrates :=
    modus_ponens Person Mortal EveryoneIsMortal Socrates
end Introduction.ex6