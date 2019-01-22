/-
Copyright 2019 Kevin Sullivan and Ben Hocking. 
-/


/-
Every term has exactly one type in Lean.
-/
namespace Types.ex1
#check 2
#check 2 + 2
def x : nat := 2
#check x
#check tt
#check "Hello, Lean!"
#check "Hello, " ++ "Lean!"
end Types.ex1



/-
All terms are type checked for type correctness. The following code does not type check.
-/
namespace Types.ex2
def x : nat := "Hello, Lean!"   -- type error
#check "Hello, Lean!" + 3       -- type error
end Types.ex2



/-
Proof checking in Lean is done by type checking. Propositions are types. Proofs are values of these types. If a variable is defined to be of type P, where P is a proposition, then the only kind of proof that can be bound to that variable is a proof term (a value) of type P. You can see a proof checking error in this code.
-/
namespace Types.ex3
axioms (P Q : Prop) (p : P) (q : Q)
def pf_P  : P := p
def pf_P' : P := q
end Types.ex3



/-
You can define your own types in Lean. We will get into this topic in detail later in the course. Each type comes with its own namespace, with the same name as the type itself. If you want to refer to constructors of a type without writing the type name as a namespace prefix, you can "open" the namespace.
-/
namespace Types.ex4
inductive day : Type
| Sunday : day
| Monday : day
| Tuesday : day
| Wednesday : day
| Thursday : day
| Friday : day
| Saturday : day

#check day.Monday
open day
#check Monday
end Types.ex4



/-
Types are terms so they too have types. There are two "sorts" of types in Lean: logical types are propositions; computational types are for programming. Computation types include basic data types as well as function types. You can see here that function types are all of type  "Type".
-/
namespace Types.ex5a
-- computational data types
#check nat
#check string
#check bool

-- computational function types
#check nat → nat
#check string → nat
#check string → bool
end Types.ex5a




/-
And all propostions are of type, "Prop".
-/
namespace Types.ex5b
#check true
#check false
#check 0 = 1

axioms P Q : Prop
#check P
#check Q
#check P ∧ Q
#check P ∨ Q
#check P → Q
#check ¬ P
end Types.ex5b



/-
Proofs really are just values (terms) of their corresponding types.
-/
namespace Terms.ex8
axioms (P : Prop) (p : P)
example : P := p
end Terms.ex8
