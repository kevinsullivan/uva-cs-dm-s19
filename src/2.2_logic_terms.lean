/-
Copyright 2019 Kevin Sullivan and Ben Hocking. 
-/

/-
Literal terms
-/
#eval 1
#eval tt
#eval "Hello, Lean!"



/-
Identifier terms
-/
namespace Terms.ex2
def x := 1
def y := 1 + 1
#eval x
#eval y
end Terms.ex2



/-
Lambda abstract terms: a special case of literal terms. Lambda abstractions are literal terms that represent total functions. Lambda abstractions are often called anonymous functions. We can bind a name to a lambda abstraction, as in the following example.
-/
namespace Terms.ex3
#reduce (λ n : ℕ, n + 1)
#eval (λ n : ℕ, n + 1) 5
def f := (λ n : ℕ, n + 1)
#eval f 5
end Terms.ex3


/-
Lean provides C-style notations for defining named lambda abstractions.  Here's exactly the same function defined using C-style notation.
-/
namespace Terms.ex4
def f (n : ℕ) : ℕ :=  n + 1
#eval f                     -- it's the same function
#eval f 5
end Terms.ex4



/-
One can even define such "functions" interactively using tactic-style expressions.
-/
namespace Terms.ex5
def f (n : ℕ) : ℕ :=
begin
exact (n + 1)
end
#eval f                     -- still the same function!
#eval f 5
end Terms.ex5


/-
Tactic-based "proof scripts" are just another way to produce a term. Here we use such a proof script to bind a simple nat value to an identifier. Indeed, you can think of values as nothing other than proofs of their types!
-/
namespace Terms.ex6
def x : nat :=
begin
exact 1
end
#eval x
end Terms.ex6


/-
Function application expressions are of the form (func arg). In this example, we apply the function, nat.inc, which is defined in the Lean libraries, and which increments the value of its argument (by 1) to the argument 1.
-/
namespace Terms.ex7
#check (λ n, n + 1) 1
#reduce (λ n, n + 1) 1
end Terms.ex7
