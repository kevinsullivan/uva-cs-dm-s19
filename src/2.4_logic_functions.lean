/-
Copyright 2019 Kevin Sullivan and Ben Hocking. 
-/

namespace Functions.ex0
axioms S T : Type
def single_valued := ∀ f : S → T, 
    ∀ x : S, ∀ y z : T,
        f x = y ∧ f x = z → y = z
end Functions.ex0

namespace Functions.ex1
axioms S T : Type
def total := ∀ f : S → T, 
    ∀ x : S, ∃ y : T, f x = y
end Functions.ex1

namespace Functions.ex2
axioms S T : Type
def strictly_partial := ∀ f : S → T, 
    ∃ x : S, ¬ ∃ y : T, f x = y
end Functions.ex2

namespace Functions.ex3
axioms S T : Type
def surjective := ∀ f : S → T, 
    ∀ y : T, ∃ x : S, f x = y
end Functions.ex3

namespace Functions.ex4
axioms S T : Type
def injective := ∀ f : S → T, 
    ∀ x y : S, ∀ z : T,
        f x = z ∧ f y = z → x = y
end Functions.ex4

namespace Functions.ex5
def f : ∀ n : ℕ, ℕ := λ n, n + 1
#check f
end Functions.ex5


/-
Review of notations for declaring and defining functions (as lambda abstractions) in Lean.
-/
namespace Functions.ex1

def double (n : ℕ) := 2 * n
def double' : ℕ →  ℕ := λ n , 2 * n

#check double
#check double'
#check double 3
#reduce double 3
#reduce double' 3

end Functions.ex1


/-
Another example.
-/
namespace Functions.ex2
def square (n: ℕ) := n * n -- return type inferred
#check square
#check square 3
#reduce square 3

def square' : ℤ → ℤ := λ n, n * n

#reduce square' (-3)
end Functions.ex2



/-
Another example.
-/
namespace Functions.ex3
def uint32: ℕ → bool :=
λ n,
        if n >= 0 ∧ n < 2^32 then tt else ff

#check uint32
end Functions.ex3



/-
Another example.
-/
namespace Functions.ex7
def my_pow (x y: nat) := x^y
#eval my_pow 2 16
end Functions.ex7



/-
A function that takes a natural number, n, as an argument and that returns a function as a result. The returned function takes a natural number and always returns the number, n, as a result.
-/
namespace Functions.ex8

def constNatFun (n: ℕ) : ℕ → ℕ := λ k, n
def f3 := constNatFun 3
#eval f3 17

end Functions.ex8



/-
A function that takes a function, f, and an value, n, as arguments and that returns the result of applying f to n.
-/
namespace Functions.ex9

def apply (f: ℕ → ℕ) (n : ℕ) := f n
def square (n : ℕ) := n * n
#eval apply square 5
def cube (n : ℕ) := n * n * n
#eval apply cube 5
end Functions.ex9



/-
A function that takes two functions as arguments and that returns a new function as a result, namely the composition of the given functions. 
-/
namespace Functions.ex10
def compose (g: ℕ → ℕ) (f: ℕ → ℕ) (x: ℕ) : ℕ := g (f x)
#check compose

def double (n : nat) := 2 * n
def square (n : nat) := n * n

def sd := compose square double
def ds := compose double square

#reduce ds 5
#reduce sd 5
end Functions.ex10

