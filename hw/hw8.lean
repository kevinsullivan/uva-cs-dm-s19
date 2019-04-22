import tactic.ring

/-
1. 

We implemented a Boolean abstract data type,
mybool. That exercise showed you how the bool
type is implemented in Lean. For purposes of
this assignment, please use the bool type
that Lean provides instead of our mybool type. 
-/

/- 1a. 

Implement a function, bool_implies, that takes
two bool values, b1 and b2 (not propositions),
and that returns the the value of b1 → b2.
Here the → operator means implication in Boolean
algebra. To know what your function should do,
write out the truth table for implication. You
may  not use Lean's → operator (which does work
for bool values, by the way) in your answer. 
-/

def bool_implies : bool → bool → bool
| _ tt := tt
| ff _ := tt
| _ _ := ff


/- 1b.
Given your implementation of bool_implies,
prove the following proposition. Use induction
rather than the cases tactic to do case
analysis on Boolean values. 
-/

example : ∀ b1 b2 : bool, 
    (bool_implies b1 b2 = tt) → (b2 = tt ∨ b1 = ff) :=
begin
intros b1 b2,
induction b1,
induction b2,
assume h,
apply or.inr,
exact rfl,
assume h,
apply or.inl,
exact rfl,
induction b2,
assume h,
apply or.inr,
cases h,
assume h,
apply or.inl,
exact rfl,
end 

/- 2a.

A tree of natural numbers is either empty or
it is constructed from a natural number and
two smaller trees of natural numbers. Give
an inductive definition of the type of such
trees. Call you datatype tree_nat. Your type
will have two constructors. Call the first
one "empty", and call the second "node".
Hint: The second will take three arguments.
-/

inductive tree_nat : Type
| empty : tree_nat
| node : nat → tree_nat → tree_nat → tree_nat

/- 2b.

Define aTree to be a node containing the
value 3 and two trees, the first one empty
and the second one a node containing the
value 2 and two empty trees.
-/

def aTree := tree_nat.node 
                3 
                (tree_nat.empty) 
                (tree_nat.node 
                    2 
                    tree_nat.empty
                    tree_nat.empty)

/- 3. Define a polymorphic type, "tree", 
just like tree_nat, but where the value stored
in a node can be of any type, T. Then define 
aTree' to be the same as aTree except that it's 
now of type tree rather than of type tree_nat.
Make the type argument implicit. Finally
define a tree of strings, aTree'', just like
aTree' except that 3 is replaced by "Hi!" and
2 is replaced by "Jo".
-/

inductive tree { T : Type } : Type
| empty : tree
| node : T → tree → tree → tree

def aTree' : tree := tree.node
                3 
                (tree.empty) 
                (tree.node 
                    2 
                    tree.empty
                    tree.empty)

def aTree'' : tree := tree.node
                "Hi!" 
                (tree.empty) 
                (tree.node 
                    "Jo" 
                    tree.empty
                    tree.empty)


/- 4.

Write a recursive function, num_nodes, 
that takes a value of type tree T, as an 
argument, where T is some type, and that 
returns the number of nodes in the tree. 
The number of nodes in an empty tree is zero, 
while the number of nodes in a non-empty 
tree is one (for the "top" node) plus the 
number of nodes in each of the subtrees.
-/

def num_nodes : ∀ {T : Type}, @tree T → nat
| T tree.empty := 0
| T (tree.node t c1 c2) := 
    1 + num_nodes c1 + num_nodes c2


/- 
Our mynat type is identical to the nat type
provided by Lean's library of data types.
For the following problems, used Lean's nat
type rather than our mynat type.
-/

#print nat

/- #5

Prove the following by induction on n in Lean.
-/

-- 5a. Prove that zero is a right identity for mult.

example : ∀ (n : ℕ), 
  n * 0 = 0 :=
begin
intro n,
induction n with n,
exact rfl,
exact rfl,
end

-- 5b. Prove that addition is associative.

example : 
    ∀ (n m p : ℕ), 
        (n + m) + p = n + (m + p) :=
begin
intros n m,
induction n with n,
simp,
simp,
end


example : ∀ (n m : ℕ), (n = m) :=
begin

end

-- 5c. Prove that addition is commutative.

example :
    ∀ (n m : ℕ), n + m = m + n :=
begin
    intros n m,
    induction n,
    simp,
    simp,
end


/- 6a. 

The next problem refers to the following
recursive function. It takes a natural number
as an argument and returns the natural number
that is double the value of the argument. 
Start by being sure you see how it works.
-/
def double : ℕ → ℕ 
| nat.zero := nat.zero
| (nat.succ n') := nat.succ (nat.succ (double n'))

#eval double 5  -- it works

/- 6b.

Prove the following simple proposition about
this function. (Ack. To B. Pierce for this
problem.) 

Important hints: (1) the tactic, "simp [double]"
will simplify an expression using the rules in
the definition of the double function; (2) the
"ring" tactic can find proofs for certain easy
arithmetic propositions that require reasoning
about associativity, commutativity, etc.; (3) it
is often useful to use an induction hypothesis 
*rewrite* a goal into a form that can then be
proved more easily.
-/

lemma double_plus : ∀ (n : ℕ), double n = n + n :=
begin
intro n,
induction n,
exact rfl,
simp [double],
rw n_ih,
ring,
end


/- 7a. 

Complete then test the following definition of
a function that computes the n'th Fibonacci number given
n as an argument.
-/
def fib : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (nat.succ (nat.succ n')) := _




