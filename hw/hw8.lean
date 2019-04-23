import tactic.ring

/-
0. For the preceding import to work, you need 
to have downloaded and compiled Lean's math library,
per the recent ungraded assignment. Please go ahead
and do that now. You'll need it for one or two of 
the problems below.
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
| _ := _

/- 1b.
Given your implementation of bool_implies,
prove the following proposition. Use induction
rather than the cases tactic to do case
analysis on Boolean values. 
-/

example : ∀ b1 b2 : bool, 
    (bool_implies b1 b2 = tt) → (b2 = tt ∨ b1 = ff) :=
begin
_
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
| 

/- 2b.

Define aTree to be a node containing the
value 3 and two trees, the first one empty
and the second one a node containing the
value 2 and two empty trees.
-/

def aTree := _

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

-- Your answer here



/- 4.

Write a recursive function, num_nodes, 
that takes a value of type tree T, as an 
argument, where T is some type, and that 
returns the number of nodes in the tree. 
The number of nodes in an empty tree is zero, 
while the number of nodes in a non-empty 
tree is one (for the "top" node) plus the 
number of nodes in each of the subtrees.

The "at sign" before "tree" in the following
function signature tells Lean that even though
tree takes its type argument implicitly, in 
this case we want to give it explicitly. We
need to specify T explicitly here because Lean
has no way of knowing that's what we want.
-/

def num_nodes : ∀ {T : Type}, @tree T → nat
| T tree.empty := _


/- 
The following questions use our definition of
the nas to practice proof by induction. Here is
our nat type and the implementations of addition
and multiplication.
-/

inductive mynat : Type
| zero : mynat
| succ : mynat → mynat

def add_mynat: mynat → mynat → mynat
| mynat.zero m := m
| (mynat.succ n') m :=
    mynat.succ (add_mynat n' m)

def mult_mynat: mynat → mynat → mynat
| mynat.zero m := mynat.zero
| (mynat.succ n') m :=
    add_mynat m (mult_mynat n' m) 


/-
Here's a proof that zero is a right identity
for addition. We explain details in comments.
You will want to use some of the same ideas in
your proofs. 
-/

theorem zero_right_id_add : ∀ (n : mynat),
    add_mynat n mynat.zero = n :=
begin
-- forall introduction
intro n,
-- induction
induction n with n' ih,

-- base case
exact rfl,

-- recursive case
-- first simplify based on definition of add_mynat
simp [add_mynat],
-- now apply induction hypothesis
exact ih,
end

/- #5

Prove the following by induction on n in Lean.
-/

-- 5b. Prove that succ (n + m) = n + (succ m).

theorem add_succ : ∀ (n m : mynat), 
    mynat.succ (add_mynat n m) = add_mynat n (mynat.succ m) :=
begin
_
end


-- 5a. Prove zero is a right identity for mult.

theorem zero_right_absorb_mult : ∀ (n : mynat), 
  mult_mynat n mynat.zero = mynat.zero :=
begin
_
end

-- 5b. Prove addition is associative.

theorem addition_assoc : 
    ∀ (n m p : mynat), 
        add_mynat (add_mynat n m) p = 
        add_mynat n (add_mynat m p) :=
begin
_
end

-- 5c. Prove addition is commutative.

theorem addition_comm :
    ∀ (n m : mynat), add_mynat n m = add_mynat m n :=
begin
_
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
_
end


/- 6c.

Translate your formal proof that double n = n + n into
a concise natural language proof.

Your answer here: 

-/


/- 7a. 

Complete then test the following definition of
a function that computes the n'th Fibonacci 
number when given n as an argument.
-/
def fib : ℕ → ℕ 
| _ := _



/- 7b.

Implement the factorial function. You will need to 
define the function for both its base and recursive
cases.
-/

def fac : ℕ → ℕ
| _ := _
