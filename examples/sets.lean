/-
Intuitively a set is a collection of objects.
That said, if one is not careful about what
one allows a set to be, paradoxes can arise,
making the logical system inconsistent, and 
thus useless. For more details, search for an
explanation of Russell's paradox. 

The work needed to repair Russell's original
mistake led to Zermelo-Frankel set theory, the
set theory of everyday mathematics, and also,
at least indirectly to the type theory that
underpins Lean and relate proof assistants.

There are two things to know about how sets 
and operations involving sets are reprented
in Lean. First, in Lean, set is what we call
a type constructor. Second, sets are identified 
with membership predicates. We discuss each of
these idea next.
-/

-- Type Constructors: set

/-
First, set is a type constructor, not a type.
It takes a type parameter as an argument and 
returns a type, one now specialized to the 
argument type. Because it takes a type and
returns a type, set (and a type constructor
more generally) is a function:  one of type,
Type → Type. So, for example, set int is the 
type of sets with int-valued elements.

Lean tells us that the set type constructor can 
actually take a type in any type universe, i.e., 
Type (which is really Type 0), Type 1, Type 2,
etc. We needn't be concerned with that here.
-/

#check set

-- Membership Predicates

/-
Second, sets in Lean are identified with
membership predicates: of type T → Prop, 
where T is type of elements in a set. The 
membership predicate is true for values in
the set and not true otherwise. 
-/

#check set ℕ 

#reduce set ℕ

-- Example: the empty set of ℕ 

/-
For example the empty set of ℕ values, also 
written as ∅ ℕ, is literally defined as the 
predicate, λ n : ℕ, false. This predicate is
satisfied for no value of type ℕ, and so the 
set it defines is the empty set. 
-/

#check (∅ : set ℕ )

/-
We think of the predicate that defines a set 
as specifying a property of elements of the 
kind in or not in the set. The type, set ℕ, 
is thus equated with a predicate on ℕ, which
we consider as defining the property of being
of being a member of the set. Sets (at least)
in Lean are identified with their membership
predicates. 

As an example, the empty set of ℕ is defined
by the predicate that is false for every ℕ.
No natural number satisfies this predicate.
The set it denotes is the set of values that
satisfy it, which is the empty set. Study the
following code with care and understand it.
-/

#reduce (∅ : set ℕ)

/-
The predicate  that defines the empty 
set is, as we've already discussed, 
false(n): i.e., the function of type 
ℕ → Prop that for any value, n : ℕ, 
returns the proposition false. No 
ℕ  can satisfy this predicate by 
making it anything other than false. 
The set it designates is the empty set.
-/

-- Display Notation

/-
Let's bind and empty set of ℕ to the
identifier, e. We can also write the
empty set using curly braces, or what
we call set display notation.
-/

def e: set ℕ := { }

/-
The symbol, ∅, is often used to represent 
the  empty set (of values of whatever type).
-/

def e': set ℕ := ∅ 

/-
We can't write "e : set := {}"", because 
then Lean would not have enough context 
to infer the type of the set elements.
-/

/-
EXERCISE: What is the property of 
natural numbers that characterizes 
e, the empty set of natural numbers?
Give you answer as a predicate: a
function from ℕ to Prop. Give a λ 
abstraction as an answer.
-/

/-
EXERCISE: What predicate defines the
set of all ℕ values?
-/

-- Set Builder Notation

/-
We can also represent the empty 
set using set builder notation.
Set builder notation is also called
set comprehension notation.
-/


/-
Here we define the empty set of ℕ again
-/

def e'' : set ℕ := { n | false }


/-
Now we define the entire set of even ℕ 
-/

def evs : set ℕ := { n | ∃ m, m + m = n } 


-- Singleton Sets

/-
Here's another set of ℕ, containing 
only the number, 1. We call such a
set a singleton set.
-/

def x: set nat := { 1 }

/-
EXERCISE: What property of natural 
numbers defines the property of being 
in this set? Try to come up with the
answer before you look! 
-/

#reduce x

/-
The answer is a little surprising.
The predicate λ n, n = 1, would do
to define this set, but instead Lean
uses λ n, n = 1 ∨ false. Lean could
have, and in some cases will, leave
off the (∨ false) at the end. See it
is so in the following example code.
-/

def x' := { n | n = 1 }
#reduce x'

/-
The two different notations give rise 
to slightly different but equivalent
predicates, and thus to the same sets.
-/

-- SET MEMBERSHIP

/-
So what does set membership mean?
By the notation 1 ∈ x we mean the
proposition that "1 is in, or is 
a member of the set, x." This is
simply the proposition obtained 
by applying the predicate, x, to
the value, 1. x is the set and it
is the predicate that defines the
set. In Lean they are the same
thing. The proposition 1 ∈ x is 
definitionally the same as (x 1). 
The predicate, i.e., the set, x, 
is defined as  λ (n : ℕ), n = 1. 
Applying this predicate/function 
to 1 yields the proposition that:
1 = 1 ∨ false. This proposition,
in turn, is easy to prove, and so,
yes, indeed, 1 is in the set x.
-/

/-
Reducing 1 ∈ x reveals the 
proposition obtained by applying
the x predicate to the value 1 
to get a membership proposition
for 1. 
-/
#reduce 1 ∈ x
#reduce x 1

/-
In this case, the membership
proposition, 1 ∈ x, is true, as
we prove next.
-/

example : 1 ∈ x :=
-- 1 = 1 ∨ false
begin
/-
It can be easier to work with proofs 
about sets if you use the change tactic
to ask Lean to show you the predicate 
that the goal represents. You can use
#reduce to see the proposition that the
goal using set notation denotes. 
-/
  change 1 = 1 ∨ false,
  -- the rest is straightforward
  apply or.intro_left,
  exact rfl,
end


/-
Here we use some shorthand tactics to
make it easier to write the proof. It's
good to learn this shortcuts. They make
quick work of some proof goals.
-/

example : 1 ∈ x :=
-- 1 = 1
begin
  change 1 = 1 ∨ false,
-- now or.intro_left, but with a shortcut
  left,
-- and now exact rfl, but with a shortcut
  trivial,
end


-- MORE EXAMPLE

/-
Here's two sets with three
elements each.
-/

def y : set nat := { 1, 2, 3 }
def z : set nat := { 2, 3, 4 }

/-
EXERCISE: What is a predicate
that characterizes membership in
the set, y?
-/

#reduce y


/-
EXERCISE: Define the same set, y,
with the name, y', using set builder
notation.
-/

def y' : set nat := { n | 
    n = 1 ∨ n = 2 ∨ n = 3 }

#reduce y 

/-
With these basics in hand, we can 
define, understand, and work with
the full range of set operations.
Set operations are like operations
with numbers but their operands and
results are sets.
-/

-- SET UNION

/-
The union of two sets, y and z, 
which we denote as y ∪ z, is the
combined set of values from y and 
z. 

An element is either in or not in 
a given, but cannot be in a more 
than one time (otherwise you have
what is called a multiset). The 
union of y and z as defined above 
is thus the set { 1, 2, 3, 4 }.
-/

def u := y ∪ z


/-
EXERCISE: What predicate defines 
the set that is the union of y and z?
-/

#reduce u

/-
Answer: It is the predicate that
defines what it means to be in y 
or to be in z. That is, it is the
disjunction of the predicates that
define y and z, respectively. Union
corresponds to "or."
-/

/-
Let's prove that 3 ∈ u. Let's 
start by reminding ourselves of
the predicate that defines u and
of the proposition represented 
by 3 ∈ u.
-/

#reduce u

/-
The set, u, is defined as a
predicate that takes a : ℕ and
returns the proposition that
that a is one of the values
in the set, expressed as a 
somewhat long disjunction. Lean 
selects the variable name, a, 
for purposes of printing out 
the value of u. There is no
special meaning to a; it is 
just an otherwise unbound name.
-/


/-
Now that we know that 3 ∈ u is 
just a proposition involving a
bunch of disjunctions, it's easy
to prove. -/

example : 3 ∈ u :=
begin
/-
Notice again that Lean leaves the 
goal written using set membership
notation. Just bear in mind that
the goal is just the disjunction,
(3 = 3 ∨ 3 = 2 ∨ 3 = 1 ∨ false) ∨ 
3 = 4 ∨ 3 = 3 ∨ 3 = 2 ∨ false.
-/
left,
left,
trivial,
end

#reduce 3 ∈ y ∪ z

/-
Or, if you prefer, make the goal
explicit as a disjunction.
-/
example : 3 ∈ y ∪ z :=
begin
change (3 = 3 ∨ 3 = 2 ∨ 3 = 1 ∨ false) ∨ 3 = 4 ∨ 3 = 3 ∨ 3 = 2 ∨ false,
apply or.inl,
apply or.inl,
trivial,
end

-- SET INTERSECTION

/-
The intersection of two sets, y and
z, which we denote as y ∩ z, is the
set containing those values that are
in y and that are in z. Intersection
thus corresponds to the conjunction
of the predicates defining the two
individual sets.
-/

def w := y ∩ z

#reduce w

example : 2 ∈ y ∩ z :=
-- (a = 3 ∨ a = 2 ∨ a = 1 ∨ false) ∧ (a = 4 ∨ a = 3 ∨ a = 2 ∨ false)
begin
  apply and.intro,
    -- 2 ∈ y
    right,
    left,
    trivial,

    -- 2 ∈ z
    right,
    right,
    left,
    trivial,
end


-- SET DIFFERENCE

/-
The set difference y - z, also
writen as y \ z, is the set of
values that are in y but not in
z. Think of the subtraction as
saying that from y you take away
z, and the result is what is left
of y.

EXERCISE: What predicate defines
a set difference, y \ z?
-/

#reduce y \ z

example : 1 ∈ y \ z :=
begin
-- apply and.intro,
  split,
    -- 1 ∈ y
    right,
    right,
    left,
    trivial,
/-
The goal looks funny, but think
about what it means. It is the
predicate, (λ (a : ℕ), a ∉ z),
applied to the value, 1, which
is to say it's the proposition,
1 ∉ z. That in turn is ¬ 1 ∈ z.
And that, in turn, is just the
proposition that 1 ∈ z → false.
So assume 1 ∈ z and show false 
to prove it. What is 1 ∈ z? It's
the proposition that 1 is one of
the elements in the set, written
as a disjunction, so use case
analysis! 
-/
    -- 1 ∉ z
    assume pf,
    cases pf,
/-
Now we need a proof that 1 ≠ 4. The 
dec_trivial tactic defined in the Lean's
standard library "decides" many purely 
arithmetic propositions. That is, it 
generates either a proof that such a
proposition is true if it's true. It
will also generate a proof that its
negation is true if that is the case. 
The dec_trivial tactic implements a
"decision procedure" for sufficiently
simple propositions involved numbers.
Here we use it to give us a proof of 
1 ≠ 4. We can then use that to get a 
proof of false and use false elim to 
eliminate the current case on grounds 
that it is based on contradictory
assumptions (and thus can't happen).
-/
      have h : 1 ≠ 4 := dec_trivial,
/-
The contradiction tactic looks for a
explicit contradiction in the context
and if it finds one, applies false.elim
to finish proving the goal.
-/
      contradiction,

      cases pf,
        have h : 1 ≠ 3 := dec_trivial,
        contradiction,

        cases pf,
          have h : 1 ≠ 2 := dec_trivial,
          contradiction,

          have f : false := pf,
          contradiction,
end


-- SUMMARY SO FAR

/-
The examples in this summary
require you to recall that 
previously in this file we 
defined x, y,  and z to be the 
ℕ sets, { 1 }, { 1, 2, 3 }, 
and { 2, 3, 4 }.
-/

#print x
#print y
#print z

/-
A set can be, and in Lean is, 
characterized by a predicate: 
one that is true for each member 
of the set and false otherwise.
It is a "membership predicate".

Consider, for example, what it
means for 1 or for 2 to be in the
set, x. We write these propositions
as 1 ∈ x and as 2 ∈ x respectively.
-/

#reduce 1 ∈ x
#reduce 2 ∈ x
#reduce 3 ∈ z


/-
The union of two sets is given
by the disjunction (or, ∨) of the 
respective membership predicates:
(a ∈ y ∪ z) means (a ∈ y) ∨ (a ∈ z).
-/

#reduce 1 ∈ (y ∪ z)
#reduce (1 ∈ y) ∨ (1 ∈ z)


/-
The intersection of two sets is
defined by the conjunction of the
respective membership predicates:
(x ∈ y ∩ z) = (x ∈ y ∧ a ∈ z)
-/

#reduce (1 ∈ y ∩ z)

/-The difference of two sets, y \ z,
is defined by the conjunction of the 
first and the negation of the second
membership predicates for the sets:
(a ∈ y \ z) = ( a ∈ y) ∧ (¬ a ∈ z).
-/

#reduce 1 ∈ y \ z


-- PART II

/-
Now we introduce additional basic 
set theory concepts: these include
notions of subsets, set equality,
power sets, product sets, tuples,
and a function that simulates an 
element insertion operator for sets. 

In all cases, we see that these
set operations can be understood
as operations on the predicates
that define sets. The connection
of set theory to predicate logic 
is thus made clear and explicit.
-/

-- SUBSET

/-
Subset, denoted ⊆, is a binary 
relation on sets, denoted X ⊆ Y, 
where X and Y are sets. Viewed 
as a predicate on such sets, it
is satisfied (made true by X and
Y) iff every member of X is also 
a member of Y. Logically, X is a
subset of Y if the property of
being in X implies the property
of being in Y.
-/

#check x ⊆ y
#reduce x ⊆ y

/-
Note that what is displayed when you
hover over the reduce line includes 
"script" curly brace characters. These
indicate a slight variant on implicit
arguments that we needn't get in any
detail right now. Just think of them
as indicating implicit arguments.
-/

/-
So, { 1, 2 } ⊆ { 1, 2, 3 }, for
example, but is is not the case
that { 1, 2 } ⊆ { 1, 3, 4}. In the
first case, every element of the
set, { 1, 2 }, is also in the set
{ 1, 2, 3 }, so { 1, 2 } is a 
subset of { 1, 2, 3 }; but that
is not the case for { 1, 2 } and
{ 1, 3, 4 }.
-/

/-
EXERCISE: List all of the subsets
of each of the following sets of ℕ. 

* ∅ 
* { 1 }
* { 1, 2 }
* { 1, 2, 3 }

EXERCISE: How many subsets are there
of a set containing n elements. Does 
your formula work even for the empty
set?
-/

/-
We can now see that the subset relation
on sets has a precise logical meaning. 
x ⊆ y means ∀ a, a ∈ x → a ∈ y.
-/

#check x ⊆ y
#reduce x ⊆ y

/-
A quick note on a pattern that appears
often in predicate logic:

Let's look at the definition of the 
subset relation again, for sets of ℕ 
values, x and y. Here is what it means
for y ⊆ x.

∀ (a : ℕ), a ∈ y → a ∈ z.

Let's translate this to logicky English.

For any natural number, a, if a is in
y then e is in z. That is what is means
for y to be a subset of z.

What's interesting in this formulation
is the combination of a ∀, which picks
out *all* elements of the ℕ type, followed
by a conditional (implication), where the
premise imposes a further constraint on 
the elements being considered. It need 
only be true that every ℕ that is *also*
and element of y be a member of z for y
to be a subset of z. 

This is a common pattern in logic. The
general form is ∀ x : T, P x → Q x. It 
is read as saying that for any x *with 
property P*, some other property, Q, 
must hold. In effect it quantifies over
the values of type T with property P,
and then makes a statement about those
values, in particular: here they they
also have property Q.
-/

/-
Okay, so let assert and prove a
proposition involving the subset
relation. We'll show that x ⊆ y,
i.e., { 1 } ⊆ { 1, 2, 3 }. To do
it we have to proving that if 
a ∈ x then a ∈ y. Now remember
what x and a ∈ x are. First, x
is understood to be a set, but 
it is specifically a membership
predicate, of type ℕ → Prop, and
a ∈ x is a proposition, namely 
the one obtained by applying the
membership predicate to a: (x a).
If (x a), i.e., a ∈ x, is true,
i.e., provable, then a is said 
to be a member of the set, x. 
-/

/-
Let's have another look at what
the proposition, x ⊆ y, means: 
for any a, if a ∈ x then a ∈ y.
-/

#reduce x ⊆ y

/-
So let's prove it's true.
-/

example : x ⊆ y := 
begin
/-
It's sometimes helpful to change 
from set notation to the equivalent
propositional notation. The change
tactic will do this for you, as 
long as what you're changing the
goal is is "definitionally equal"
to the current goal. You cand find
out what the exact proposition is
using reduce, as we did above.
-/
  change ∀ ⦃a : ℕ⦄, a = 1 ∨ false → a = 3 ∨ a = 2 ∨ a = 1 ∨ false,
/-
The rest is just an everyday proof.
Note that we can quickly zero in on
the disjunct we need using a series
of left and right tactics. (You do
need to remember that ∨ is right
associative, so left gives you the
left disjunct and right gives you
everything else to the right of the 
leftmost disjunct.
-/
  assume a,
  intro h,
  cases h,
  -- case a = 1
    right,
    right,
    left,
    assumption,
  
  -- case false
    contradiction,
end


section sets
/-
We temporarily assume, within this
section, that T is an arbitrary type,
x is an arbitrary value of type T,
and that A, B, and C are arbitrary
sets of T-type elements.
-/
variable T : Type
variable x : T
variables A B C : set T


/-
We can confirm our understanding
of the subset relation using this
notation. Now A and B are sets, and
in Lean that means that these sets
are represented by their membership
predicates. They are membership
predicates.
-/

#reduce A ⊆ B

/-
EXERCISE: Explain precisely what 
the message produced by #reduce is
saying. What is another way that
Lean could have written A a or B a?
-/


-- SET EQUALITY (and extensionality)

/-
The "principle of extensionality" for
sets stipulates that if one can show
that ∀ e, (e ∈ A ↔ e ∈ B) → (A = B). 
-/

#check ext

/-When faced with a goal of proving 
that two sets, A and B are equal,
i.e., that A = B, one can apply this 
principle to reduce the goal to that 
of showing that ∀ e, e ∈ A ↔ e ∈ B.
-/

-- set equality
example : A = B :=
begin
  apply ext,
  intro x,
  apply iff.intro,
  intro,
/-
We can proceed no further here, as
we have nothing to use to prove that
A actually does equal B in this case.
A and B are just arbitary sets, so not
equal, in general. What the example is
meant to show is how to use ext and 
how to proceed. As for this proof, we
will just abandon it as not possible
to prove.
-/
end

/-
Let's prove that { 1, 2 } = { 2, 1 }.
-/

def p : set ℕ := { 1, 2 }
def q : set ℕ := { 2, 1 }

#reduce 1 ∈ p

theorem oo : p = q  := 
begin
  apply ext,
  intro x,
  apply iff.intro,

  -- forward direction

  intro, 
  -- remember that a is a disjunction
  cases a with first rest,
/-
We introduce a new tactic: rewrite,
written as rw h or rw ←h. When applied 
to a proof, h : x = y or h : x ↔ y, of 
an equality or a bi-implication, it 
rewrites any occurrences of the left 
side, x, in the goal, with the right 
side, y. If you want to rewrite by 
replacing occurrences of the right 
side, y, with the left, x, use rw ←h.
-/
  rw first,
  right, left, apply rfl,
  cases rest,
  rw rest,
  apply or.inl, apply rfl, 
  -- rest is now ((λ n, false) x) = false!
  apply false.elim rest,

  -- backward direction
  intro,
  cases a,
  rw a,
  right, left, apply rfl,
  cases a, 
  rw a,
  left, apply rfl,
  apply false.elim a,
end


-- POWERSET

/-
The powerset of a set, A, is the set of all
of the subsets of A.
-/

#check A
#check powerset A
#check 𝒫 A
#reduce 𝒫 A

/-
Note about implicit arguments. In the preceding
definition we see {{ }} brackets, rendered using
the characters, ⦃ ⦄. This states that the argument
is to be inferred from context (is implicit) but
is expected only when it appears before another
implicit argument. This notation tells Lean not
to "eagerly" consume the argument, as soon as it
can, but to wait to consume it until it appears,
implicitly, before another implicit argument in a
list of arguments. This is a notational detail 
that it's not worth worry about at the moment. 
-/

/-
There are two members we always know are in the
powerset of A: the emptyset and A itself. Of course,
if A is the emptyset, this is technically only one
member, but the proofs are the same.
-/

#check A
#check 𝒫 A
#reduce 𝒫 A

/-
We define the powerset of A, itself a set,
as, λ (t : T → Prop), ∀ ⦃a : T⦄, t a → A a.
Let's analyze this. First, we note that it
is a predicate, as we would expect, given
that we use predicates to define sets. In 
particular, this a predicate on values of
type, T → Prop, which is to say, this is a
predicate on predicates that define sets!
It's a predicate that's true whenever its
argument, a set defined by a predicate, is
a subst of A, which is to say that it's true
when any element in the argument (set) is 
also in A. When applied to a set, t, this
predicate is satisfied (true) if and only 
if every a in t is also in A: formally,
∀ ⦃a : T⦄, t a → A a.
-/

#reduce ∅ ∈ 𝒫 A

/-
Lean is helping us here. We need to 
show that if a ∈ ∅ then a ∈ a to show
that ∅ is a subset of A. But a ∈ ∅ is
literally false. To see it, work through
the application of the predicate for ∅ 
to any value, a. Lean is simplifying
a ∈ ∅ to false.
-/

example: ∅ ∈ 𝒫 A :=
/-
To show that the set, ∅, is in the set 𝒫 A, 
we have to show that ∅ is a subset of A. To
do that, we have to show that any t that is 
in ∅ is also in A.
-/
begin
  -- change goal to logical form
  change ∀ ⦃a : T⦄, false → A a,
  -- use forall introduction
  intro t,
  -- now it's a trivial proof
  assume t_in_emptyset,
  contradiction,
end

#reduce A ∈ 𝒫 A

/-
To prove this, we need to prove that A
is subset of A, which is to say any a in
A is also in A. It's as simple as that and
the proof is of course trivial.
-/

example: A ∈ 𝒫 A :=
begin
  change ∀ ⦃a : T⦄, A a → A a,
  assume t,
  assume t_in_A,
  assumption
end

/-
Slightly more interesting cases are also
easy to prove. There's nothing involved 
here beyond what you already understand.
-/
#reduce ({1, 3}: set ℕ) ∈ 𝒫 ({1, 2, 3}: set ℕ)

/-
One again to prove that {1, 3} is in the power
set of {1, 2, 3} it suffices to show that every
element of {1, 3} is in {1, 2, 3}, because that
is what it means to be a subset. The proof is
straightforward.
-/

example: ({1, 3}: set ℕ) ∈ 𝒫 ({1, 2, 3}: set ℕ) :=
begin
  change ∀ ⦃a : ℕ⦄, a = 3 ∨ a = 1 ∨ false → a = 3 ∨ a = 2 ∨ a = 1 ∨ false,
  -- forall introduction
  intro t,
  -- assume premise of implication to be proved
  assume pf_t_in_1_3,
  -- use or elimination on proof of premise
  cases pf_t_in_1_3 with pf_t_is_3 pf_t_in_1 ,
    -- show 3 from {1, 3} is in {1, 2, 3}
    exact or.inl pf_t_is_3,

    -- show 1 from {1, 3} is in {1, 2, 3}
    right,
    -- an ever so slightly clever or intro
    exact or.inr pf_t_in_1,
end

-- a more involved example; study this one
-- {{1, 2}, {1, 3}, {2, 3}} ⊆ 𝒫 {1, 2, 3}

#reduce ({{1, 2}, {1, 3}, {2, 3}}: set (set nat)) ⊆ 𝒫 ({1, 2, 3})

example : 
({{1, 2}, {1, 3}, {2, 3}}) ⊆ 𝒫 ({1, 2, 3} : set nat) :=
begin
  change ∀ ⦃a : ℕ → Prop⦄,
  (a = λ (b : ℕ), b = 3 ∨ b = 2 ∨ false) ∨
    (a = λ (b : ℕ), b = 3 ∨ b = 1 ∨ false) ∨ (a = λ (b : ℕ), b = 2 ∨ b = 1 ∨ false) ∨ false →
  ∀ ⦃a_1 : ℕ⦄, a a_1 → a_1 = 3 ∨ a_1 = 2 ∨ a_1 = 1 ∨ false,
  intro s,
  assume pf_s_in_subset,
  cases pf_s_in_subset with pf_s_is_2_3,
    assume t,
    assume pf_t_in_s,
    cases pf_s_is_2_3 with pf_s_is_3,
      cases pf_t_in_s with pf_t_is_3 pf_t_in_2,
        exact or.inl pf_t_is_3,

        apply or.inr,
        cases pf_t_in_2 with pf_t_in_2 pf_t_in_emptyset,
          exact or.inl pf_t_in_2,
          exact false.elim pf_t_in_emptyset,

  cases pf_s_in_subset with pf_s_is_1_3,
    assume t,
    assume pf_t_in_s,
    cases pf_s_is_1_3 with pf_s_is_3,
      cases pf_t_in_s with pf_t_is_3 pf_t_in_1,
        exact or.inl pf_t_is_3,

        apply or.inr,
        apply or.inr,
        assumption,

  cases pf_s_in_subset with pf_s_is_1_2 pf_s_in_emptyset,
    assume t,
    assume pf_t_in_s,
    cases pf_s_is_1_2 with pf_s_is_2,
      cases pf_t_in_s with pf_t_is_2 pf_t_in_1,
        apply or.inr,
        exact or.inl pf_t_is_2,

        apply or.inr,
        apply or.inr,
        assumption,
      
    exact false.elim pf_s_in_emptyset,

end

 
-- Tuples
/-
If S and T are types, then the product type
of S and T, written out as (prod S T) and in
shorthand as S × T, has as its values all of
2-tuples, or ordered pairs, (s, t), where 
s : S, and t : T. 
-/

/-
In the following code, we see that ℕ × ℕ is
a type, and the 2-tuple, or ordered pair, 
(1, 2), is a value of this type. 
-/

#check ℕ × ℕ 
#check prod ℕ ℕ 
#check (1, 2)

/-
We can form product types from any two types.
Note the type of this 2-tuple.
-/

#check ("Hello Lean", 1)

/-
This ordered pair notation in Lean in shorthand 
for the appliation of the constructor, prod.mk,
two two arguments. The constructor takes the 
type arguments implicitly.
-/
#check prod.mk 1 2 -- long way to write (1, 2)
example : prod.mk 1 2 = (1, 2) := rfl

/-
We can form 3- and larger tuples using nested
2-tuples. Note that × is right associative, as
you can see by studying the type of this term.
-/

#check ("Hello Lean", (10, (tt,1)))

#check ((0,0),(0,0))


-- PRODUCT SET

/-
The Cartesian product set of two sets, A 
and B, denoted as A × B in everyday math,
is the set of all ordered pairs, (a, b) 
(values of type prod A B), where a ∈ A 
and b ∈ B. In Lean, the set product of 
sets, A and B, is denoted as set.prod A B.
There is no nice infix operator notation
for set products at this time.

Note carefully: there is a distinction
here between product types and product sets.
Product types are types, while product sets
are sets. And sets are not types in Lean.
Rather they're specified as properties.

This is potentially confusing. It is made
more confusing by the fact that Lean has 
a way to convert a set into a special type
called a subset type: the type of elements
in the set, along with proofs of membership.
And if you apply prod to two sets, you'll 
get a subset type!
-/

#check set.prod y z     -- product set type
#reduce set.prod y z    -- product set property
#check prod y z         -- oops, a subset type
#check y × z            -- oops, same thing
#reduce prod y z        -- oops, not what we want


/-
A set product is just a set, which is to
say it's defined by a predicate, s. Such a
predicate is true for exactly the members
of the set. That is, (s x) is a proposition
that is true iff x ∈ s. The predicate that
defines a product set is a predicate on
ordered pairs. It's basically defined like
this:
-/

def mysetprod (S T : Type) 
  (s : set S) (t : set T) : set (S × T) :=
    { p : S × T | p.1 ∈ s ∧ p.2 ∈ t }

/-
What this says, then, is that the product set
of s (a set of S-type values) and t (a set of
T-type values) is the set of pairs, p, each of
type (prod S T), and each thus an ordered pair,
p = (p.1, p.2), where p.1 ∈ s and p.2 ∈ t.
Lean provides this function as set.prod. 
-/


example : (1, 2) ∈ set.prod y z := 
begin
change (λ (p : ℕ × ℕ),
  (p.fst = 3 ∨ p.fst = 2 ∨ p.fst = 1 ∨ false) ∧ (p.snd = 4 ∨ p.snd = 3 ∨ p.snd = 2 ∨ false)) (1,2),
  split,
  right,right,left,apply rfl,
  right,right,left,apply rfl,
end


-- COMPLEMENT

/-
The complement of a set is the set of all
values of the set's type that are not in that
set.

The complement is specified by the "-" sign
-/

#check -y
#reduce -y
#reduce 5 ∈ -y

example: 5 ∈ -y :=
begin
  change 5 = 3 ∨ 5 = 2 ∨ 5 = 1 ∨ false → false,
  assume pf_5_in_y,
  cases pf_5_in_y with pf_5_eq_3 h,
    have pf_5_ne_3: 5 ≠ 3 := dec_trivial,
    contradiction,

  cases h with pf_5_eq_2 h,
    have pf_5_ne_2: 5 ≠ 2 := dec_trivial,
    contradiction,

  cases h with pf_5_eq_1 h,
    have pf_5_ne_1: 5 ≠ 1 := dec_trivial,
    contradiction,

    assumption
end


-- INSERTION

/-
We can define an operation that we can think
of as "inserting" an element into a set: as a
function that takes an element and a set and
returns the set containing that element along
with the elements of the original set. Unlike
in Python or Java, there's no change to a data 
structure in this case. In pure functional
languages, such as Lean, there is no concept
of a memory or of "mutable" objects. Rather,
everything is defined by functions, here one
that takes a set and a value and constructs 
a new set value just like the old one but with
the new element included as well. -/

def myInsert 
{ T : Type } (a : T) (s : set T) : set T :=
    {b | b = a ∨ b ∈ s}

/-
The predicate for the set resulting from
"inserting 5 into { 1, 2, 3, 5 }" admits
that 5 is also a member of the result set. 
-/    
#reduce myInsert 5 { 1, 2, 3, 4 }

-- The Lean math library defines "insert"
#reduce insert 5 { 1, 2, 3, 4 }


-- MORE EXAMPLES

/-
Several of these examples are adapted
from Jeremy Avigad's book, Logic and 
Proof. Prof. Avigad (CMU) is one of the
main contributors to the development of
Lean, and he leads the development of 
its mathematical libraries, including
the one you're now using for sets, in
particular.
-/

/-
A is a subset of A ∪ B
-/
example : ∀ T : Type, ∀ s t: set T, s ⊆ s ∪ t :=
begin
  assume T s t x, 
  assume h : x ∈ s,
  show x ∈ s ∪ t, 
  change s x ∨ t x,
  change s x at h,
  from or.inl h
end

/-
The empty set, ∅, is a subset of any set.
-/
example : ∀ T : Type, ∀ s: set T, ∅ ⊆ s :=
begin
  assume T s x,
  assume h : x ∈ (∅ : set T),
  have f: false := h,
  contradiction,
end

/-
Subset is a transitive relation on sets
-/
example : 
    ∀ T : Type, ∀ A B C: set T, 
        A ⊆ B → B ⊆ C → A ⊆ C 
:=
begin
    assume T s t u,
    assume st tu,
    intro,
    intro,
    have z := st a_1,
    exact (tu z),
end  

/-
If an object is in both sets A and B
then it is in their intersection.
-/
example : 
∀ T : Type, forall A B : set T, 
∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B :=
begin
  assume T A B x,
  assume hA : x ∈ A,
  assume hB : x ∈ B,
  show x ∈ A ∧ x ∈ B, from
  and.intro hA hB,
end


/-
If an object is in set A or is in
set B then it is in their union.
-/
example : 
∀ T : Type, forall A B : set T, 
∀ x, x ∈ A ∨ x ∈ B → x ∈ A ∪ B :=
begin
  assume T A B x,
  intro dis,
  show x ∈ A ∨ x ∈ B,
  by assumption,
end

/-
A minus B is a subset of A
-/
example : A \ B ⊆ A :=
begin
  assume x,
  assume mem : x ∈ A \ B,
  cases mem, 
  from mem_left,
end

/-
A minus B is contained in the complement of B
-/
example : A \ B ⊆ -B :=
begin
  assume x,
  assume mem : x ∈ A \ B,
  change x ∈ A ∧ ¬ x ∈ B at mem,
  change x ∉ B,
  exact mem.right,
end


/-
A \ B is equal to the intersection
of A with the complement of B.
-/
example : A \ B = A ∩ -B :=
begin
  apply ext,
  intro,
  split,
  intro h,
  exact h,
  intro h,
  exact h,
end

end sets

