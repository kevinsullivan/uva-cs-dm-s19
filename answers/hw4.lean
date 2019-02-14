/-
0. Read the class notes through Section 
3.7, Implication. It is important that 
you do this before classes next week, as
we will move somewhat quickly through a
few of these chapters.

To complete the rest of this homework,
solve the problems given as specified,
then save and submit this file.
-/


/-
1. 

Show that if you're given proofs
of a = b and c = b you can construct
a proof of a = c. Do it by completing
the following function. 
-/

def eq_snart { T : Type}
             { a b c: T }
             (ab: a = b)
             (cb: c = b) : 
             a = c :=
eq.trans
    ab
    (eq.symm cb)

/-
Now given the following assumptions, apply
your newly proved inference rule, eq.snart,
(!) to show that Harry = Bob.
-/

axiom Person : Type
axioms Harry Bob Jose: Person
axioms (hj : Harry = Bob) (jb : Jose = Bob)
example : Harry = Jose := eq_snart hj jb

/-
Note: This problem featured the use of a 
logically correct but humanly midleading
identifier, hj, for a proof of Harry=Bob.
It would have been better style to call it
hb. That said, the proof goes through just
fine. Ultimately the main rules that one
must follow when it comes to identifiers
is to avoid using conflicting identifiers.
There is a more subtle rule when it comes
to the elimination for for existentially
quantified propositions. We'll get there. 
For now, it's a good practice to avoid
using misleading idenifiers, even if they
are logically ok.
-/

/-
2. Use example to assert and then prove that
if T is any type, and if a, b, c, and d, are
values of that type, and if you have proofs of
a = b, b = c, and c = d, you can construct a 
proof of a = d. Put the proposition in the first
placeholder below, and the proof in the second.

Hint: Aquality propositions are types. Think of
the problem here as one of producing a function
of the specific type. Use lambdas. We've gotten
you started. The first lambda "assumes" that a,
b, c, and d are natural numbers. What's left to
do is to prove a function (yes, start with lambda)
that takes three arguments of the specified kinds 
(use lambda to give them names) and that finally
produces a result of the type at the end of the 
chain.
-/

theorem transit : 
∀ a b c d : ℕ, 
    (a = b) → (b = c) → (c = d) → (a = d) 
:= 
    λ a b c d,
        λ ab bc cd,
            eq.trans (eq.trans ab bc) cd

/-
3. In the context of the axioms in the following
namespace, write an exact proof term to prove 
that Yuanfang is friendly. Hint #1: Just apply 
the relevant inference rule as a function to the
right arguments. Hint #2: The direction in which
an equality is written matters. If, for example,
you have a proof of x = y and you want to apply 
an inference rule that requires a proof of y = x,
then you need to find a way to get what you need
from what you have to work with in your context.
-/

axioms Mary Yuanfang : Person
axiom Friendly : Person → Prop
axiom mf : Friendly Mary
axiom yeqm : Yuanfang = Mary
example : Friendly Yuanfang :=
    eq.subst (eq.symm yeqm) mf


/-
4. The subtitution rule for equality lets
you rewrite proof goals by substituting one 
term for another, in a goal, as long as you 
already have a proof that the two  terms 
are equal. The reasoning is that replacing 
one term with another makes no difference to 
the truth of a proposition if the two terms
are equal. 

Suppose for example that you have a proof, 
h, of y = x (yes we can and do give names 
to proofs, as we consider them to be values), 
and a proof, y1, of y = 1, and that your 
goal is to prove (x = 1). You can justify 
rewriting this goal as (y = 1), for which 
you already have a proof, because you know 
that y = x; so making this substitution 
doesn't change the truth of the proposition. 

In the tactic scripting libraries that Lean
provides, there is a tactic for rewriting a 
goal in this way. If h is a proof of x = y,
then the tactic, "rw h" ("rw" is short for 
"rewrite") replaces all occurrences of x (the 
left side of h) with y (it's right side).

Here's an example.
-/

def foo (x y : ℕ) (y1 : y = 1) (h: x = y) : (x = 1) :=
begin
rewrite h,
exact y1,
end


/-
Use what you just learned to state and prove 
the proposition that for any type, T, and for 
any objects, a, b, and c, of this type, if 
(a = b) and (b = c) then (c = a). Do this by
finishing off the tactic script that follows.  
Note that to apply an inference rule within a
tactic script you use the "apply" tactic. Read 
the further explanation and hint that follow 
before attempting to solve this problem.
-/

def ac (T : Type) (a b c : T) 
       (ab : a = b) (bc : b = c) 
    : (c = a) := 
begin
apply eq.symm (eq.trans ab bc)
end

/-
Note that the "foralls" in the natural language 
statement are represented in this code *not* by 
using  ∀ but by declaring them to be arguments 
to our function. If you can write a function of 
the specified type then you have in effect proven
that for *any* T and any a, b, c, of type T, if 
if you also have a proof of a=b and a proof of 
b=c, then a value of type c=a can be constructed 
and returned. The reason this is true is that in
Lean all functions are total, as you now recall!

Key hint: The tactic application "rw h" changes
all occurrences of the left side of the equality
h, in the goal, into what's on its right side. 
If you want the rewriting to go from right to 
left, use "rw<-h". When you're just about done, 
don't be surprised if the rewrite tactic applies 
rfl automatically.
-/