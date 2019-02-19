/-
Here is the practice exam. It provides you
with a set of problems illustrative of the
material to be tested. This is a homework
assignment due this coming Thursday. We will
review the questions in class.

Copy this file your "work" directory. Work
on it there. Upload to Collab when done.

Note: An incorrect answer above or below
a correct answer can cause Lean to be unable
to process the correct answer. If you are not
able to complete a problem successfully please
comment out your incomplete answer so that we
can see your work but so that your incomplete
work does not cause problems for surrounding
problems and answers.
-/

/-
PART I: Functions. Functions are an essential
element of the language of predicate logic. In
this section, you show that you understand how
to define, use, and reason about functions in
Lean.
-/

/- 1.
Study each of the following definitions,
then answer the associated question about
the types involved in these definitions.
-/

-- Consider this function
def f (n : ℕ) (s : string) := s

/-
a. What is it's return type? Answer:
-/

/-
b. What is the type of (f 5)? Answer:
-/

/-
c. What is the value of (f 0 "yay")
-/

/-
d. What is the type of this function?
-/


/- 2.
Define three functions called square,
square', and square'', each of type
ℕ → ℕ. Each function must return the
square of the value to which it is
applied. Write the first function in
"C" style, the second using a tactic
script, and the third using a lambda
abstraction. Declare all argument and
return types explicitly. Answer below.
-/







/- 3.
Construct three proofs to test your
function definitions. The first must
use "lemma" to define a proof, called
square_3_9, of the proposition that
(square 3) equals 9. The second must
use "theorem" to define a proof, called
square'_4_16, of the proposition that
square' applied to 4 reduces to 16. The
third must prove that square'' 5 is
equal to 25. This third proof must not
use the equals sign, =, but must use
"eq" instead to state the proposition
to be proved. Hint on #3, sometimes
you need to use parentheses to express
how you want terms to be grouped. Answer
below.
-/






/- 4.
Define a function called last_first.
It must take two string values, called
"first" and "last" (without quotes),
and return a string consisting of "last"
followed by a comma and a space followed
by "first".

For example (last_first "Orson" "Welles")
must return the string, "Welles, Orson".
Write a test case for your function to
prove that (last_first "Orson" "Welles")
is "Welles, Orson". Use "example", to
check the proof. Hint: The ++ operator
implements the string append function.
Answer below.
-/




/- 5.

Complete the following definition of a
function, called apply3. It takes, as an
argument, a function, you might call it f,
of type ℕ → ℕ. It must return a function,
also of type ℕ to ℕ, that, when applied
to a value, n, returns the result of
applying the given function, f, to the
given value, n, three times. The function
returned must compute f(f(f(n))) when it
is applied to an argument, n.
-/

def apply3 : _ :=
    λ f : _, _

/- 6.

The Lean libraries define a function,
string.length, that takes a string and
returns its length as a natural number.
Define a function, len2, that takes two
strings and returns the sum of their
lengths. You may use the ++ operator
but not the + operator in your answer.
Follow your function definition with a
test case in the form of a proof using
"example" showing that len2 applied to
"Orson" and "Welles" is 11. Remember:
you might need parenthesis in some
cases to group terms correctly into
larger terms.
-/



/- 7.
Use "example" to prove that there is a
function of the following type:

((ℕ → ℕ) → (ℕ → ℕ)) →
    ((ℕ → ℕ) → ℕ) →
        ((ℕ → ℕ) → ℕ)
-/



/-
PART II: Functions, revisited. In
mathematics,  functions play a central
role. A function, f, in the mathematical
sense is a triple, f = { D, P, C }, where
D, a set, is the domain of definition of
f, C is the co-domain of f, and P is a
set of ordered pairs, each with a first
element from D and a second element from
C,. In addition, P has one additional
essential  property, the subject of one
of the following questions.
-/

/- 8.

What one additional property is essential to
the definition of what it means for a triple,
{ D, P, C } to be a function?

Name the property. Answer:

Now explain precisely what it means:  "That there
are no two pairs, (x, y) and (x', y') such that..."

Fill in the blank, and use a logical ∧ in answering.
You might also want to use = or ≠.

Answer:
-/

/- 9.

Give names to the following concepts:

The set of all values appearing as the first
element of any pair in P.

Answer:

The set of all values appearing as the second
element of any pair in P.

Answer:

The property that the set of all values
appearing as the first element of P is the
same as the entire set, D.

Answer:

Answer: The property that the set of all
values appearing as the second element of
P is the same as the entire set, C.

Answer:

The property of being one-to-one and onto.

Answer:

-/

/- 10.

What does it mean for a function, f, to be
injective? Give you answer by completing the
following sentences with logical expressions.

"A function, f, is said to be injective if
it has no two pairs, (x, y) and (x', y'),
such that ..."

Answer:

In other words, "If (x, y) and (x', y') are
related by f and x ≠ x' then ..."

Answer:
-/


/- 11.

Suppose that S and T are types and that f
is defined to be a function, *in Lean*, of
type S → T. Which of the following properties,
if any, does f necessarily have?

- injective
- surjective
- bijective
- one-to-many
- one-to-one
- onto
- single-valued
- partial
- total

Answer:

-/

/-
PART III: Logic and Proof.
-/

/- 12a.

Use axiom and/or axioms in Lean to express,
in formal logic, the following assumptions:

- T is a type
- t1 and t2 are values of type T
- t1 = t2

Answer immediately after this comment block.
If you need to introduce a name, use eqt1t2.
-/



/- 12b.

Use axiom or axioms to represent the
additional assumptions that

- P is a predicate expressing a property of objects of type T
- t1 has property P

If you need to use a name, use Pt1
-/



/- 12 c.

Now use "example" to assert, and then
prove, that t2 also has property P.
-/


/- 13 a.
Define eq_1_0 to be the proposition, 1 = 0.
-/



/- 13 b.
Define pf_eq_0_0 to be a proof of the
proposition that 0 = 0. Use the lemma
keyword.
-/


/- 13 c.
Write a function, w, that takes three
values, a, b, and c of type ℕ, and that
also takes proofs, cb : c = b, and
ba : b = a, and that returns a proof
that a = c.
-/



/- 13d.

What is the type of this function?

Answer:

What is the form of this proposition?

Answer:

What's the form the proposition after the
comma?

Answer:

What is the premise of the proposition after
the comma?

Answer:

-/

/- 14.
Complete the following proofs. Give each one
in the form indicated by a comment preceding
the statement of the conjecture to be proved.
When using tactic scripts, remember to write
begin/end pairs right away, so Lean knowns
you want to use a tactic script.
-/

-- lambda expression
example : ∀ (s : string), s = s :=
_


-- lambda expresion
example : ∀ (n : ℕ), ∀ (m : ℕ), true :=
_


-- tactic script
example : ∀ (T : Type), ∀ (t : T), eq t t :=
_


-- tactic script
example :
    ∀ (T : Type),
    ∀ (P : T → Prop),
    ∀ t1 t2 : T,
    ∀ Pt1 : P t1,
    ∀ t2t1 : t2 = t1,
    P t2 :=
_

/-
The following problems involve implications.
For example, false → P in an implication. To
prove an implication, just show that there is
(give) a function of the specified type.
-/

-- lambda expression
example : ∀ (P : Prop), false → P :=
_


-- tactic script
example : ∀ (P : Prop), false → P :=
_


-- lambda expression
example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
_

-- tactic script
example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
_



-- tactic script
example :
    ∀ T : Type,
    ∀ (t1 t2 t3 : T),
    t1 = t2 ∧ t2 = t3 → t1 = t3 :=
_


/- 15.

Use Lean to model a world in which there
are Dogs, all Dogs are friendly, and Fido
is a Dog, with a proof that in this world,
Fido must be friendly, too.
-/
