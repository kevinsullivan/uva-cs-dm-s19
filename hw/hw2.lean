/-
This is the second homework assignment for UVa CS2101, Spring 2019. 

If you are in Professor Sullivan's class, you are to complete problems 1 - 8. 
If you are in Prof. Hocking's class, you are to complete problems 9 - 13. 

The first eight problems require that you carefully read the updated class 
notes on relations vs. functions and on properties of functions: from the 
start of 2.4 through 2.4.4. For all of the remaining problems, you must 
have read the rest of the chapter, on higher-order functions. 

The collaboration policy for this assignment has two parts. First, you must
complete this work on your own. Second, please do not discuss your results
with anyone in the other professor's class, even after the deadline for the
homework has passed, as your assignment this week will be part of their 
assignment next week.

To complete this homework, first make a copy of this file in the "work" 
directory of your class repository. Do not edit this file directly in the 
hw directory. Make a copy first. Then fill in answers as required, save 
your changes, and submit your work by uploading the completed file on Collab.

Make a copy of this file in your work directory; complete the work using 
that copy; then upload the resulting file, after saving it, through Collab 
before the due date.
-/

/-
1. Is the function, G, as defined in the reading, total? Explain.

Answer here: 

-/


/-
2. Give an example of a value in the domain of definition the function, F, 
as defined in the reading, that proves that F is strictly partial, i.e., 
for which F is not defined.

Answer here: 

-/

/-
3. Give an example of a value in the codomain of F that proves that F is 
not surjective.

Answer here: 

-/


/-
4. Is our example function, G, strictly partial? Explain.

Answer here: 

-/


/-
5. Identify a value in the codomain of F that is not the image of any 
value value in its domain of definition.

Answer here: 

-/

/-
6. Translate our logical definition of injective into mathematically 
precise English following the examples for other properties of functions 
given in the reading.

Answer here: 

-/


/-
7. Is the function, f(x) = log(x) over the real numbers, injective? 
Is it surjective? Is it bijective? Explain each of your answers briefly.

Answer here: 

-/


/-
8. Is the relation, 3x^2 + 4y^2 = 4, single-valued? Explain your answers.

Answer here: 

-/

/-
Complete each of the following partial definitions in Lean by replacing 
the underscore characters with code to define functions of the specified 
types using lambda notation. We only care that you define some function 
of each required type, not what particular function you define.

In preparation, note that if you hover your mouse over an underscore, 
Lean will tell you what type of term you is needed to fill that hole. 
The type that Lean requires appears after the "turnstile" symbol, |-, 
in the message Lean will give you. Even more interestingly, if you 
fill in a hole with a term of the right type that itself has one or 
more remaining holes, Lean will tell you what types of terms are needed 
to fill in those holes! You can thus fill a hole in an incremental manner, 
refining a partial solution at each step until all holes are filled, 
guided by the types that Lean tells you are needed for any given hole. 
We recommend that you try developing your answers in this "top-down 
structured" style of programming. That said, we will grade you only on 
your answers and not on how you developed them.
-/

-- 9. 
def hw2_1: ℕ → ℕ :=
    λ(x: ℕ), 
        _


-- 10.
def hw2_2: ℕ → ℕ → ℕ :=
    _


-- 11.
def hw2_3: (ℕ → ℕ) → (ℕ → ℕ) :=
    _


-- 12.
def hw2_4: (ℕ → ℕ) → (ℕ → ℕ) :=
    _


-- 13.
def hw2_5: (ℕ → ℕ) → ((ℕ → ℕ) → (ℕ → ℕ)) :=
    _
