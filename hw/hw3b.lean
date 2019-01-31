/-
CS 2102 Spring 2019 Homework #3b

The first part of your homework this week is to make
a new copy of the *blank* homework #2 assignment in
your "work" directory, now called "hw3a.lean", then
complete the questions that you did *not* complete 
last week. To rename the file after copying it, click
on the file name, hit enter, then enter a new name for
the file.

This file contains the second half of the homework for
this week, which everyone in CS2102 is to complete.

The purpose of this part of the homework assignment 
for this week is to help you learn how to write 
propositions of various kinds in formal predicate 
logic.
-/

/-
To this end, you are to translate the informally 
stated propositions we give you into formal and 
mechanically checked propositions using Lean. 

To prepare to do this work, we strong recommend 
that you reread the very recently updated version 
of Chapter 2.5 in the notes, on Propositions. 

So here we go.
-/

/-
#1. 10 points

To start, write the Lean code using the axiom keyword
needed to introduce the assumptions that "ItsRaining" 
and "TheStreetsAreWet" are propositions. Write your
answer just below this comment block and before the
next one.
-/

-- Your answer here


/-
#2. 90 points

Now, write formal (using Lean) versions of each of 
the following informally stated propositions. Do this
by writing your expressions in place of the underscore
characters in the following incomplete definitions. 
-/

/- If it's raining, then the streets are wet. -/

def p1 : Prop := _

/- It's raining and the streets are wet. -/

def p2 : Prop := _

/- It's not raining. -/

def p3 : Prop := _

/- It's raining or the streets are wet. -/

def p4 : Prop := _

/- It's raining if and only if the streets are wet. -/

def p5 : Prop := _

/- It's raining or the streets are not wet. -/

def p6 : Prop := _

/- 
If it's raining then (if the streets are wet then 
it's raining).  
-/

def p7 : Prop := _

/-
If (if it's raining then the streets are wet) then
it's raining.
-/

def p8 : Prop := _

/-
If the streets are wet and it's raining then 
the streets are wet. 
-/

def p9 : Prop := _

/-
The streets are wet and the streets are not wet 
implies a contradiction (false).
-/

def p10 : Prop := _
