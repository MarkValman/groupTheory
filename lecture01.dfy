/*

Logic and Set Theory - lecture 1

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hourse: Wednesdays 18-20 (בתיאום מראש, במייל)

Today: introduction to logic:
- syntax and semantics
- propositions: atomic and composite
- truth tables
- logical connectors/operators: conjunction, disjunction, negation, implication (later in the semester), equivalence

Language: Dafny
Recommended Environment: Visual Studio Code (VS Code)

Q26:

B said that A said that A is a Knave

due to P below, B must be lying

if (C is a knight) {
	C is a knight
	C said that B is a knave
	B must be a knave
	A said that A is a Knight
}
else {
	C is Knave
	B is knight
	A said he was a knave
	which contradicts P below!!!
}
C must be a knight, B must be a knave!!!

if (A is Knave) {
	A would answer that he is a knight
}
else {
	A is a knight
	A would answer that he is a knight
}
P: So anyway A would anser he was a knight!!!

 Naively, we could have examined all cases:

S is the set of all Knights
if S == {A,B,C} NO
else if S == {A,B} NO 
else if S == {B,C} NO
else if S == {A,C} good 
else if S == {} NO 
else if S == {A} NO 
else if S == {B} NO 
else if S == {C} good

Q28

A makes the following statement: "At least one of us is a knave"
(in other words: A is knave || B is knave)

If A is knave, we know that !(A is knave || B is knave)
And according to the De Morgan (1) law (see below), this is logically equivalent to:
!(A is knave) && !(B is knave) which is in turn equivalent to:
A is knight && B is knight
so we reached a contraditiction (with the assumption that A was knave);

conclusion: the only possible option is that A is knight.
Since A said that at least one of them is knave, the only possible option is that
B is knave.

Answer: A is knight and B is knave

We needed help, since there's negation of a composite proposition!

The truth table of negation:

 P    !P
 F    T
 T    F

The truth table of conjunction (AND, &&):

 P  Q  (P && Q)
 F  F  F
 F  T  F
 T  F  F
 T  T  T

The truth table of disjunction (OR, ||):

 P  Q  (P || Q)
 F  F  F
 F  T  T
 T  F  T
 T  T  T (the so-called inclusive or, in contrast to exclusive-or)

What is the truth table of the proposition !(P || Q)

 P  Q  (P || Q)  !(P || Q)
 F  F  F         T
 F  T  T         F
 T  F  T         F
 T  T  T         F

De Morgan 1: negation of disjunction is the conjunction of the negations

!(P || Q) == !P && !Q

We need to check that the 4th column is equal to the 7th column:

 P  Q  (P || Q)  !(P || Q)   !P     !Q    (!P && !Q)
 F  F  F         T           T      T     T   
 F  T  T         F           T      F     F
 T  F  T         F           F      T     F
 T  T  T         F           F      F     F

Q29

A says "Either I am a knave or B is a knight."

P: A is knave
Q: B is knight

A says: P || Q

If A is a knight, B must be a knight too; why?

If A is knave, P is true, we have !(P || Q)
By De Morgan (1), this is:
!P && !Q
P and !P is a contradiction

P is false, A is a knight;
and Q? must be true! 

So we have !P and Q:
A is not a knave (it is a knight) and
B is a knight too.
*/
