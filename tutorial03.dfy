/*
	tutorial 3: truth tables + first proofs with "forall ... ensures"
*/

/*

A questions from last year's exam:

בהינתן הנוסחה
(p ==> (q && r)) <==> ((p ==> q) || (p ==> r))
בכמה מתוך 8 השורות בטבלת האמת של נוסחה זו הערך הינו True ?

 p  q  r  "q && r"  "p ==> (q && r)"  "p ==> q"  "p ==> r"   "(p ==> q) || (p ==> r)"    "(p ==> (q && r)) <==> ((p ==> q) || (p ==> r))"
 F  F  F  F         T                 T          T           T                           T
 F  F  T  F         T                 T          T           T                           T
 F  T  F  F         T                 T          T           T                           T
 F  T  T  T         T                 T          T           T                           T
 T  F  F  F         F                 F          F           F                           T
 T  F  T  F         F                 F          T           T                           F
 T  T  F  F         F                 T          F           T                           F
 T  T  T  T         T                 T          T           T                           T

תשובה: 6

*/

include "lecture03.dfy"

lemma TheEmptySetIsASubsetOfAnySet<T>(A: set<T>)
    ensures IsSubset({}, A)
{
	forall n | n in {} ensures n in A {
		assert L1: n in {}; // by the "|" above
		assert L2: n !in {} by { TheEmptySetIsIndeedEmpty<T>(); }
		// we reached a contradiction!
		assert P: false by { reveal L1,L2; }
		assert Q: false ==> n in A; // since false implies anything (for any P, "false ==> P")
		assert n in A by { reveal P,Q; ModusPonens(false, n in A); } // let's return to that next week!
	}
}

lemma TheEmptySetIsIndeedEmpty<T>()
	ensures forall s: set<T>, n: T :: s == {} ==> n !in s
{}

lemma ModusPonens(P: bool, Q: bool)
	requires P ==> Q
	requires P
	ensures Q
{}

lemma SelfSubset'(A: set)
    ensures IsSubset(A, A)
{
	forall n | n in A ensures n in A {
		assert L1: n in A; // by the "|" above
		assert n in A by { reveal L1; }
	}
}