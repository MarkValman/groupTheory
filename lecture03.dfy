// include "lecture02.dfy"

// predicate isSubset(A: set, B: set)
// {
//     forall n :: n in A ==> n in B // for all objects n in set A, they also objects in set B. same as "A <= B"
// }

// lemma intersectionIsSubsetofBoth(A: set, B: set, C: set) // Lemma - טענה, Name, Parameters
//     requires pre: C == setIntersection(A, B) // == A*B, Requiers for parameters
//     ensures isSubset (C, A) // C <= A
//     ensures isSubset (C, B) // C <= B
// { // הוכחת נכונות
//   // Post 1:
//     assert isSubset(C,A) by {
//             forall n | n in C ensures n in A {
//                 assert L1; n in C; // we know this
//                 assert n in A && n in B; {reveal pre,L1; }// by the deffinition of setIntersection
//                 assert n in A; // by { reveal pre; } this is what we need to prove
//             }
//         }
// }

lemma andMeansBoth(P: bool, Q: bool) // Lemma - טענה, Name, Parameters with DataTypes
    ensures P && Q ==> P // ensure that if P and Q = True, then P = True. For ex. P || Q ==> P: It's wrong cause if only Q = True, this is NOT ensures that P = True. 
    ensures P && Q ==> Q // ensure that if P and Q = True, then Q = True
{}

 