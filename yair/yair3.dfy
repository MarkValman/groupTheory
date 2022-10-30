///////////////////////////
// Function returning the difference between two groups
// A = {1, 2, 3, 4, 5}, B = {5, 6, 1, 2}
// A - B = {3, 4}
///////////////////////////

// "(A: set, B: set)" - function input, ": set" - function output
function setDifference(A: set, B: set): set
{
    // set of all the x's, belong to A, and (וגם) not belong to B
    set x | x in A && x !in B
}


///////////////////////////
// Function returning the intersection (חיתוך) between two groups
// A = {1, 2, 3, 4, 5}, B = {5, 6, 1, 2}
// A*B = {1, 2, 5}
///////////////////////////

function setIntersection(A: set, B: set): set
{
    set x | x in A && x in B
}


///////////////////////////
// Lemma to prove that Intersection of two sets it's subset of both of them
// A = {1, 2, 3, 4, 5}, B = {5, 6, 1, 2}
// A*B = {1, 2, 5} = C
// C < A && C < B 
///////////////////////////

// Way 1
// כל תיאור של הלמה עד הסוגריים מסולסלות - נקרא חתימה
// הוכחה נמצאת בתוך סןגריים מסולסלות
// lemma intersectionIsSubsetOfBoth(A: set, B: set, C: set)
//     requires C == A*B;
//     ensures C <= A && C <= B;
// {
//     forall x | x in C ensures x in A && x in B {
//         assert 3: x in A*B;
//         assert 4: x in A by {reveal 3;}
//         assert 5: x in B by {reveal 3;}
//         assert x in C by {reveal 3, 4 , 5;}
//     }
// }

// Way 2
// lemma intersectionIsSubsetOfBoth2(A: set, B: set, C: set)
//     requires Pre1 : C == setIntersection(A, B);
//     ensures IsSubset(C, A);
//     ensures IsSubset(C, B);
// {
//     assert IsSubset(C, A) by {
//         assert forall x | x in C ==> x in A by { 
//             forall m | m in C ensures m in A {}
//         }
//     }
// }

// My way
lemma intersectionIsSubsetOfBoth(A: set, B: set, C: set)
    requires pre: C == A*B;
    ensures C <= A;
    ensures C <= B;
{
    assert C <= A by {
        // When writing ==> we cant use x outside of scoupe. So we use "::" instead of "|"
        // And after "b" we assert the same thing again with another symbol
        assert forall x :: x in C ==> x in A by {
            assert forall m | m in C ==> m in A;
        }
        assert L1: m in C;
        assert L2: m in A && m in B by { reveal pre,L1;}
        assert m in A;

    }
}

