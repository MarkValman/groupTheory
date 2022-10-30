predicate IsSubset(A: set, B: set) // <=
{
	forall n :: n in A ==> n in B // same as the next line
	//forall n :: if n in A then n in B else true // same as "A <= B"
}

lemma {:verify true} transitiveOfSetInclusion (A: set, B: set, C: set)
    requires Pre1: IsSubset(A,B)
    requires Pre2: IsSubset(B, C)
    ensures IsSubset(A, C)
{
    assert forall 
}