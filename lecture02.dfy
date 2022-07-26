// set theory 
const s1 := {1, 9, 4} //extentional definition of a set
const s2 := {4, 9, 1, 4, 1}
const s3 := {1,4}

// Create methods only for proves of concept
// Can't changr const variable after creating, for ex. inside of method 

// working with separates variables
method extentionalMethod(){
    assert !(1 == 2); // or
    assert 1!=2;
    assert s1 == {4, 9, 1} == s2; //
    assert |s1| == |s2| == 3; // How many different symbols in group
    assert !(8 in s1); //or
    assert 8 !in s1;

    assert !(s3 == s1); // there's some elements not exists in set 1
    assert !(s3 == s1) by {
        assert 9 in s1 && 9 !in s3;
    } //Prove manually
}

//  working with set of variables
const allEvenNumbersBetween100And200 := set n: int  | 100 <= n <= 200 && n%2 == 0 // {100, 102, 104, ... ,200}

method intentionalMethod(){
    assert 158 in allEvenNumbersBetween100And200;
    assert 159 !in allEvenNumbersBetween100And200 by {
        assert 159%2 != 0;
    }
    assert 60 !in allEvenNumbersBetween100And200 by {
        assert 60 < 100;
    }
    assert 1580 !in allEvenNumbersBetween100And200 by {
        assert 1580 > 200;
    }
}


// a first operation on sets: union

const s4 := {"abc", "def"}
const s5 := {"abc", "ert"}
const s6 := s4 + s5;

method method3() {
  assert "abc" != "ABC"; // string in Dafny are case sensitive
  assert "" !in s6;
  assert "abc" in s6;
  assert s6 == {"abc", "def", "ert"};
  // "forall" is a quantifaier
  assert forall str: string :: (str in s6) <==> (str in s4 || str in s5);
}



// Operations on sets: Union
lemma setUnion (A: set<string>, B: set<string>, C: set<string>)
    requires C == A+B
    ensures forall str: string :: (str in C) <==> (str in A || str in B);
{}


// Operations os sets: intersection

const s7 := s4*s5;
const s7' := set stringi: string  | stringi in s4 && stringi in s5;

method method4() {
  assert "abc" != "ABC"; // string in Dafny are case sensitive
  assert "" !in s6;
  assert "abc" in s6;
  assert s6 == {"abc", "def", "ert"};
  assert s7 == {"abc"};
  assert forall str: string :: (str in s7) <==> (str in s4 && str in s5);
  assert s7' == s7;
}


lemma setIntersection (A: set<string>, B: set<string>, C: set<string>)
    requires C == A*B
    ensures forall str: string :: (str in C) <==> (str in A && str in B); 
{}

// Input: 2 Groups, Output: Group of intersection of this 2 groups
function setIntersectionFunction<T(!new)>(A: iset<T>, B: iset<T>): iset<T>{
    iset x | x in A && x in B
}

// ghost const s8 := setIntersectionFunction(s4, s5)

// method functionCallingMethod(){
//     assert s8 == s7' == s7;
// }