/* 
Mark Valman
342439593
*/

/* 
מטלה 2 - הגדרת קבוצות, יחסים בינאריים, יחסי שקילות ויחס סדר חלקי

במטלה זו 7 תרגילים
בתרגילים 1 עד 5 יש להשלים את ההגדרות כך שכל פקודות האסרט יהיו נכונות
בתרגילים 6 ו-7 יש לספק הוכחת נכונות באופן מפורט כפי שלמדנו

השלמת ההגדרות מתבצעת על ידי הוספת סוגריים מסולסלות לכל החלקים התכנית שמופיעים ללא סוגריים
למשל בתרגיל הראשון, יש לספק הגדרה ל-4 הפונקציות
f1a,f1b,f1c,f1d

ההגשה בזוגות עד יום ג' 6/9
*/

include "definitions_until_lecture08.dfy"

ghost const R1 := iset a,b | a == 4 || a+b == 4 :: (a,b)

function f1a(): (int,int) { (4,0)} // יש להשלים את ההגדרה בשורה הבאה

function f1b(): (int,int)  {(3,2)}// יש להשלים את ההגדרה בשורה הבאה

function f1c(): (int,int) {(4,1)}// יש להשלים את ההגדרה בשורה הבאה

function f1d(): (int,int){(0,4)}// יש להשלים את ההגדרה בשורה הבאה

ghost const AllPairs1 := {f1a(), f1b(), f1c(), f1d()}

method {:verify true} Q1()
{
	assert |AllPairs1| == 4;
	var p := f1a();
	assert p in R1 by { assert p.0 == 4 && p.0 + p.1 == 4; }
	p := f1b();
	assert p !in R1;
	p := f1c();
	assert p.0+p.1 != 4;
	assert p in R1 by { assert p.0 == 4; }
	p := f1d();
	assert p.0 != 4;
	assert p in R1 by { assert p.0 + p.1 == 4; }
}

// תרגיל 2: יחסים בינאריים, יחס על קבוצה, רפלקסיביות, טרנזיטיביות וסימטריה
function f2a(): BinaryRelation<int, int>
{
	iset{(1,1), (1,2), (1,5), (2,2), (2,4), (3,1), (4,2), (4,5), (5,3)}
}

function f2b(): BinaryRelation<int, int> 
{iset{(1,5),(2,4),(4,2),(4,5),(5,3)}}  // יש להשלים את ההגדרה בשורה הבאה

function f2c(): BinaryRelation<int, int>
 {iset{(3,3),(2,1),(3,2)} }// יש להשלים את ההגדרה בשורה הבאה

ghost const A2: iset<int> := iset{1,2,3};
ghost const R2: BinaryRelation<int, int> := (f2a() - f2b()) + f2c();

method {:verify true} Q2()
{
	assert f2a() !! f2c();
	assert f2b() < f2a();
	assert forall p :: p in f2b() ==> p.0 !in A2 || p.1 !in A2;
	assert RelationOn(R2, A2);
	assert Reflexive(R2, A2);
	assert Transitive(R2);
	assert !EquivalenceRelation(R2, A2) by {
		assert !Symmetric(R2);
	}
}


// // תרגיל 3: יחסי שקילות, מחלקת שקילות
function f3a(): BinaryRelation<int, int>
{
	iset{(1,1), (1,2), (1,5), (2,2), (2,4), (3,1), (4,2), (4,5), (5,3)}
}

function f3b(): BinaryRelation<int, int> // יש להשלים את ההגדרה בשורה הבאה
{iset{(1,2),(2,4),(4,2),(4,5)}}

function f3c(): BinaryRelation<int, int> // יש להשלים את ההגדרה בשורה הבאה
  {iset{(3,3),(4,4),(5,5),(1,3),(3,5),(5,1)}}
ghost const A3: iset<int> := iset{1,2,3,4,5};
ghost const R3: BinaryRelation<int, int> := (f3a() - f3b()) + f3c();

method {:verify true} Q3()
{
	assert f3a() !! f3c();
	assert f3b() < f3a();
	assert EquivalenceRelation(R3, A3);
	assert EquivalenceClassOf(1, A3, R3) == iset{1,3,5};
}



// תרגיל 4: יחס סדר חלקי - רפלקסיביות, טרנזיטיביות ואנטי-סימטריה
ghost const R4a: BinaryRelation<int, int> := iset{(5,5), (5,3), (4,4), (3,5), (3,3), (2,2)}
ghost const R4b: BinaryRelation<int, int> := iset{(5,5), (5,3), (4,4), (3,3), (3,2), (2,2)}
ghost const R4c: BinaryRelation<int, int> := iset{}
ghost const R4d: BinaryRelation<int, int> := iset{(5,5), (5,4), (4,4), (3,3), (3,2), (2,2)}

ghost const A4: iset<int> := iset{2,3,4,5}

ghost const AllR4 := {R4a, R4b, R4c, R4d}

function f4a(): BinaryRelation<int, int> // יש להשלים את ההגדרה בשורה הבאה
{R4d}
function f4b(): BinaryRelation<int, int> // יש להשלים את ההגדרה בשורה הבאה
{R4c}
function f4c(): BinaryRelation<int, int> // יש להשלים את ההגדרה בשורה הבאה
{R4b}
function f4d(): BinaryRelation<int, int> // יש להשלים את ההגדרה בשורה הבאה
{R4a}
method {:verify true} Q4()
{
	assert f4a() in AllR4 && f4b() in AllR4 && f4c() in AllR4 && f4d() in AllR4;
	assert IsPartialOrder(f4a(), A4);
	assert !IsPartialOrder(f4b(), A4) by { assert !Reflexive(f4b(), A4); }
	assert !IsPartialOrder(f4c(), A4) by { assert !Transitive(f4c()); }
	assert !IsPartialOrder(f4d(), A4) by { assert !AntiSymmetric(f4d()); }
}



// תרגיל 6: הוכחת טענה על התחום של היחס ההופכי - הוכיחו בצורה מפורטת כפי שלמדנו
lemma Q6_InverseDomain<T(!new)>(R: BinaryRelation<T,T>, InverseR: BinaryRelation<T,T>, A: iset<T>)
	requires pre1: RelationOn(R, A)
	requires pre2: InverseR == InverseRelation(R)
	ensures Range(R) == Domain(InverseR)
{
	reveal pre1, pre2;
		assert Range(R) == Domain(InverseR) by {
			calc {
				Range(R);
				==
				iset x,y | (x, y) in R :: y;
				==
				iset x, y | (x, y) in InverseR :: x;
				==
				Domain(InverseR);
			}
		}
}


// תרגיל 7: הוכחת טענה לגבי יחס סדר חלקי - הוכיחו בצורה מפורטת כפי שלמדנו
lemma Q7_GE_IsPartialOrder(R: BinaryRelation<int,int>, A: iset<int>)
    requires pre1: RelationOn(R, A)
    requires pre2: R == Q7_GE_Relation(A)
	 ensures IsPartialOrder(R, A)
{
	reveal pre1, pre2;
	assert Transitive(R) by {
		forall a, b, c | (a,b) in R && (b,c) in R ensures (a,c) in R{
		assert 1 : a >= b && b >= c;
		assert 2 : a >= c by{reveal 1;}
		assert 3 : (a,c) in R by {reveal 2;}
		}
	}
	assert Reflexive(R, A) by {
		forall a | a in A ensures (a,a) in R {
		assert 4 : a in A;
		assert 5 : a >= a;
		assert 6 : (a,a) in R;
		}
	}

assert AntiSymmetric(R) by {
	forall a,b | (a,b) in R && (b,a) in R ensures a == b{
	assert 7 : a >= b;
	assert 8 : b >= a;
	assert 9 : a == b; 	
	}
}

assert IsPartialOrder(R, A);

}

function Q7_GE_Relation(A: iset<int>): BinaryRelation<int,int>
{
	iset x,y | x in A && y in A && x >= y :: (x,y)
}