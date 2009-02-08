 
abstract sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

one sig A1 extends A{
}{pred_A1[]}
pred pred_A1[ ] {}
some_A1 : run { some A1 }

one sig A2 extends A{
}{pred_A2[]}
pred pred_A2[ ] {}
some_A2 : run { some A2 }

sig ASet{
        aset: set  A,
}{pred_ASet[aset]}
pred pred_ASet[ aset: set  A] {}
some_ASet : run { some ASet }

sig B{
        aset: set  A,
}{pred_B[aset]}
pred pred_B[ aset: set  A] {
	all a: aset | a = A1
}
some_B : run { some B }

sig C{
        aset: set  A,
}{pred_C[aset]}
pred pred_C[ aset: set  A] {
	some a: aset | a = A1
}
some_C : run { some C }

sig D{
        aset: set  A,
}{pred_D[aset]}
pred pred_D[ aset: set  A] {
	one a: aset | a = A1
}
some_D : run { some D }
