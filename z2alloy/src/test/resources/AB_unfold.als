sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig B{
        a: set  A,
}{pred_B[a]}
pred pred_B[ a: set  A] {}
some_B : run { some B }
