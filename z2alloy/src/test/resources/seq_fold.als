sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig B{
        a: seq A,
        b: seq A,
        c: seq A,
}{pred_B[a, b, c]}
pred pred_B[ a: seq A, b: seq A, c: seq A] {
	a = append[b, c]
}
some_B : run { some B }
