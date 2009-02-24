sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig B{
        a: Int -> A,
        b: Int -> A,
        c: Int -> A,
}{pred_B[a, b, c]}
pred pred_B[ a: Int -> A, b: Int -> A, c: Int -> A] {
	a in (seq A)
	b in (seq A)
	c in (seq A)
	a = append[b, c]
}
some_B : run { some B }
