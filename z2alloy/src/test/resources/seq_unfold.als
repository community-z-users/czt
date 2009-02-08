sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig BStart0{
        a: Int -> A,
        b: Int -> A,
        c: Int -> A,
}{pred_BStart0[a, b, c]}
pred pred_BStart0[ a: Int -> A, b: Int -> A, c: Int -> A] {
	a in (seq A)
	b in (seq A)
	c in (seq A)
	a = append[b, c]
}
some_BStart0 : run { some BStart0 }
