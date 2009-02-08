sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig BStart0{
        a: seq A,
        b: seq A,
        c: seq A,
}{pred_BStart0[a, b, c]}
pred pred_BStart0[ a: seq A, b: seq A, c: seq A] {
	a = append[b, c]
}
some_BStart0 : run { some BStart0 }
