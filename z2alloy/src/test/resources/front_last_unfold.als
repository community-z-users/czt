sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig B{
        x: Int -> A,
        y: A,
        z: Int -> A,
}{pred_B[x, y, z]}
pred pred_B[x: Int -> A, y: A, z: Int -> A] {
	x in (seq A)
	z in (seq A)
	y = seq/last[x]
	z = seq/butlast[x]
}
some_B : run { some B }
