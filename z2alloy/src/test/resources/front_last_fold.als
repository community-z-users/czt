sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig B{
        x: seq A,
        y: A,
        z: seq A,
}{pred_B[x, y, z]}
pred pred_B[ x: seq A, y: one  A, z: seq A] {
	y = seq/last[x]
	z = seq/butlast[x]
}
some_B : run { some B }
