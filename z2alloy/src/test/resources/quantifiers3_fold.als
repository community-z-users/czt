open util/integer

sig A{
	x: Int,
	y: Int,
	z: Int,
}{(pred_A[x, y, z])}


pred pred_A[x: Int, y: Int, z: Int] {}

sig B{
	x: Int,
	a: (set  Int),
}{(pred_B[x, a])}


pred pred_B[x: Int, a: (set  Int)] {}

sig B2{
	x: Int,
	a: (set  Int),
}{(pred_B2[x, a])}


pred pred_B2[x: Int, a: (set  Int)] {}

sig C{
	x: Int,
	a: (set  Int),
}{(pred_C[x, a])}


pred pred_C[x: Int, a: (set  Int)] {
	some A_temp: A | (pred_B[(A_temp . x), a])
}

sig D{
	x: Int,
	a: (set  Int),
}{(pred_D[x, a])}


pred pred_D[x: Int, a: (set  Int)] {
	some A_temp: A | ((pred_B[(A_temp . x), a]) && (pred_B2[(A_temp . x), a]))
}

sig E{
	x: Int,
	a: (set  Int),
}{(pred_E[x, a])}


pred pred_E[x: Int, a: (set  Int)] {
	some x: Int | (pred_B[x, a])
}

sig F{
	x: Int,
	a: (set  Int),
}{(pred_F[x, a])}


pred pred_F[x: Int, a: (set  Int)] {
	some x: Int, A_temp: A | ((pred_B[(A_temp . x), a]) && ((A_temp . x) = x))
}

sig G{
	x: Int,
	a: (set  Int),
}{(pred_G[x, a])}


pred pred_G[x: Int, a: (set  Int)] {
	some x: Int | ((pred_B[x, a]) && (x > 5))
}

sig H{
	x: Int,
	a: (set  Int),
}{(pred_H[x, a])}


pred pred_H[x: Int, a: (set  Int)] {
	some A_temp: A | ((pred_B[(A_temp . x), a]) && ((A_temp . x) > 5))
}

sig I{
	x: Int,
}{(pred_I[x])}


pred pred_I[x: Int] {
	some a: (set  Int) | (pred_B[x, a])
}

sig J{
}{(pred_J[])}


pred pred_J[] {
	some x: Int, a: (set  Int) | (pred_B[x, a])
}


