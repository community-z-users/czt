open util/integer

sig A{
	a: Int,
	b: Int,
}{(pred_A[a, b])}


pred pred_A[a: Int, b: Int] {
	a = b
}

sig B{
	a: Int,
}{(pred_B[a])}


pred pred_B[a: Int] {
	a > 1
}

sig C{
	b: Int,
}{(pred_C[b])}


pred pred_C[b: Int] {
	b = 3
}

sig D{
	b: Int,
	a: Int,
}{(pred_D[b, a])}


pred pred_D[b: Int, a: Int] {
	((pred_A[a, b]) && (pred_B[a])) || (pred_C[b])
}

sig E{
	b: Int,
	a: Int,
}{(pred_E[b, a])}


pred pred_E[b: Int, a: Int] {
	(pred_A[a, b]) || (pred_B[a])
	pred_C[b]
}

sig F{
	b: Int,
	a: Int,
}{(pred_F[b, a])}


pred pred_F[b: Int, a: Int] {
	((pred_A[a, b]) <=> (pred_B[a])) => (pred_C[b])
}

sig G{
	b: Int,
	a: Int,
}{(pred_G[b, a])}


pred pred_G[b: Int, a: Int] {
	((pred_A[a, b]) => (pred_B[a])) <=> (pred_C[b])
}


