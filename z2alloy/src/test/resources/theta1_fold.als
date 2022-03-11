open util/integer

sig A{
	i: Int,
}{(pred_A[i])}


pred pred_A[i: Int] {
	i > 5
}

sig B{
	i: Int,
}{(pred_B[i])}


pred pred_B[i: Int] {
	i > 6
}

sig C{
	i: Int,
}{(pred_C[i])}


pred pred_C[i: Int] {
	pred_B[i]
	pred_A[i]
	some a: A, b: B | ((((b . @i) = i) && ((a . @i) = i)) && (a = b))
}


