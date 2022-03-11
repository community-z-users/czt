open util/integer

sig A{}

sig B{
	a: A,
	b: A,
}{(pred_B[a, b])}


pred pred_B[a: A, b: A] {
	a = b
}

sig C{
	a: A,
	b: A,
	a': A,
	b': A,
}{(pred_C[a, b, a', b'])}


pred pred_C[a: A, b: A, a': A, b': A] {
	a = b
	a' = b'
}

sig D{
	a: A,
	b: A,
	a': A,
	b': A,
}{(pred_D[a, b, a', b'])}


pred pred_D[a: A, b: A, a': A, b': A] {
	a = b
	a' = b'
	a = a'
	b = b'
}