open util/integer

sig A{}

sig B{
	a: A,
	b: A,
}{(pred_B[a, b])}


pred pred_B[a: A, b: A] {
	a = b
}

sig DeltaB{
	a: A,
	a': A,
	b: A,
	b': A,
}{(pred_DeltaB[a, a', b, b'])}


pred pred_DeltaB[a: A, a': A, b: A, b': A] {
	pred_B[a, b]
	pred_B[a', b']
}

sig C{
	a: A,
	a': A,
	b: A,
	b': A,
}{(pred_C[a, a', b, b'])}


pred pred_C[a: A, a': A, b: A, b': A] {
	pred_DeltaB[a, a', b, b']
}

sig XiB{
	a: A,
	a': A,
	b: A,
	b': A,
}{(pred_XiB[a, a', b, b'])}


pred pred_XiB[a: A, a': A, b: A, b': A] {
	a = a'
	b = b'
	pred_B[a, b]
	pred_B[a', b']
}

sig D{
	a: A,
	a': A,
	b: A,
	b': A,
}{(pred_D[a, a', b, b'])}


pred pred_D[a: A, a': A, b: A, b': A] {
	pred_XiB[a, a', b, b']
}