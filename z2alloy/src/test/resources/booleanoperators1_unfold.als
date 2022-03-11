open util/integer

sig A{}

sig B{
	a1: A,
	a2: A,
}{(pred_B[a1, a2])}


pred pred_B[a1: A, a2: A] {
	(a1 = a2) => (a1 = a2)
	(a1 = a2) <=> (a1 = a2)
	! (a1 = a2)
	a1 = a2
	(a1 = a2) || (a1 = a2)
}