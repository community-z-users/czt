open util/integer

sig A{
	a: (set  Int),
}{(pred_A[a])}


pred pred_A[a: (set  Int)] {
	all x: Int | ((x >= 1) => (x in a))
	some x: Int | ((x >= 1) && (x in a))
	one x: Int | ((x >= 1) && (x in a))
	all x: Int | (x in a)
	some x: Int | (x in a)
	one x: Int | (x in a)
	all x: Int, y: Int | ((x >= 1) => (x in a))
	some x: Int, y: Int | ((x >= 1) && (x in a))
	one x: Int, y: Int | ((x >= 1) && (x in a))
}


