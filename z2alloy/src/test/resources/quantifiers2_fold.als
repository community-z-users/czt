open util/integer

sig X{
	x: Int,
}{(pred_X[x])}


pred pred_X[x: Int] {}

sig A{
	a: (set  Int),
}{(pred_A[a])}


pred pred_A[a: (set  Int)] {
	all x: Int | (((x >= 1) && (pred_X[x])) => (x in a))
	some x: Int | (((x >= 1) && (pred_X[x])) && (x in a))
	one x: Int | (((x >= 1) && (pred_X[x])) && (x in a))
	all x: Int | ((pred_X[x]) => (x in a))
	some x: Int | ((pred_X[x]) && (x in a))
	one x: Int | ((pred_X[x]) && (x in a))
	all x: Int, y: Int | (((x >= 1) && (pred_X[x])) => (x in a))
	some x: Int, y: Int | (((x >= 1) && (pred_X[x])) && (x in a))
	one x: Int, y: Int | (((x >= 1) && (pred_X[x])) && (x in a))
}


