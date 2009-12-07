open util/integer

sig A{
	a: Int,
	b: Int,
	c: Int,
}{(pred_A[a, b, c])}


pred pred_A[a: Int, b: Int, c: Int] {
	a = (integer/negate[a])
	a = (integer/sub[b, c])
	a = (integer/add[b, c])
	a = (integer/mul[b, c])
	a = (integer/div[b, c])
	a = (integer/rem[b, c])
	a < b
	a <= b
	a > b
	a >= b
	a = (integer/next[b])
}


