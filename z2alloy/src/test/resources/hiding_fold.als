open util/integer

sig A{
	i: {i: Int | (i >= 0)},
}{(pred_A[i])}


pred pred_A[i: {i: Int | (i >= 0)}] {
	(i > 5)
}

sig B{
	i: {i: Int | (i >= 0)},
	j: {i: Int | (i >= 0)},
}{(pred_B[i, j])}


pred pred_B[i: {i: Int | (i >= 0)}, j: {i: Int | (i >= 0)}] {
	(j > i)
}

sig C{
}{(pred_C[])}


pred pred_C[] {
	some i: {i: Int | (i >= 0)} | (pred_A[i])
}

sig D{
	j: {i: Int | (i >= 0)},
}{(pred_D[j])}


pred pred_D[j: {i: Int | (i >= 0)}] {
	some i: {i: Int | (i >= 0)} | ((pred_A[i]) && (pred_B[i, j]))
}

fun ndres[ex: (set  univ), r: (univ -> univ)] : (univ -> univ) {
	(((dom[r]) - ex) <: r)
}

fun append[s1: (seq univ), s2: (seq univ)] : (seq univ) {
	(seq/append[s1, s2])
}

fun dom[r: (univ -> univ)] : (set  univ) {
	(r . univ)
}

fun last[s: (seq univ)] : (one  univ) {
	(seq/last[s])
}

fun front[s: (seq univ)] : (seq univ) {
	(seq/butlast[s])
}

