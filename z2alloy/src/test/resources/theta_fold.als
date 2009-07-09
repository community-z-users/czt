sig A{
	i: Int,
}{(pred_A[i])}


pred pred_A[i: Int] {
	(i > 5)
}

sig DeltaA{
	i: Int,
	i': Int,
}{(pred_DeltaA[i, i'])}


pred pred_DeltaA[i: Int, i': Int] {}

sig B{
	i: Int,
	i': Int,
}{(pred_B[i, i'])}


pred pred_B[i: Int, i': Int] {
	(some a: A, a': A | ((pred_DeltaA[i, i']) && (((a . @i) = i) && ((a' . @i) = i'))) && (a = a'))
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

