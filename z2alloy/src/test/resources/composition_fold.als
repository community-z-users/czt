sig A{}

sig B{
	a: A,
}{(pred_B[a])}


pred pred_B[a: A] {}

sig DeltaB{
	a: A,
	a': A,
}{(pred_DeltaB[a, a'])}


pred pred_DeltaB[a: A, a': A] {}

sig C{
	a: A,
	a': A,
}{(pred_C[a, a'])}


pred pred_C[a: A, a': A] {
	((pred_DeltaB[a, a']) && (a = a'))
}

sig D{
	a: A,
	a': A,
}{(pred_D[a, a'])}


pred pred_D[a: A, a': A] {
	((pred_DeltaB[a, a']) && (! (a = a')))
}

sig E{
	a: A,
	a': A,
}{(pred_E[a, a'])}


pred pred_E[a: A, a': A] {
	some temp: B | ((pred_C[a, (temp . @a)]) && (pred_D[(temp . @a), a']))
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

