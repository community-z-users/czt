sig A{}

sig B{
	a: A,
}{(pred_B[a])}


pred pred_B[a: A] {}

sig C{
	as: A,
}{(pred_C[as])}


pred pred_C[as: A] {
	some a: A | ((pred_B[a]) && (a = as))
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


