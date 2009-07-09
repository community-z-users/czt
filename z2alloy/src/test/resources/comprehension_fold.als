sig B{}

sig A{
	fun: (B ->lone B),
}{(pred_A[fun])}


pred pred_A[fun: (B ->lone B)] {
	({temp: B | ((1 = 1) && some i: (dom[fun]) | ((i . fun) = temp))} = B)
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

