sig A{}

sig B{
	a: (set  (Int -> A)),
	b: (set  (Int -> A)),
	c: (set  (Int -> A)),
	d: (set  (Int -> A)),
	e: A,
}{(pred_B[a, b, c, d, e])}


pred pred_B[a: (set  (Int -> A)), b: (set  (Int -> A)), c: (set  (Int -> A)), d: (set  (Int -> A)), e: A] {
	(((((a in (seq A)) && (b in (seq A))) && (c in (seq A))) && (d in (seq A))) && (((a = (append[b, c])) && (e = (last[a]))) && (d = (front[a]))))
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


