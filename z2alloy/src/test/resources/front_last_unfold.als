open util/integer

sig A{}

sig B{
	x: (set  (Int -> A)),
	y: A,
	z: (set  (Int -> A)),
}{(pred_B[x, y, z])}


pred pred_B[x: (set  (Int -> A)), y: A, z: (set  (Int -> A))] {
	(((x in (seq A)) && (z in (seq A))) && ((y = (last[x])) && (z = (front[x]))))
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


