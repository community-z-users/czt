enum A{A1, A2}

sig ASet{
	aset: (set  A),
}{(pred_ASet[aset])}


pred pred_ASet[aset: (set  A)] {}

sig B{
	aset: (set  A),
}{(pred_B[aset])}


pred pred_B[aset: (set  A)] {
	((pred_ASet[aset]) && all a: aset | (a = A1))
}

sig C{
	aset: (set  A),
}{(pred_C[aset])}


pred pred_C[aset: (set  A)] {
	((pred_ASet[aset]) && some a: aset | (a = A1))
}

sig D{
	aset: (set  A),
}{(pred_D[aset])}


pred pred_D[aset: (set  A)] {
	((pred_ASet[aset]) && one a: aset | (a = A1))
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


