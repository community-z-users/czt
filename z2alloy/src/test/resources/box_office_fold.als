sig Seat{}

sig Customer{}

sig BoxOffice{
	seating: (set  Seat),
	sold: (Seat ->lone Customer),
}{(pred_BoxOffice[seating, sold])}


pred pred_BoxOffice[seating: (set  Seat), sold: (Seat ->lone Customer)] {
	((dom[sold]) in seating)
}

enum Month{jan, feb, mar, apr, may, jun, jul, aug, sep, oct, nov, dec}

sig Date{
	month: Month,
	day: {i: Int | ((i >= 1) && (i <= 31))},
}{(pred_Date[month, day])}


pred pred_Date[month: Month, day: {i: Int | ((i >= 1) && (i <= 31))}] {
	((month in (((sep + apr) + jun) + nov)) => (day <= 30))
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


