 
sig Seat{
}{pred_Seat[]}
pred pred_Seat[ ] {}
some_Seat : run { some Seat }

sig Customer{
}{pred_Customer[]}
pred pred_Customer[ ] {}
some_Customer : run { some Customer }

sig BoxOffice{
        seating: set  Seat,
        sold: Seat -> Customer,
}{pred_BoxOffice[seating, sold]}
pred pred_BoxOffice[ seating: set  Seat, sold: set  Seat -> Customer] {
	sold in Seat ->lone Customer and dom[sold] in seating
}
some_BoxOffice : run { some BoxOffice }

abstract sig Month{
}{pred_Month[]}
pred pred_Month[ ] {}
some_Month : run { some Month }

one sig jan extends Month{
}{pred_jan[]}
pred pred_jan[ ] {}
some_jan : run { some jan }

one sig feb extends Month{
}{pred_feb[]}
pred pred_feb[ ] {}
some_feb : run { some feb }

one sig mar extends Month{
}{pred_mar[]}
pred pred_mar[ ] {}
some_mar : run { some mar }

one sig apr extends Month{
}{pred_apr[]}
pred pred_apr[ ] {}
some_apr : run { some apr }

one sig may extends Month{
}{pred_may[]}
pred pred_may[ ] {}
some_may : run { some may }

one sig jun extends Month{
}{pred_jun[]}
pred pred_jun[ ] {}
some_jun : run { some jun }

one sig jul extends Month{
}{pred_jul[]}
pred pred_jul[ ] {}
some_jul : run { some jul }

one sig aug extends Month{
}{pred_aug[]}
pred pred_aug[ ] {}
some_aug : run { some aug }

one sig sep extends Month{
}{pred_sep[]}
pred pred_sep[ ] {}
some_sep : run { some sep }

one sig oct extends Month{
}{pred_oct[]}
pred pred_oct[ ] {}
some_oct : run { some oct }

one sig nov extends Month{
}{pred_nov[]}
pred pred_nov[ ] {}
some_nov : run { some nov }

one sig dec extends Month{
}{pred_dec[]}
pred pred_dec[ ] {}
some_dec : run { some dec }

sig Date{
        month: Month,
        day: Int,
}{pred_Date[month, day]}
pred pred_Date[ month: Month, day: Int] {
	day in { i: Int | i >= 1 and i <= 31} and (month in (sep + apr + jun + nov) => day <= 30)
}
some_Date : run { some Date }

fun dom[ r: (univ -> univ)] : set  univ {
	r . univ
}
