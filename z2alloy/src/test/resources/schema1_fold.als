open util/integer

sig A{}

sig B{
	a: (set  A),
}{(pred_B[a])}


pred pred_B[a: (set  A)] {}
