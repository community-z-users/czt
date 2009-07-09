sig SYM{}

sig VAL{}

sig DeltaST{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
}{(pred_DeltaST[st, st'])}


pred pred_DeltaST[st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {}

sig XiST{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
}{(pred_XiST[st, st'])}


pred pred_XiST[st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {
	((pred_DeltaST[st, st']) && (st = st'))
}

sig LookUp{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	v_out: VAL,
}{(pred_LookUp[st, st', s_in, v_out])}


pred pred_LookUp[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, v_out: VAL] {
	((pred_XiST[st, st']) && ((s_in in (dom[st])) && (v_out = (s_in . st))))
}

sig Add{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	v_in: VAL,
}{(pred_Add[st, st', s_in, v_in])}


pred pred_Add[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, v_in: VAL] {
	((pred_DeltaST[st, st']) && ((! (s_in in (dom[st]))) && (st' = (st + (s_in -> v_in)))))
}

sig Replace{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	v_in: VAL,
}{(pred_Replace[st, st', s_in, v_in])}


pred pred_Replace[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, v_in: VAL] {
	((pred_DeltaST[st, st']) && ((s_in in (dom[st])) && (st' = (st ++ (s_in -> v_in)))))
}

sig Delete{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
}{(pred_Delete[st, st', s_in])}


pred pred_Delete[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM] {
	((pred_DeltaST[st, st']) && ((s_in in (dom[st])) && (st' = (ndres[s_in, st]))))
}

enum Report{OK, Symbol_not_present, Symbol_present, Not_within_any_block, Symbol_not_found}

sig NotPresent{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
}{(pred_NotPresent[st, st', s_in, rep_out])}


pred pred_NotPresent[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report] {
	((pred_XiST[st, st']) && ((! (s_in in (dom[st]))) && (rep_out = Symbol_not_present)))
}

sig Present{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
}{(pred_Present[st, st', s_in, rep_out])}


pred pred_Present[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report] {
	((pred_XiST[st, st']) && ((s_in in (dom[st])) && (rep_out = Symbol_present)))
}

sig Success{
	rep_out: Report,
}{(pred_Success[rep_out])}


pred pred_Success[rep_out: Report] {
	(rep_out = OK)
}

sig STLookUp{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
	v_out: VAL,
}{(pred_STLookUp[st, st', s_in, rep_out, v_out])}


pred pred_STLookUp[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report, v_out: VAL] {
	(((pred_LookUp[st, st', s_in, v_out]) && (pred_Success[rep_out])) || (pred_NotPresent[st, st', s_in, rep_out]))
}

sig STAdd{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
	v_in: VAL,
}{(pred_STAdd[st, st', s_in, rep_out, v_in])}


pred pred_STAdd[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report, v_in: VAL] {
	(((pred_Add[st, st', s_in, v_in]) && (pred_Success[rep_out])) || (pred_Present[st, st', s_in, rep_out]))
}

sig STReplace{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
	v_in: VAL,
}{(pred_STReplace[st, st', s_in, rep_out, v_in])}


pred pred_STReplace[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report, v_in: VAL] {
	(((pred_Replace[st, st', s_in, v_in]) && (pred_Success[rep_out])) || (pred_NotPresent[st, st', s_in, rep_out]))
}

sig STDelete{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
}{(pred_STDelete[st, st', s_in, rep_out])}


pred pred_STDelete[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report] {
	(((pred_Delete[st, st', s_in]) && (pred_Success[rep_out])) || (pred_NotPresent[st, st', s_in, rep_out]))
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


