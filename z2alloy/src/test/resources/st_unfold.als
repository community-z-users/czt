sig SYM{}

sig VAL{}

sig DeltaST{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
}{(pred_DeltaST[st, st'])}


pred pred_DeltaST[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL))] {
	((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL)))
}

sig XiST{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
}{(pred_XiST[st, st'])}


pred pred_XiST[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL))] {
	(((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st'))
}

sig LookUp{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	v_out: VAL,
}{(pred_LookUp[st, st', s_in, v_out])}


pred pred_LookUp[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, v_out: VAL] {
	((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st')) && ((s_in in (dom[st])) && (v_out = (s_in . st))))
}

sig Add{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	v_in: VAL,
}{(pred_Add[st, st', s_in, v_in])}


pred pred_Add[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, v_in: VAL] {
	(((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && ((! (s_in in (dom[st]))) && (st' = (st + (s_in -> v_in)))))
}

sig Replace{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	v_in: VAL,
}{(pred_Replace[st, st', s_in, v_in])}


pred pred_Replace[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, v_in: VAL] {
	(((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && ((s_in in (dom[st])) && (st' = (st ++ (s_in -> v_in)))))
}

sig Delete{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
}{(pred_Delete[st, st', s_in])}


pred pred_Delete[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM] {
	(((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && ((s_in in (dom[st])) && (st' = (ndres[s_in, st]))))
}

enum Report{OK, Symbol_not_present, Symbol_present, Not_within_any_block, Symbol_not_found}

sig NotPresent{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	rep_out: Report,
}{(pred_NotPresent[st, st', s_in, rep_out])}


pred pred_NotPresent[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, rep_out: Report] {
	((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st')) && ((! (s_in in (dom[st]))) && (rep_out = Symbol_not_present)))
}

sig Present{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	rep_out: Report,
}{(pred_Present[st, st', s_in, rep_out])}


pred pred_Present[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, rep_out: Report] {
	((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st')) && ((s_in in (dom[st])) && (rep_out = Symbol_present)))
}

sig Success{
	rep_out: Report,
}{(pred_Success[rep_out])}


pred pred_Success[rep_out: Report] {
	(rep_out = OK)
}

sig STLookUp{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	v_out: VAL,
	rep_out: Report,
}{(pred_STLookUp[st, st', s_in, v_out, rep_out])}


pred pred_STLookUp[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, v_out: VAL, rep_out: Report] {
	((((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st')) && ((s_in in (dom[st])) && (v_out = (s_in . st)))) && (rep_out = OK)) || ((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st')) && ((! (s_in in (dom[st]))) && (rep_out = Symbol_not_present))))
}

sig STAdd{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	v_in: VAL,
	rep_out: Report,
}{(pred_STAdd[st, st', s_in, v_in, rep_out])}


pred pred_STAdd[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, v_in: VAL, rep_out: Report] {
	(((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && ((! (s_in in (dom[st]))) && (st' = (st + (s_in -> v_in))))) && (rep_out = OK)) || ((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st')) && ((s_in in (dom[st])) && (rep_out = Symbol_present))))
}

sig STReplace{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	v_in: VAL,
	rep_out: Report,
}{(pred_STReplace[st, st', s_in, v_in, rep_out])}


pred pred_STReplace[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, v_in: VAL, rep_out: Report] {
	(((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && ((s_in in (dom[st])) && (st' = (st ++ (s_in -> v_in))))) && (rep_out = OK)) || ((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st')) && ((! (s_in in (dom[st]))) && (rep_out = Symbol_not_present))))
}

sig STDelete{
	st: (set  (SYM -> VAL)),
	st': (set  (SYM -> VAL)),
	s_in: SYM,
	rep_out: Report,
}{(pred_STDelete[st, st', s_in, rep_out])}


pred pred_STDelete[st: (set  (SYM -> VAL)), st': (set  (SYM -> VAL)), s_in: SYM, rep_out: Report] {
	(((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && ((s_in in (dom[st])) && (st' = (ndres[s_in, st])))) && (rep_out = OK)) || ((((st in (SYM ->lone VAL)) && (st' in (SYM ->lone VAL))) && (st = st')) && ((! (s_in in (dom[st]))) && (rep_out = Symbol_not_present))))
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


