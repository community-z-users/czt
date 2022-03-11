sig SYM{}

sig VAL{}

sig ST{
	st: (SYM ->lone VAL),
}{(pred_ST[st])}


pred pred_ST[st: (SYM ->lone VAL)] {}

sig XiST{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
}{(pred_XiST[st, st'])}


pred pred_XiST[st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {
	(st = st')
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

sig DeltaST{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
}{(pred_DeltaST[st, st'])}


pred pred_DeltaST[st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {}

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

fun distro[s: (seq ST)] : (set  (SYM -> VAL)) {
	{val: VAL | some index: {i: Int | (i >= 0)} | (((sym -> val) in ((index . s) . st)) && all i: {i: Int | (i >= 0)}, sym: SYM, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST | ((i > index) => ((! (sym in (dom[((i . s) . st)]))) || ((sym -> val) in ((i . s) . st)))))}
}

sig BST{
	bst: (seq ST),
}{(pred_BST[bst])}


pred pred_BST[bst: (seq ST)] {}

sig XiBST{
	bst: (seq ST),
	bst': (seq ST),
}{(pred_XiBST[bst, bst'])}


pred pred_XiBST[bst: (seq ST), bst': (seq ST)] {
	(bst = bst')
}

sig BSearch0{
	bst: (seq ST),
	bst': (seq ST),
	s_in: SYM,
	v_out: VAL,
}{(pred_BSearch0[bst, bst', s_in, v_out])}


pred pred_BSearch0[bst: (seq ST), bst': (seq ST), s_in: SYM, v_out: VAL] {
	((pred_XiBST[bst, bst']) && ((s_in in (dom[(distro[bst])])) && (v_out = (s_in . (distro[bst])))))
}

sig DeltaBST{
	bst: (seq ST),
	bst': (seq ST),
}{(pred_DeltaBST[bst, bst'])}


pred pred_DeltaBST[bst: (seq ST), bst': (seq ST)] {}

sig BEnd0{
	bst: (seq ST),
	bst': (seq ST),
}{(pred_BEnd0[bst, bst'])}


pred pred_BEnd0[bst: (seq ST), bst': (seq ST)] {
	((pred_DeltaBST[bst, bst']) && ((! (bst = (none -> none))) && (bst' = (front[bst]))))
}

sig BReplace00{
	bst: (seq ST),
	bst': (seq ST),
	s_in: SYM,
	v_in: VAL,
	rep_out: Report,
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
}{(pred_BReplace00[bst, bst', s_in, v_in, rep_out, st, st'])}


pred pred_BReplace00[bst: (seq ST), bst': (seq ST), s_in: SYM, v_in: VAL, rep_out: Report, st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {
	(((pred_DeltaBST[bst, bst']) && (pred_DeltaST[st, st'])) && (((((! (bst = (none -> none))) && ((front[bst']) = (front[bst]))) && (st = ((last[bst]) . st))) && (st' = ((last[bst']) . st))) && ((((s_in in (dom[st])) && (st' = (st ++ (s_in -> v_in)))) && (rep_out = OK)) || (((! (s_in in (dom[st]))) && (st' = st)) && (rep_out = Symbol_not_present)))))
}

sig PhiBST{
	bst: (seq ST),
	bst': (seq ST),
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
}{(pred_PhiBST[bst, bst', st, st'])}


pred pred_PhiBST[bst: (seq ST), bst': (seq ST), st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {
	(((pred_DeltaBST[bst, bst']) && (pred_DeltaST[st, st'])) && ((((! (bst = (none -> none))) && ((front[bst]) = (front[bst']))) && (st = ((last[bst]) . st))) && (st' = ((last[bst']) . st))))
}

sig BLookUp0{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
	v_out: VAL,
	bst: (seq ST),
	bst': (seq ST),
}{(pred_BLookUp0[st, st', s_in, rep_out, v_out, bst, bst'])}


pred pred_BLookUp0[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report, v_out: VAL, bst: (seq ST), bst': (seq ST)] {
	((pred_STLookUp[st, st', s_in, rep_out, v_out]) && (pred_PhiBST[bst, bst', st, st']))
}

sig BAdd0{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
	v_in: VAL,
	bst: (seq ST),
	bst': (seq ST),
}{(pred_BAdd0[st, st', s_in, rep_out, v_in, bst, bst'])}


pred pred_BAdd0[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report, v_in: VAL, bst: (seq ST), bst': (seq ST)] {
	((pred_STAdd[st, st', s_in, rep_out, v_in]) && (pred_PhiBST[bst, bst', st, st']))
}

sig BReplace0{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
	v_in: VAL,
	bst: (seq ST),
	bst': (seq ST),
}{(pred_BReplace0[st, st', s_in, rep_out, v_in, bst, bst'])}


pred pred_BReplace0[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report, v_in: VAL, bst: (seq ST), bst': (seq ST)] {
	((pred_STReplace[st, st', s_in, rep_out, v_in]) && (pred_PhiBST[bst, bst', st, st']))
}

sig BDelete0{
	st: (SYM ->lone VAL),
	st': (SYM ->lone VAL),
	s_in: SYM,
	rep_out: Report,
	bst: (seq ST),
	bst': (seq ST),
}{(pred_BDelete0[st, st', s_in, rep_out, bst, bst'])}


pred pred_BDelete0[st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: SYM, rep_out: Report, bst: (seq ST), bst': (seq ST)] {
	((pred_STDelete[st, st', s_in, rep_out]) && (pred_PhiBST[bst, bst', st, st']))
}

sig BLookUp1{
	v_out: VAL,
	bst': (seq ST),
	rep_out: Report,
	bst: (seq ST),
	s_in: SYM,
}{(pred_BLookUp1[v_out, bst', rep_out, bst, s_in])}


pred pred_BLookUp1[v_out: VAL, bst': (seq ST), rep_out: Report, bst: (seq ST), s_in: SYM] {
	some i: {i: Int | (i >= 0)}, sym: SYM, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST | (pred_BLookUp0[(deltast_temp . (SYM ->lone VAL)), (deltast_temp . (SYM ->lone VAL)), s_in, rep_out, v_out, bst, bst'])
}

sig BAdd1{
	bst': (seq ST),
	rep_out: Report,
	bst: (seq ST),
	s_in: SYM,
	v_in: VAL,
}{(pred_BAdd1[bst', rep_out, bst, s_in, v_in])}


pred pred_BAdd1[bst': (seq ST), rep_out: Report, bst: (seq ST), s_in: SYM, v_in: VAL] {
	some i: {i: Int | (i >= 0)}, sym: SYM, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST | (pred_BAdd0[(deltast_temp . (SYM ->lone VAL)), (deltast_temp . (SYM ->lone VAL)), s_in, rep_out, v_in, bst, bst'])
}

sig BReplace1{
	bst': (seq ST),
	rep_out: Report,
	bst: (seq ST),
	s_in: SYM,
	v_in: VAL,
}{(pred_BReplace1[bst', rep_out, bst, s_in, v_in])}


pred pred_BReplace1[bst': (seq ST), rep_out: Report, bst: (seq ST), s_in: SYM, v_in: VAL] {
	some i: {i: Int | (i >= 0)}, sym: SYM, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST | (pred_BReplace0[(deltast_temp . (SYM ->lone VAL)), (deltast_temp . (SYM ->lone VAL)), s_in, rep_out, v_in, bst, bst'])
}

sig BDelete1{
	bst': (seq ST),
	rep_out: Report,
	bst: (seq ST),
	s_in: SYM,
}{(pred_BDelete1[bst', rep_out, bst, s_in])}


pred pred_BDelete1[bst': (seq ST), rep_out: Report, bst: (seq ST), s_in: SYM] {
	some i: {i: Int | (i >= 0)}, sym: SYM, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST, deltast_temp: DeltaST | (pred_BDelete0[(deltast_temp . (SYM ->lone VAL)), (deltast_temp . (SYM ->lone VAL)), s_in, rep_out, bst, bst'])
}

sig Empty{
	bst: (seq ST),
	bst': (seq ST),
	rep_out: Report,
}{(pred_Empty[bst, bst', rep_out])}


pred pred_Empty[bst: (seq ST), bst': (seq ST), rep_out: Report] {
	((pred_XiBST[bst, bst']) && ((bst = (none -> none)) && (rep_out = Not_within_any_block)))
}

sig NotFound{
	bst: (seq ST),
	bst': (seq ST),
	s_in: SYM,
	rep_out: Report,
}{(pred_NotFound[bst, bst', s_in, rep_out])}


pred pred_NotFound[bst: (seq ST), bst': (seq ST), s_in: SYM, rep_out: Report] {
	((pred_XiBST[bst, bst']) && (((! (bst = (none -> none))) && (! (s_in in (dom[(distro[bst])])))) && (rep_out = Symbol_not_found)))
}

sig BSearch{
	bst: (seq ST),
	bst': (seq ST),
	rep_out: Report,
	s_in: SYM,
	v_out: VAL,
}{(pred_BSearch[bst, bst', rep_out, s_in, v_out])}


pred pred_BSearch[bst: (seq ST), bst': (seq ST), rep_out: Report, s_in: SYM, v_out: VAL] {
	((((pred_BSearch0[bst, bst', s_in, v_out]) && (pred_Success[rep_out])) || (pred_NotFound[bst, bst', s_in, rep_out])) || (pred_Empty[bst, bst', rep_out]))
}

sig BEnd{
	bst: (seq ST),
	bst': (seq ST),
	rep_out: Report,
}{(pred_BEnd[bst, bst', rep_out])}


pred pred_BEnd[bst: (seq ST), bst': (seq ST), rep_out: Report] {
	(((pred_BEnd0[bst, bst']) && (pred_Success[rep_out])) || (pred_Empty[bst, bst', rep_out]))
}

sig BLookUp{
	v_out: VAL,
	bst': (seq ST),
	rep_out: Report,
	bst: (seq ST),
	s_in: SYM,
}{(pred_BLookUp[v_out, bst', rep_out, bst, s_in])}


pred pred_BLookUp[v_out: VAL, bst': (seq ST), rep_out: Report, bst: (seq ST), s_in: SYM] {
	((pred_BLookUp1[v_out, bst', rep_out, bst, s_in]) || (pred_Empty[bst, bst', rep_out]))
}

sig BAdd{
	bst': (seq ST),
	rep_out: Report,
	bst: (seq ST),
	s_in: SYM,
	v_in: VAL,
}{(pred_BAdd[bst', rep_out, bst, s_in, v_in])}


pred pred_BAdd[bst': (seq ST), rep_out: Report, bst: (seq ST), s_in: SYM, v_in: VAL] {
	((pred_BAdd1[bst', rep_out, bst, s_in, v_in]) || (pred_Empty[bst, bst', rep_out]))
}

sig BReplace{
	bst': (seq ST),
	rep_out: Report,
	bst: (seq ST),
	s_in: SYM,
	v_in: VAL,
}{(pred_BReplace[bst', rep_out, bst, s_in, v_in])}


pred pred_BReplace[bst': (seq ST), rep_out: Report, bst: (seq ST), s_in: SYM, v_in: VAL] {
	((pred_BReplace1[bst', rep_out, bst, s_in, v_in]) || (pred_Empty[bst, bst', rep_out]))
}

sig BDelete{
	bst': (seq ST),
	rep_out: Report,
	bst: (seq ST),
	s_in: SYM,
}{(pred_BDelete[bst', rep_out, bst, s_in])}


pred pred_BDelete[bst': (seq ST), rep_out: Report, bst: (seq ST), s_in: SYM] {
	((pred_BDelete1[bst', rep_out, bst, s_in]) || (pred_Empty[bst, bst', rep_out]))
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


