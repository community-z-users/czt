sig SYM{
}{pred_SYM[]}
pred pred_SYM(){}
some_SYM : run { some SYM }

sig VAL{
}{pred_VAL[]}
pred pred_VAL(){}
some_VAL : run { some VAL }

sig DeltaST{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
}{pred_DeltaST[st, st']}
pred pred_DeltaST[st : SYM ->lone VAL, st' : SYM ->lone VAL]{}
some_DeltaST : run { some DeltaST }

sig XiST{
        st: SYM ->lone VAL,
        st': SYM ->lone VAL,
}{pred_XiST[st, st']}
pred pred_XiST[st : SYM ->lone VAL, st' : SYM ->lone VAL]{
        pred_DeltaST[st, st'] and st = st'
}
some_XiST : run { some XiST }

sig LookUp{
        st: SYM ->lone VAL,
        st': SYM ->lone VAL,
        s_in: one  SYM,
        v_out: one  VAL,
}{pred_LookUp[st, st', s_in, v_out]}
pred pred_LookUp[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : one  SYM, v_out : one  VAL]{
        pred_XiST[st, st']
		s_in in dom[st]
		v_out = s_in.st
}
some_LookUp : run { some LookUp }

sig Add{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: one  SYM,
        v_in: one  VAL,
}{pred_Add[st, st', s_in, v_in]}
pred pred_Add(st : (SYM ->lone VAL), st' : (SYM ->lone VAL), s_in : one  SYM, v_in : one  VAL){
        (pred_DeltaST[st, st'] and ! (s_in in dom[st]) and (st' = (st + (s_in -> v_in))))
}
some_Add : run { some Add }

sig Replace{
        st: SYM ->lone VAL,
        st': SYM ->lone VAL,
        s_in: SYM,
        v_in: VAL,
}{pred_Replace[st, st', s_in, v_in]}
pred pred_Replace[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : SYM, v_in : VAL]{
	pred_DeltaST[st, st']
	s_in in dom[st]
	st' = st ++ s_in -> v_in
}
some_Replace : run { some Replace }

sig Delete{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: SYM,
}{pred_Delete[st, st', s_in]}
pred pred_Delete[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : SYM]{
    pred_DeltaST[st, st']
	s_in in dom[st]
	st' = ndres[s_in, st]
}
some_Delete : run { some Delete }

abstract sig Report{
}{pred_Report[]}
pred pred_Report(){}
some_Report : run { some Report }

one sig OK extends Report{
}{pred_OK[]}
pred pred_OK(){}
some_OK : run { some OK }

one sig Symbol_not_present extends Report{
}{pred_Symbol_not_present[]}
pred pred_Symbol_not_present(){}
some_Symbol_not_present : run { some Symbol_not_present }

one sig Symbol_present extends Report{
}{pred_Symbol_present[]}
pred pred_Symbol_present(){}
some_Symbol_present : run { some Symbol_present }

one sig Not_within_any_block extends Report{
}{pred_Not_within_any_block[]}
pred pred_Not_within_any_block(){}
some_Not_within_any_block : run { some Not_within_any_block }

one sig Symbol_not_found extends Report{
}{pred_Symbol_not_found[]}
pred pred_Symbol_not_found(){}
some_Symbol_not_found : run { some Symbol_not_found }

sig NotPresent{
        st: SYM ->lone VAL,
        st': SYM ->lone VAL,
        s_in: SYM,
        rep_out: Report,
}{pred_NotPresent[st, st', s_in, rep_out]}
pred pred_NotPresent[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : SYM, rep_out : Report]{
	pred_XiST[st, st']
	! s_in in dom[st]
	rep_out = Symbol_not_present
}
some_NotPresent : run { some NotPresent }

sig Present{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: SYM,
        rep_out: Report,
}{pred_Present[st, st', s_in, rep_out]}
pred pred_Present[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : SYM, rep_out : Report]{
	pred_XiST[st, st']
	s_in in dom[st]
	rep_out = Symbol_present
}
some_Present : run { some Present }

sig Success{
        rep_out: Report,
}{pred_Success[rep_out]}
pred pred_Success[rep_out : Report]{
        rep_out = OK
}
some_Success : run { some Success }

sig STLookUp{
        st: SYM ->lone VAL,
        st': SYM ->lone VAL,
        s_in: SYM,
        rep_out: Report,
        v_out: VAL,
}{pred_STLookUp[st, st', s_in, rep_out, v_out]}
pred pred_STLookUp[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : SYM, rep_out : Report, v_out : VAL]{
	(pred_LookUp[st, st', s_in, v_out] and pred_Success[rep_out]) or pred_NotPresent[st, st', s_in, rep_out]
}
some_STLookUp : run { some STLookUp }

sig STAdd{
        st: SYM ->lone VAL,
        st': SYM ->lone VAL,
        s_in: SYM,
        rep_out: Report,
        v_in: VAL,
}{pred_STAdd[st, st', s_in, rep_out, v_in]}
pred pred_STAdd[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : SYM, rep_out : Report, v_in : VAL]{
        (pred_Add[st, st', s_in, v_in] and pred_Success[rep_out]) or pred_Present[st, st', s_in, rep_out]
}
some_STAdd : run { some STAdd }

sig STReplace{
        st: SYM ->lone VAL,
        st': SYM ->lone VAL,
        s_in: SYM,
        v_in: VAL,
        rep_out: Report,
}{pred_STReplace[st, st', s_in, v_in, rep_out]}
pred pred_STReplace[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : SYM, v_in : VAL, rep_out : Report]{
        (pred_Replace[st, st', s_in, v_in] and pred_Success[rep_out]) or pred_NotPresent[st, st', s_in, rep_out]
}
some_STReplace : run { some STReplace }

sig STDelete{
        st: SYM ->lone VAL,
        st': SYM ->lone VAL,
        s_in: SYM,
        rep_out: Report,
}{pred_STDelete[st, st', s_in, rep_out]}
pred pred_STDelete[st : SYM ->lone VAL, st' : SYM ->lone VAL, s_in : SYM, rep_out : Report]{
        (pred_Delete[st, st', s_in] and pred_Success[rep_out]) or pred_NotPresent[st, st', s_in, rep_out]
}
some_STDelete : run { some STDelete }

fun dom[r : univ -> univ]: set  univ{
        r . univ
}

fun ndres[ex : set  univ, r : univ -> univ]: univ -> univ{
        (dom[r] - ex) <: r
}
