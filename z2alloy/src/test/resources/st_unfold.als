 sig SYM{
}{pred_SYM[]}
pred pred_SYM[ ] {}
some_SYM : run { some SYM }

sig VAL{
}{pred_VAL[]}
pred pred_VAL[ ] {}
some_VAL : run { some VAL }

sig DeltaST{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
}{pred_DeltaST[st, st']}
pred pred_DeltaST[ st: set  (SYM -> VAL), st': set  (SYM -> VAL)] {
((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)))
}
some_DeltaST : run { some DeltaST }

sig XiST{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
}{pred_XiST[st, st']}
pred pred_XiST[ st: set  (SYM -> VAL), st': set  (SYM -> VAL)] {
((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st'))
}
some_XiST : run { some XiST }

sig LookUp{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        v_out: one  VAL,
}{pred_LookUp[st, st', s_in, v_out]}
pred pred_LookUp[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, v_out: one  VAL] {
((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st') and (s_in in dom[st]) and (v_out = (s_in . st)))
}
some_LookUp : run { some LookUp }

sig Add{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        v_in: one  VAL,
}{pred_Add[st, st', s_in, v_in]}
pred pred_Add[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, v_in: one  VAL] {
((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and ! (s_in in dom[st]) and (st' = (st + (s_in -> v_in))))
}
some_Add : run { some Add }

sig Replace{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        v_in: one  VAL,
}{pred_Replace[st, st', s_in, v_in]}
pred pred_Replace[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, v_in: one  VAL] {
((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (s_in in dom[st]) and (st' = (st ++ (s_in -> v_in))))
}
some_Replace : run { some Replace }

sig Delete{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
}{pred_Delete[st, st', s_in]}
pred pred_Delete[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM] {
((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (s_in in dom[st]) and (st' = ndres[s_in, st]))
}
some_Delete : run { some Delete }

abstract sig Report{
}{pred_Report[]}
pred pred_Report[ ] {}
some_Report : run { some Report }

one sig OK extends Report{
}{pred_OK[]}
pred pred_OK[ ] {}
some_OK : run { some OK }

one sig Symbol_not_present extends Report{
}{pred_Symbol_not_present[]}
pred pred_Symbol_not_present[ ] {}
some_Symbol_not_present : run { some Symbol_not_present }

one sig Symbol_present extends Report{
}{pred_Symbol_present[]}
pred pred_Symbol_present[ ] {}
some_Symbol_present : run { some Symbol_present }

one sig Not_within_any_block extends Report{
}{pred_Not_within_any_block[]}
pred pred_Not_within_any_block[ ] {}
some_Not_within_any_block : run { some Not_within_any_block }

one sig Symbol_not_found extends Report{
}{pred_Symbol_not_found[]}
pred pred_Symbol_not_found[ ] {}
some_Symbol_not_found : run { some Symbol_not_found }

sig NotPresent{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        rep_out: one  Report,
}{pred_NotPresent[st, st', s_in, rep_out]}
pred pred_NotPresent[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, rep_out: one  Report] {
((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st') and ! (s_in in dom[st]) and (rep_out = Symbol_not_present))
}
some_NotPresent : run { some NotPresent }

sig Present{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        rep_out: one  Report,
}{pred_Present[st, st', s_in, rep_out]}
pred pred_Present[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, rep_out: one  Report] {
((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st') and (s_in in dom[st]) and (rep_out = Symbol_present))
}
some_Present : run { some Present }

sig Success{
        rep_out: one  Report,
}{pred_Success[rep_out]}
pred pred_Success[ rep_out: one  Report] {
(rep_out = OK)
}
some_Success : run { some Success }

sig STLookUp{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        v_out: one  VAL,
        rep_out: one  Report,
}{pred_STLookUp[st, st', s_in, v_out, rep_out]}
pred pred_STLookUp[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, v_out: one  VAL, rep_out: one  Report] {
(((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st') and (s_in in dom[st]) and (v_out = (s_in . st)) and (rep_out = OK)) or ((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st') and ! (s_in in dom[st]) and (rep_out = Symbol_not_present)))
}
some_STLookUp : run { some STLookUp }

sig STAdd{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        v_in: one  VAL,
        rep_out: one  Report,
}{pred_STAdd[st, st', s_in, v_in, rep_out]}
pred pred_STAdd[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, v_in: one  VAL, rep_out: one  Report] {
(((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and ! (s_in in dom[st]) and (st' = (st + (s_in -> v_in))) and (rep_out = OK)) or ((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st') and (s_in in dom[st]) and (rep_out = Symbol_present)))
}
some_STAdd : run { some STAdd }

sig STReplace{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        v_in: one  VAL,
        rep_out: one  Report,
}{pred_STReplace[st, st', s_in, v_in, rep_out]}
pred pred_STReplace[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, v_in: one  VAL, rep_out: one  Report] {
(((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (s_in in dom[st]) and (st' = (st ++ (s_in -> v_in))) and (rep_out = OK)) or ((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st') and ! (s_in in dom[st]) and (rep_out = Symbol_not_present)))
}
some_STReplace : run { some STReplace }

sig STDelete{
        st: set  (SYM -> VAL),
        st': set  (SYM -> VAL),
        s_in: one  SYM,
        rep_out: one  Report,
}{pred_STDelete[st, st', s_in, rep_out]}
pred pred_STDelete[ st: set  (SYM -> VAL), st': set  (SYM -> VAL), s_in: one  SYM, rep_out: one  Report] {
(((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (s_in in dom[st]) and (st' = ndres[s_in, st]) and (rep_out = OK)) or ((st in (SYM ->lone VAL)) and (st' in (SYM ->lone VAL)) and (st = st') and ! (s_in in dom[st]) and (rep_out = Symbol_not_present)))
}
some_STDelete : run { some STDelete }

fun dom[ r: (univ -> univ)] : set  univ {
(r . univ)
}

fun ndres[ ex: set  univ, r: (univ -> univ)] : (univ -> univ) {
((dom[r] - ex) <: r)
}
