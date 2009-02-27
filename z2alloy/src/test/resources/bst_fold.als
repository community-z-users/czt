sig SYM{
}{(pred_SYM[])}
pred pred_SYM[ ] {}
some_SYM : run { some SYM }

sig VAL{
}{(pred_VAL[])}
pred pred_VAL[ ] {}
some_VAL : run { some VAL }

sig ST{
        st: (SYM ->lone VAL),
}{(pred_ST[st])}
pred pred_ST[ st: (SYM ->lone VAL)] {}
some_ST : run { some ST }

sig XiST{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
}{(pred_XiST[st, st'])}
pred pred_XiST[ st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {
(st = st')
}
some_XiST : run { some XiST }

sig LookUp{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        v_out: (one  VAL),
}{(pred_LookUp[st, st', s_in, v_out])}
pred pred_LookUp[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), v_out: (one  VAL)] {
((pred_XiST[st, st']) and (s_in in (dom[st])) and (v_out = (s_in . st)))
}
some_LookUp : run { some LookUp }

sig DeltaST{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
}{(pred_DeltaST[st, st'])}
pred pred_DeltaST[ st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {}
some_DeltaST : run { some DeltaST }

sig Add{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        v_in: (one  VAL),
}{(pred_Add[st, st', s_in, v_in])}
pred pred_Add[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), v_in: (one  VAL)] {
((pred_DeltaST[st, st']) and (! (s_in in (dom[st]))) and (st' = (st + (s_in -> v_in))))
}
some_Add : run { some Add }

sig Replace{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        v_in: (one  VAL),
}{(pred_Replace[st, st', s_in, v_in])}
pred pred_Replace[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), v_in: (one  VAL)] {
((pred_DeltaST[st, st']) and (s_in in (dom[st])) and (st' = (st ++ (s_in -> v_in))))
}
some_Replace : run { some Replace }

sig Delete{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
}{(pred_Delete[st, st', s_in])}
pred pred_Delete[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM)] {
((pred_DeltaST[st, st']) and (s_in in (dom[st])) and (st' = (ndres[s_in, st])))
}
some_Delete : run { some Delete }

abstract sig Report{
}{(pred_Report[])}
pred pred_Report[ ] {}
some_Report : run { some Report }

one sig OK extends Report{
}{(pred_OK[])}
pred pred_OK[ ] {}
some_OK : run { some OK }

one sig Symbol_not_present extends Report{
}{(pred_Symbol_not_present[])}
pred pred_Symbol_not_present[ ] {}
some_Symbol_not_present : run { some Symbol_not_present }

one sig Symbol_present extends Report{
}{(pred_Symbol_present[])}
pred pred_Symbol_present[ ] {}
some_Symbol_present : run { some Symbol_present }

one sig Not_within_any_block extends Report{
}{(pred_Not_within_any_block[])}
pred pred_Not_within_any_block[ ] {}
some_Not_within_any_block : run { some Not_within_any_block }

one sig Symbol_not_found extends Report{
}{(pred_Symbol_not_found[])}
pred pred_Symbol_not_found[ ] {}
some_Symbol_not_found : run { some Symbol_not_found }

sig NotPresent{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        rep_out: (one  Report),
}{(pred_NotPresent[st, st', s_in, rep_out])}
pred pred_NotPresent[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), rep_out: (one  Report)] {
((pred_XiST[st, st']) and (! (s_in in (dom[st]))) and (rep_out = Symbol_not_present))
}
some_NotPresent : run { some NotPresent }

sig Present{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        rep_out: (one  Report),
}{(pred_Present[st, st', s_in, rep_out])}
pred pred_Present[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), rep_out: (one  Report)] {
((pred_XiST[st, st']) and (s_in in (dom[st])) and (rep_out = Symbol_present))
}
some_Present : run { some Present }

sig Success{
        rep_out: (one  Report),
}{(pred_Success[rep_out])}
pred pred_Success[ rep_out: (one  Report)] {
(rep_out = OK)
}
some_Success : run { some Success }

sig STLookUp{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        rep_out: (one  Report),
        v_out: (one  VAL),
}{(pred_STLookUp[st, st', s_in, rep_out, v_out])}
pred pred_STLookUp[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), rep_out: (one  Report), v_out: (one  VAL)] {
(((pred_LookUp[st, st', s_in, v_out]) and (pred_Success[rep_out])) or (pred_NotPresent[st, st', s_in, rep_out]))
}
some_STLookUp : run { some STLookUp }

sig STAdd{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        rep_out: (one  Report),
		v_in : (one VAL),
       }{(pred_STAdd[st, st', s_in, rep_out, v_in])}
pred pred_STAdd[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), rep_out: (one  Report), v_in: (one  VAL)] {
(((pred_Add[st, st', s_in, v_in]) and (pred_Success[rep_out])) or (pred_Present[st, st', s_in, rep_out]))
}
some_STAdd : run { some STAdd }

sig STReplace{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        v_in: (one  VAL),
        rep_out: (one  Report),
}{(pred_STReplace[st, st', s_in, v_in, rep_out])}
pred pred_STReplace[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), v_in: (one  VAL), rep_out: (one  Report)] {
(((pred_Replace[st, st', s_in, v_in]) and (pred_Success[rep_out])) or (pred_NotPresent[st, st', s_in, rep_out]))
}
some_STReplace : run { some STReplace }

sig STDelete{
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        rep_out: (one  Report),
}{(pred_STDelete[st, st', s_in, rep_out])}
pred pred_STDelete[ st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), rep_out: (one  Report)] {
(((pred_Delete[st, st', s_in]) and (pred_Success[rep_out])) or (pred_NotPresent[st, st', s_in, rep_out]))
}
some_STDelete : run { some STDelete }

sig BST{
        bst: (seq ST),
}{(pred_BST[bst])}
pred pred_BST[ bst: (seq ST)] {}
some_BST : run { some BST }

sig XiBST{
        bst: (seq ST),
        bst': (seq ST),
}{(pred_XiBST[bst, bst'])}
pred pred_XiBST[ bst: (seq ST), bst': (seq ST)] {
(bst = bst')
}
some_XiBST : run { some XiBST }

sig BSearch0{
        bst: (seq ST),
        bst': (seq ST),
        s_in: (one  SYM),
        v_out: (one  VAL),
}{(pred_BSearch0[bst, bst', s_in, v_out])}
pred pred_BSearch0[ bst: (seq ST), bst': (seq ST), s_in: (one  SYM), v_out: (one  VAL)] {
((pred_XiBST[bst, bst']) and (s_in in (dom[(DistroSlash[bst])])) and (v_out = (s_in . (DistroSlash[bst]))))
}
some_BSearch0 : run { some BSearch0 }

sig DeltaBST{
        bst: (seq ST),
        bst': (seq ST),
}{(pred_DeltaBST[bst, bst'])}
pred pred_DeltaBST[ bst: (seq ST), bst': (seq ST)] {}
some_DeltaBST : run { some DeltaBST }

sig BEnd0{
        bst: (seq ST),
        bst': (seq ST),
}{(pred_BEnd0[bst, bst'])}
pred pred_BEnd0[ bst: (seq ST), bst': (seq ST)] {
((pred_DeltaBST[bst, bst']) and (! (bst = (none -> none))) and (bst' = (seq/butlast[bst])))
}
some_BEnd0 : run { some BEnd0 }

sig BReplace00{
        bst: (seq ST),
        bst': (seq ST),
        s_in: (one  SYM),
        v_in: (one  VAL),
        rep_out: (one  Report),
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
}{(pred_BReplace00[bst, bst', s_in, v_in, rep_out, st, st'])}
pred pred_BReplace00[ bst: (seq ST), bst': (seq ST), s_in: (one  SYM), v_in: (one  VAL), rep_out: (one  Report), st: (SYM ->lone VAL), st': (SYM ->lone VAL
)] {
((pred_DeltaBST[bst, bst']) and (pred_DeltaST[st, st']) and (! (bst = (none -> none))) and ((seq/butlast[bst']) = (seq/butlast[bst])) and (st = ((seq/last[
bst]) . @st)) and (st' = ((seq/last[bst']) . @st)) and (((s_in in (dom[st])) and (st' = (st ++ (s_in -> v_in))) and (rep_out = OK)) or ((! (s_in in (dom[st
]))) and (st' = st) and (rep_out = Symbol_not_present))))
}
some_BReplace00 : run { some BReplace00 }

sig PhiBST{
        bst: (seq ST),
        bst': (seq ST),
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
}{(pred_PhiBST[bst, bst', st, st'])}
pred pred_PhiBST[ bst: (seq ST), bst': (seq ST), st: (SYM ->lone VAL), st': (SYM ->lone VAL)] {
((pred_DeltaBST[bst, bst']) and (pred_DeltaST[st, st']) and (! (bst = (none -> none))) and ((seq/butlast[bst]) = (seq/butlast[bst'])) and (st = ((seq/last[
bst]) . @st)) and (st' = ((seq/last[bst']) . @st)))
}
some_PhiBST : run { some PhiBST }

sig BLookUp0{
        bst: (seq ST),
        bst': (seq ST),
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        rep_out: (one  Report),
        v_out: (one  VAL),
}{(pred_BLookUp0[bst, bst', st, st', s_in, rep_out, v_out])}
pred pred_BLookUp0[ bst: (seq ST), bst': (seq ST), st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), rep_out: (one  Report), v_out: (one  VAL)
] {
((pred_STLookUp[st, st', s_in, rep_out, v_out]) and (pred_PhiBST[bst, bst', st, st']))
}
some_BLookUp0 : run { some BLookUp0 }

sig BAdd0{
        bst: (seq ST),
        bst': (seq ST),
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        rep_out: (one  Report),
        v_in: (one  VAL),
}{(pred_BAdd0[bst, bst', st, st', s_in, rep_out, v_in])}
pred pred_BAdd0[ bst: (seq ST), bst': (seq ST), st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), rep_out: (one  Report), v_in: (one  VAL)] {
((pred_STAdd[st, st', s_in, rep_out, v_in]) and (pred_PhiBST[bst, bst', st, st']))
}
some_BAdd0 : run { some BAdd0 }

sig BReplace0{
        bst: (seq ST),
        bst': (seq ST),
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        v_in: (one  VAL),
        rep_out: (one  Report),
}{(pred_BReplace0[bst, bst', st, st', s_in, v_in, rep_out])}
pred pred_BReplace0[ bst: (seq ST), bst': (seq ST), st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), v_in: (one  VAL), rep_out: (one  Report)
] {
((pred_STReplace[st, st', s_in, v_in, rep_out]) and (pred_PhiBST[bst, bst', st, st']))
}
some_BReplace0 : run { some BReplace0 }

sig BDelete0{
        bst: (seq ST),
        bst': (seq ST),
        st: (SYM ->lone VAL),
        st': (SYM ->lone VAL),
        s_in: (one  SYM),
        rep_out: (one  Report),
}{(pred_BDelete0[bst, bst', st, st', s_in, rep_out])}
pred pred_BDelete0[ bst: (seq ST), bst': (seq ST), st: (SYM ->lone VAL), st': (SYM ->lone VAL), s_in: (one  SYM), rep_out: (one  Report)] {
((pred_STDelete[st, st', s_in, rep_out]) and (pred_PhiBST[bst, bst', st, st']))
}
some_BDelete0 : run { some BDelete0 }

sig BLookUp1{
        v_out: (one  VAL),
        bst': (seq ST),
        rep_out: (one  Report),
        s_in: (one  SYM),
        bst: (seq ST),
}{(pred_BLookUp1[v_out, bst', rep_out, s_in, bst])}
pred pred_BLookUp1[ v_out: (one  VAL), bst': (seq ST), rep_out: (one  Report), s_in: (one  SYM), bst: (seq ST)] {
some deltast_temp: DeltaST | (pred_BLookUp0[bst, bst', (deltast_temp . @st), (deltast_temp . @st'), s_in, rep_out, v_out])
}
some_BLookUp1 : run { some BLookUp1 }

sig BAdd1{
        bst': (seq ST),
        rep_out: (one  Report),
        s_in: (one  SYM),
        bst: (seq ST),
        v_in: (one  VAL),
}{(pred_BAdd1[bst', rep_out, s_in, bst, v_in])}
pred pred_BAdd1[ bst': (seq ST), rep_out: (one  Report), s_in: (one  SYM), bst: (seq ST), v_in: (one  VAL)] {
some deltast_temp: DeltaST | (pred_BAdd0[bst, bst', (deltast_temp . @st), (deltast_temp . @st'), s_in, rep_out, v_in])
}
some_BAdd1 : run { some BAdd1 }

sig BReplace1{
        bst': (seq ST),
        rep_out: (one  Report),
        s_in: (one  SYM),
        bst: (seq ST),
        v_in: (one  VAL),
}{(pred_BReplace1[bst', rep_out, s_in, bst, v_in])}
pred pred_BReplace1[ bst': (seq ST), rep_out: (one  Report), s_in: (one  SYM), bst: (seq ST), v_in: (one  VAL)] {
some deltast_temp: DeltaST | (pred_BReplace0[bst, bst', (deltast_temp . @st), (deltast_temp . @st'), s_in, v_in, rep_out])
}
some_BReplace1 : run { some BReplace1 }

sig BDelete1{
        bst': (seq ST),
        rep_out: (one  Report),
        s_in: (one  SYM),
        bst: (seq ST),
}{(pred_BDelete1[bst', rep_out, s_in, bst])}
pred pred_BDelete1[ bst': (seq ST), rep_out: (one  Report), s_in: (one  SYM), bst: (seq ST)] {
some deltast_temp: DeltaST | (pred_BDelete0[bst, bst', (deltast_temp . @st), (deltast_temp . @st'), s_in, rep_out])
}
some_BDelete1 : run { some BDelete1 }

sig Empty{
        bst: (seq ST),
        bst': (seq ST),
        rep_out: (one  Report),
}{(pred_Empty[bst, bst', rep_out])}
pred pred_Empty[ bst: (seq ST), bst': (seq ST), rep_out: (one  Report)] {
((pred_XiBST[bst, bst']) and (bst = (none -> none)) and (rep_out = Not_within_any_block))
}
some_Empty : run { some Empty }

sig NotFound{
        bst: (seq ST),
        bst': (seq ST),
        s_in: (one  SYM),
        rep_out: (one  Report),
}{(pred_NotFound[bst, bst', s_in, rep_out])}
pred pred_NotFound[ bst: (seq ST), bst': (seq ST), s_in: (one  SYM), rep_out: (one  Report)] {
((pred_XiBST[bst, bst']) and (! (bst = (none -> none))) and (! (s_in in (dom[(DistroSlash[bst])]))) and (rep_out = Symbol_not_found))
}
some_NotFound : run { some NotFound }

sig BSearch{
        bst: (seq ST),
        bst': (seq ST),
        rep_out: (one  Report),
        s_in: (one  SYM),
        v_out: (one  VAL),
}{(pred_BSearch[bst, bst', rep_out, s_in, v_out])}
pred pred_BSearch[ bst: (seq ST), bst': (seq ST), rep_out: (one  Report), s_in: (one  SYM), v_out: (one  VAL)] {
(((pred_BSearch0[bst, bst', s_in, v_out]) and (pred_Success[rep_out])) or (pred_NotFound[bst, bst', s_in, rep_out]) or (pred_Empty[bst, bst', rep_out]))
}
some_BSearch : run { some BSearch }

sig BEnd{
        bst: (seq ST),
        bst': (seq ST),
        rep_out: (one  Report),
}{(pred_BEnd[bst, bst', rep_out])}
pred pred_BEnd[ bst: (seq ST), bst': (seq ST), rep_out: (one  Report)] {
(((pred_BEnd0[bst, bst']) and (pred_Success[rep_out])) or (pred_Empty[bst, bst', rep_out]))
}
some_BEnd : run { some BEnd }

sig BLookUp{
        bst: (seq ST),
        bst': (seq ST),
        rep_out: (one  Report),
        v_out: (one  VAL),
        s_in: (one  SYM),
}{(pred_BLookUp[bst, bst', rep_out, v_out, s_in])}
pred pred_BLookUp[ bst: (seq ST), bst': (seq ST), rep_out: (one  Report), v_out: (one  VAL), s_in: (one  SYM)] {
((pred_BLookUp1[v_out, bst', rep_out, s_in, bst]) or (pred_Empty[bst, bst', rep_out]))
}
some_BLookUp : run { some BLookUp }

sig BAdd{
        bst: (seq ST),
        bst': (seq ST),
        rep_out: (one  Report),
        s_in: (one  SYM),
        v_in: (one  VAL),
}{(pred_BAdd[bst, bst', rep_out, s_in, v_in])}
pred pred_BAdd[ bst: (seq ST), bst': (seq ST), rep_out: (one  Report), s_in: (one  SYM), v_in: (one  VAL)] {
((pred_BAdd1[bst', rep_out, s_in, bst, v_in]) or (pred_Empty[bst, bst', rep_out]))
}
some_BAdd : run { some BAdd }

sig BReplace{
        bst: (seq ST),
        bst': (seq ST),
        rep_out: (one  Report),
        s_in: (one  SYM),
        v_in: (one  VAL),
}{(pred_BReplace[bst, bst', rep_out, s_in, v_in])}
pred pred_BReplace[ bst: (seq ST), bst': (seq ST), rep_out: (one  Report), s_in: (one  SYM), v_in: (one  VAL)] {
((pred_BReplace1[bst', rep_out, s_in, bst, v_in]) or (pred_Empty[bst, bst', rep_out]))
}
some_BReplace : run { some BReplace }

sig BDelete{
        bst: (seq ST),
        bst': (seq ST),
        rep_out: (one  Report),
        s_in: (one  SYM),
}{(pred_BDelete[bst, bst', rep_out, s_in])}
pred pred_BDelete[ bst: (seq ST), bst': (seq ST), rep_out: (one  Report), s_in: (one  SYM)] {
((pred_BDelete1[bst', rep_out, s_in, bst]) or (pred_Empty[bst, bst', rep_out]))
}
some_BDelete : run { some BDelete }

fun dom[ r: (univ -> univ)] : (set  univ) {
(r . univ)
}

fun DistroSlash[ s: (seq ST)] : (set  (SYM -> VAL)) {
{ sym: SYM, val: VAL | some index: { i: Int | ((i) >= 0)} | (((sym -> val) in ((index . s) . @st)) and all i: { i: Int | ((i) >= 0)} | ((! ((i) > (index)))
 or (! (sym in (dom[((i . s) . @st)]))) or ((sym -> val) in ((i . s) . @st))))}
}

fun ndres[ ex: (set  univ), r: (univ -> univ)] : (univ -> univ) {
(((dom[r]) - ex) <: r)
}
