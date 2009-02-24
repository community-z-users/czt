sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig B{
        a: (set  (Int -> A)),
        b: (set  (Int -> A)),
        c: (set  (Int -> A)),
        d: (set  (Int -> A)),
        e: (one  A),
}{pred_B[a, b, c, d, e]}
pred pred_B[ a: (set  (Int -> A)), b: (set  (Int -> A)), c: (set  (Int -> A)), d: (set  (Int -> A)), e: (one  A)] {
((a in (seq A)) and (b in (seq A)) and (c in (seq A)) and (d in (seq A)) and (a = seq/append[b, c]) and (e = seq/last[a]) and (d = seq/butlast[a]))
}
some_B : run { some B }
