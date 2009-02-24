sig A{
}{pred_A[]}
pred pred_A[ ] {}
some_A : run { some A }

sig B{
        a: (seq A),
        b: (seq A),
        c: (seq A),
        d: (seq A),
        e: (one  A),
}{pred_B[a, b, c, d, e]}
pred pred_B[ a: (seq A), b: (seq A), c: (seq A), d: (seq A), e: (one  A)] {
((a = seq/append[b, c]) and (e = seq/last[a]) and (d = seq/butlast[a]))
}
some_B : run { some B }
