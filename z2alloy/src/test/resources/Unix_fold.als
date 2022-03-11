sig BYTE{}

sig ZERO in BYTE{
}{(pred_ZERO[])}


pred pred_ZERO[] {}

sig FILE{
	contents: (seq BYTE),
}{(pred_FILE[contents])}


pred pred_FILE[contents: (seq BYTE)] {}

sig DS{
	file: FILE,
}{(pred_DS[file])}


pred pred_DS[file: FILE] {}

sig InitDS{
	file': FILE,
}{(pred_InitDS[file'])}


pred pred_InitDS[file': FILE] {
	((pred_DS[file']) && ((file' . contents) = (none -> none)))
}

fun after[f: FILE, offset: {i: Int | (i >= 0)}] : (set  (Int -> BYTE)) {
	{i: {i: Int | ((i >= 1) && (i <= ((# (f . contents)) - offset)))}, j: BYTE | (j = ((i + offset) . (f . contents)))}
}

sig XiDS{
	file: FILE,
	file': FILE,
}{(pred_XiDS[file, file'])}


pred pred_XiDS[file: FILE, file': FILE] {
	(file = file')
}

sig readFILE{
	file: FILE,
	file': FILE,
	offset_in: {i: Int | (i >= 0)},
	length_in: {i: Int | (i >= 0)},
	data_out: FILE,
}{(pred_readFILE[file, file', offset_in, length_in, data_out])}


pred pred_readFILE[file: FILE, file': FILE, offset_in: {i: Int | (i >= 0)}, length_in: {i: Int | (i >= 0)}, data_out: FILE] {
	((pred_XiDS[file, file']) && ((data_out . contents) = ({i: Int | ((i >= 1) && (i <= length_in))} <: (after[file, offset_in]))))
}

fun zero[n: {i: Int | (i >= 0)}] : (set  (Int -> BYTE)) {
	{k: {i: Int | ((i >= 1) && (i <= n))}, j: BYTE | (j = ZERO)}
}

fun shift[f: FILE, offset: {i: Int | (i >= 0)}] : (set  (Int -> BYTE)) {
	(ndres[{i: Int | ((i >= 1) && (i <= offset))}, (append[(zero[offset]), (f . contents)])])
}

sig DeltaDS{
	file: FILE,
	file': FILE,
}{(pred_DeltaDS[file, file'])}


pred pred_DeltaDS[file: FILE, file': FILE] {}

sig writeFILE{
	file: FILE,
	file': FILE,
	offset_in: {i: Int | (i >= 0)},
	data_in: FILE,
}{(pred_writeFILE[file, file', offset_in, data_in])}


pred pred_writeFILE[file: FILE, file': FILE, offset_in: {i: Int | (i >= 0)}, data_in: FILE] {
	((pred_DeltaDS[file, file']) && ((file' . contents) = (((zero[offset_in]) ++ (file . contents)) ++ (shift[data_in, offset_in]))))
}

sig FID{}

sig SS{
	fstore: (FID ->lone FILE),
}{(pred_SS[fstore])}


pred pred_SS[fstore: (FID ->lone FILE)] {}

sig InitSS{
	fstore': (FID ->lone FILE),
}{(pred_InitSS[fstore'])}


pred pred_InitSS[fstore': (FID ->lone FILE)] {
	((pred_SS[fstore']) && (fstore' = (none -> none)))
}

sig DeltaSS{
	fstore: (FID ->lone FILE),
	fstore': (FID ->lone FILE),
}{(pred_DeltaSS[fstore, fstore'])}


pred pred_DeltaSS[fstore: (FID ->lone FILE), fstore': (FID ->lone FILE)] {}

sig createSS{
	fstore: (FID ->lone FILE),
	fstore': (FID ->lone FILE),
	fid_in: FID,
}{(pred_createSS[fstore, fstore', fid_in])}


pred pred_createSS[fstore: (FID ->lone FILE), fstore': (FID ->lone FILE), fid_in: FID] {
	((pred_DeltaSS[fstore, fstore']) && one f: FILE | (((f . contents) = (none -> none)) && (fstore' = (fstore ++ (fid_in -> f)))))
}

sig destroySS{
	fstore: (FID ->lone FILE),
	fstore': (FID ->lone FILE),
	fid_in: FID,
}{(pred_destroySS[fstore, fstore', fid_in])}


pred pred_destroySS[fstore: (FID ->lone FILE), fstore': (FID ->lone FILE), fid_in: FID] {
	((pred_DeltaSS[fstore, fstore']) && ((fid_in in (dom[fstore])) && (fstore' = (ndres[fid_in, fstore]))))
}

sig PhiSS{
	fstore: (FID ->lone FILE),
	fstore': (FID ->lone FILE),
	file: FILE,
	file': FILE,
	fid_in: FID,
}{(pred_PhiSS[fstore, fstore', file, file', fid_in])}


pred pred_PhiSS[fstore: (FID ->lone FILE), fstore': (FID ->lone FILE), file: FILE, file': FILE, fid_in: FID] {
	(((pred_DeltaSS[fstore, fstore']) && (pred_DeltaDS[file, file'])) && (((fid_in in (dom[fstore])) && (file = (fid_in . fstore))) && (fstore' = (fstore ++ (fid_in -> file')))))
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


