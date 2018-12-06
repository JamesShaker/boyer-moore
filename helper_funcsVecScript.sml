open HolKernel boolLib bossLib Parse;
open pairTheory;
open rich_listTheory;
open listTheory;
open optionTheory;
open helper_funcsTheory;
open mlvectorTheory;
open regexp_compilerTheory;
open arithmeticTheory;
val _ = new_theory"helper_funcsVec";

(* Replicating Helper Functions but for vectors and proving
   equivalence *)

(* -- EXTRACT FUNCTION -- *)
(* General Purpose Subvector extract function *)
val extractVec_def =
    Define
    `
    extractVec (i,j) v = tabulate (MIN (length v - i) (j - i)) (\a. sub v (a+i))
    `;

(* Equivalent formulation of extract in terms of genlist *)
val EXTRACT_VEC_THM = store_thm(
    "EXTRACT_VEC_THM",
    ``extractVec (i,j) v = Vector (GENLIST (\a. EL (a+i) (toList v)) (MIN (length v - i)(j-i)))``,
    rw[extractVec_def]
    >> rw[tabulate_def]
    >> `?l. v = Vector l` by metis_tac[vector_nchotomy]
    >> rw[sub_def,toList_thm]
    );

(* Proving equivalence to list formulation *)
val EXTRACT_VEC_COR_THM = store_thm(
    "EXTRACT_VEC_COR_THM",
    ``extractVec (a,b) v = Vector (extract (a,b) (toList v))``,
    rw[EXTRACT_VEC_THM,EXTRACT_GEN_THM,length_toList,MIN_COMM]
    );

(* -- UNIQUE ELEMS FUNCTION -- *)
(* Recursive func to build unique elems list from vector *)
val uevRecur_def =
    tDefine "uevRecur"
    `
    uevRecur v i =
        if
            i < length v
        then
            let
                (uniTail  = uevRecur v (SUC i));
                (currElem = sub v i)
            in
                if
                    ~(MEM currElem uniTail)
                then
                    currElem :: uniTail
                else
                    uniTail
        else
            []
    `
    (WF_REL_TAC `measure (\(v, i). length v - i)`);

(* Actual uniqueElems vector func to kick off recursion and produce final vector *)
val uniqueElemsVec_def =
    Define
    `
    uniqueElemsVec v = Vector (uevRecur v 0)
    `;

(* Proof of equivalence to list version *)
val UNIQUE_ELEMS_VEC_COR_THM = store_thm(
    "UNIQUE_ELEMS_VEC_COR_THM",
    ``uniqueElemsVec v = Vector (uniqueElems (toList v))``,
    rw[uniqueElemsVec_def,uniqueElems_def]
    >> Induct_on `v`
    >> Induct_on `l`
    >- (ONCE_REWRITE_TAC[uevRecur_def,toList_thm]
        >> simp[length_def]
        >> simp[uniqueElems_def])
    >- (STRIP_TAC
        >> simp[toList_thm]
        >> ONCE_REWRITE_TAC[uevRecur_def,uniqueElems_def]
        >> simp[length_def,sub_def]
        >> `uevRecur (Vector (h::l)) 1 = uevRecur (Vector l) 0`
                suffices_by (fs[toList_thm]
                             >> Cases_on `MEM h (uniqueElems l)`
                             >> simp[])
        >> `!n. uevRecur (Vector (h::l)) (SUC n) = uevRecur (Vector l) n`
                suffices_by metis_tac[DECIDE ``1 = SUC 0``]
        >> STRIP_TAC
        >> Induct_on `LENGTH l - n`
        >- (rpt STRIP_TAC
            >> ONCE_REWRITE_TAC[uevRecur_def]
            >> simp[length_def])
        >- (rpt STRIP_TAC
            >> ONCE_REWRITE_TAC[uevRecur_def]
            >> `n < length (Vector l)` by simp[length_def]
            >> `SUC n < length (Vector (h::l))` by simp[length_def]
            >> simp [sub_def])
        )
    );

(* -- FIND ELEMS FUNCTION -- *)
(* Find first index of element in list. Returns past end of list if no elem *)

val findElemVecRecur_def =
    tDefine "findElemVecRecur"
    `
    findElemVecRecur v e i =
        if
            (i < length v) /\
            (sub v i <> e)
        then
            findElemVecRecur v e (SUC i)
        else
            i
    `
    (WF_REL_TAC `measure (\(v, e, i). length v - i)`);

val findElemVec_def =
    Define
    `
    findElemVec v e = findElemVecRecur v e 0
    `;

(* Proof of equivalence to list version *)

val FIND_ELEM_VEC_COR_THM = store_thm(
    "FIND_ELEM_VEC_COR_THM",
    ``findElemVec v e = findElem (toList v) e``,
    `?l. v = Vector l`
            by rw[vector_nchotomy]
    >> rw[toList_thm]
    >> Induct_on `l`
    >- (ONCE_REWRITE_TAC[findElemVec_def,findElem_def]
        >> ONCE_REWRITE_TAC[findElemVecRecur_def]
        >> simp[length_def])
    >- (ONCE_REWRITE_TAC[findElemVec_def,findElem_def]
        >> ONCE_REWRITE_TAC[findElemVecRecur_def]
        >> simp[length_def,sub_def]
        >> STRIP_TAC
        >> Cases_on `h=e`
        >- simp[]
        >- (simp[]
            >> `findElemVecRecur (Vector (h::l)) e 1 = findElemVec (Vector l) e + 1`
                    suffices_by rw[]
            >> `!i. i < LENGTH l ==>
                    (findElemVecRecur (Vector l) e i + 1
                    = findElemVecRecur (Vector (h::l)) e (SUC i))`
                    suffices_by (ONCE_REWRITE_TAC[findElemVec_def]
                                 >> Cases_on `l`
                                 >- (simp[]
                                     >> ONCE_REWRITE_TAC [findElemVecRecur_def]
                                     >> simp[length_def])
                                 >- simp[])
            >> Induct_on `LENGTH l - i`
            >- simp[]
            >- (rpt STRIP_TAC
                >> ONCE_REWRITE_TAC[findElemVecRecur_def]
                >> `sub (Vector l) i = sub (Vector (h::l)) (SUC i)`
                        by rw[sub_def,EL]
                >> Cases_on `sub (Vector l) i <> e`
                >> Cases_on `sub (Vector (h::l)) (SUC i) <> e`
                >> fs[]
                >> Cases_on `SUC i < LENGTH l`
                >- simp[length_def]
                >- (simp[length_def]
                    >> ONCE_REWRITE_TAC[findElemVecRecur_def]
                    >> simp[length_def])
                )
            )
        )
    );

(* -- CHECK PREFIX RL FUNCTION -- *)
val checkPrefixRLVecRecur_def =
    tDefine "checkPrefixRLVecRecur"
    `
    checkPrefixRLVecRecur pat search i =
        let
            index = PRE (length pat) - i
        in
            if
                i < length pat
            then
                if
                    (sub pat index = sub search index)
                then
                    checkPrefixRLVecRecur pat search (SUC i)
                else
                    index
            else
                i
    `
    (WF_REL_TAC `measure (\(p, s, i). length p - i)`);

val checkPrefixRLVec_def =
    Define
    `checkPrefixRLVec pat search =
        if
            length pat <= length search
        then
            checkPrefixRLVecRecur pat search 0
        else
            length pat + 1
    `;


(* Proof of equivalence to list version *)
val CHECK_PREFIX_RL_VEC_COR_THM = store_thm(
    "CHECK_PREFIX_RL_VEC_COR_THM",
    ``checkPrefixRLVec pat search = checkPrefixRL (toList pat) (toList search)``,
    rw[checkPrefixRLVec_def,checkPrefixRL_def]
    >- fs[length_toList]
    >- (qabbrev_tac `ps = ZIP ((REVERSE (toList pat)),
                               (REVERSE (TAKE (LENGTH (toList pat)) (toList search))))`
        >> `LENGTH (toList pat) = LENGTH ps`
                by rw[Abbr `ps`, LENGTH_ZIP, LENGTH_REVERSE,LENGTH_TAKE]
        >> `checkPairs ps = LENGTH ps`
                by (`checkPairs ps <= LENGTH ps` by rw[CHECK_PAIRS_BND]
                    >> `checkPairs ps >= LENGTH ps` by rw[]
                    >> simp[])
        >> `!i. (i < LENGTH ps) ==> (FST (EL i ps) = SND (EL i ps))`
                by fs[CHECK_PAIRS_MATCH]
        >> `!i. (i < LENGTH ps) ==>
                    (EL i ps =
                        (EL i (REVERSE (toList pat)),
                         EL i (REVERSE (TAKE (LENGTH (toList pat)) (toList search))))
                    )`
                by simp[Abbr `ps`, EL_ZIP]
        >> `!i. (i < LENGTH ps) ==>
                    (EL i (REVERSE (toList pat)) =
                     EL i (REVERSE (TAKE (LENGTH (toList pat)) (toList search))))`
                     by fs[FST,SND]
        >> qabbrev_tac `P = toList pat`
        >> qabbrev_tac `Se = toList search`
        >> qabbrev_tac `fS = TAKE (LENGTH P) Se`
        >> `!i. (i < LENGTH P) ==> (EL (PRE (LENGTH P - i)) P
                                    = EL (PRE (LENGTH fS - i)) fS)`
                by (rpt STRIP_TAC
                    >> `EL i (REVERSE P) = EL (PRE (LENGTH P - i)) P`
                            by metis_tac[EL_REVERSE]
                    >> `LENGTH fS = LENGTH P`
                            by rw[Abbr `fS`, Abbr `Se`, LENGTH_TAKE]
                    >> `EL i (REVERSE fS) = EL (PRE (LENGTH P - i)) fS`
                            by metis_tac[EL_REVERSE]
                    >> `EL i (REVERSE P) = EL i (REVERSE fS)`
                           suffices_by simp[]
                    >> Q.UNDISCH_THEN `!i. i < LENGTH ps ==> EL i (REVERSE P)
                                        = EL i (REVERSE fS)` mp_tac
                    >> metis_tac[])
        >> `!j. j < LENGTH P ==> EL j P = EL j fS`
                by (rpt STRIP_TAC
                    >> `(PRE (LENGTH P) - j) < LENGTH P`
                            by fs[]
                    >>  qabbrev_tac `i = (PRE (LENGTH P) - j)`
                    >> `EL (PRE (LENGTH P - i)) P = EL (PRE (LENGTH P - i)) fS`
                            by (`LENGTH P = LENGTH fS`
                                    by rw[Abbr `P`, Abbr `fS`, Abbr `Se`, LENGTH_TAKE]
                                >> metis_tac[])
                    >> `PRE (LENGTH P - i) = j`
                            by rw[Abbr `i`]
                    >> fs[])
        >> `!j. j < LENGTH P ==> (EL j P = EL j Se)`
                by rw[Abbr `P`, Abbr `fS`, Abbr `Se`, EL_TAKE]
        >> `!j. j < length pat ==> (sub pat j = sub search j)`
                by  (rpt STRIP_TAC
                    >> `fromList P = pat`
                        by rw[Abbr `P`, toList_fromList]
                    >> `sub pat j = EL j P`
                            by rw[sub_def,fromList_def]
                    >> `fromList Se = search`
                            by rw[Abbr `Se`, toList_fromList]
                    >> `sub search j = EL j Se`
                            by rw[sub_def,fromList_def]
                    >> `j < LENGTH P`
                            by fs[Abbr `P`, length_toList]
                    >> fs[])
        >> `!i. i < length pat ==> checkPrefixRLVecRecur pat search i = length pat`
                by (Induct_on `length pat - i`
                    >- simp[]
                    >- (rpt STRIP_TAC
                        >> `v = length pat - SUC i`
                                by simp[ADD_CLAUSES]
                        >> Cases_on `SUC i = length pat`
                        >- (ONCE_REWRITE_TAC[checkPrefixRLVecRecur_def]
                            >> simp[]
                            >> ONCE_REWRITE_TAC[checkPrefixRLVecRecur_def]
                            >> simp[])
                        >- (`SUC i < length pat`
                                by simp[]
                            >> `checkPrefixRLVecRecur pat search (SUC i) = length pat`
                                    by metis_tac[]
                            >> ONCE_REWRITE_TAC[checkPrefixRLVecRecur_def]
                            >> simp[])
                        )
                    )
        >> `length pat = LENGTH ps`
                by (`length pat = LENGTH (toList pat)`
                        by (ONCE_REWRITE_TAC[EQ_SYM_EQ]
                            >> ONCE_REWRITE_TAC[length_toList]
                            >> simp[])
                    >> simp[])
        >> Cases_on `0 < length pat`
        >- metis_tac[]
        >- (ONCE_REWRITE_TAC[checkPrefixRLVecRecur_def]
            >> `LENGTH ps = 0`
                    suffices_by simp[LENGTH_EQ_NUM]
            >> fs[ADD_CLAUSES]
            )
        )
    >- (qabbrev_tac `P = toList pat`
        >> qabbrev_tac `Se = toList search`
        >> qabbrev_tac `ps = ZIP (REVERSE P, REVERSE (TAKE (LENGTH P) Se))`
        >> `LENGTH P = length pat`
                by simp[Abbr `P`, length_toList]
        >> `!x . x < length pat ==>
                    (sub pat (PRE (length pat) - x) = EL x (REVERSE P))
                    /\ (sub search (PRE (length pat) - x) = EL x (REVERSE (TAKE (length pat) Se)))`
                by (rpt STRIP_TAC
                    >- (`fromList P = pat`
                            by rw[Abbr `P`, toList_fromList]
                        >> `sub pat (PRE (length pat) - x) = EL (PRE (length pat) - x) P`
                                by rw[sub_def,fromList_def]
                        >> `EL (PRE (length pat) - x) P = EL x (REVERSE P)`
                                by (rw[Abbr `P`, EL_REVERSE]
                                    >> rw[length_toList]
                                    >> rw[DECIDE ``PRE a - b = PRE (a - b)``])
                        >> simp[])
                    >- (`fromList Se = search`
                            by rw[Abbr `Se`, toList_fromList]
                        >> `sub search (PRE (length pat) - x) = EL (PRE (length pat) - x) Se`
                                by rw[sub_def,fromList_def]
                        >> `EL (PRE (length pat) - x) Se = EL (PRE (length pat) - x) (TAKE (length pat) Se)`
                                by rw[EL_TAKE]
                        >> `length pat > 0`
                                by (CCONTR_TAC
                                    >> fs[Abbr `P`, length_toList])
                        >> `PRE (length pat) - x < length pat`
                                by simp[]
                        >> `EL (PRE (length pat) - x) (TAKE (length pat) Se)
                                = EL x (REVERSE (TAKE (length pat) Se))`
                                by simp[EL_REVERSE, DECIDE ``PRE a - i = PRE (a - i)``]
                        >> simp[]))
        >> `!i . i < checkPairs ps ==> (sub pat (PRE (length pat) - i)
                                        = sub search (PRE (length pat) - i))`
                by (rpt STRIP_TAC
                    >> `EL i (REVERSE P) = EL i (REVERSE (TAKE (length pat) Se))`
                            suffices_by rw[]
                    >> `FST (EL i ps) = SND (EL i ps)`
                            suffices_by rw[Abbr `ps`, EL_ZIP, FST, SND]
                    >> `LENGTH ps = LENGTH P`
                            suffices_by rw[CHECK_PAIRS_THM]
                    >> rw[Abbr `ps`, LENGTH_ZIP, LENGTH_REVERSE, LENGTH_TAKE])
        >> `sub pat (PRE (length pat) - checkPairs ps) <> sub search (PRE (length pat) - checkPairs ps)`
                by (`EL (checkPairs ps) (REVERSE P) <> EL (checkPairs ps) (REVERSE (TAKE (length pat) Se))`
                            suffices_by rw[]
                    >> `FST (EL (checkPairs ps) ps) <> SND (EL (checkPairs ps) ps)`
                            suffices_by (qabbrev_tac `j = checkPairs ps`
                                         >> qunabbrev_tac `ps`
                                         >> rw[EL_ZIP,FST,SND])
                    >> `LENGTH ps = LENGTH P`
                            suffices_by rw[CHECK_PAIRS_THM]
                    >> rw[Abbr `ps`, LENGTH_ZIP, LENGTH_REVERSE, LENGTH_TAKE])
        >> `checkPrefixRLVecRecur pat search 0 = checkPrefixRLVecRecur pat search (checkPairs ps)`
                suffices_by (simp[]
                             >> STRIP_TAC
                             >> ONCE_REWRITE_TAC[checkPrefixRLVecRecur_def]
                             >> simp[])
        >> `! i. i <= checkPairs ps ==> (checkPrefixRLVecRecur pat search i =
                                            checkPrefixRLVecRecur pat search (checkPairs ps))`
                suffices_by simp[]
        >> Induct_on `checkPairs ps - i`
        >- (rpt STRIP_TAC
            >> `i = checkPairs ps`
                    by fs[]
            >> simp[])
        >- (rpt STRIP_TAC
            >> Cases_on `i = checkPairs ps`
            >> simp[]
            >> qabbrev_tac `j = checkPrefixRLVecRecur pat search (checkPairs ps)`
            >> ONCE_REWRITE_TAC[checkPrefixRLVecRecur_def]
            >> simp[]
            >> `v = checkPairs ps - SUC i`
                    by simp[]
            >> `SUC i <= checkPairs ps`
                    by simp[]
            >> metis_tac[]))
    >- rw[length_toList]
    >- fs[length_toList]
    >- fs[length_toList]);


val checkPrefixRLVecShiftRecur_def =
    tDefine "checkPrefixRLVecShiftRecur"
    `
    checkPrefixRLVecShiftRecur pat search shift i =
        let
            index = PRE (length pat) - i
        in
            if
                i < length pat
            then
                if
                    (sub pat index = sub search (index+shift))
                then
                    checkPrefixRLVecShiftRecur pat search shift (SUC i)
                else
                    index
            else
                i
    `
    (WF_REL_TAC `measure (\(p, s1, s2, i). length p - i)`);

val checkPrefixRLVecShift_def =
    Define
    `checkPrefixRLVecShift pat search shift =
        if
            length pat <= length search - shift
        then
            checkPrefixRLVecShiftRecur pat search shift 0
        else
            length pat + 1
    `;

val CHECK_PREFIX_RL_VEC_SHIFT_COR_THM = store_thm(
    "CHECK_PREFIX_RL_VEC_SHIFT_COR_THM",
    ``checkPrefixRLVecShift pat search shift
         = checkPrefixRL (toList pat) (DROP shift (toList search))``,
    `checkPrefixRL (toList pat) (DROP shift (toList search))
                = checkPrefixRLVec pat (Vector (DROP shift (toList search)))`
                by rw[CHECK_PREFIX_RL_VEC_COR_THM,toList_thm]
    >> `checkPrefixRLVecShift pat search shift
                = checkPrefixRLVec pat (Vector (DROP shift (toList search)))`
                suffices_by rw[]
    >> Cases_on `length pat <= length search - shift`
    >- (ONCE_REWRITE_TAC[checkPrefixRLVecShift_def, checkPrefixRLVec_def]
        >> rw[]
        >- (fs[length_def,length_toList]
            >> `! i. checkPrefixRLVecShiftRecur pat search shift i
                    = checkPrefixRLVecRecur pat (Vector (DROP shift (toList search))) i`
                    suffices_by metis_tac[]
            >> Induct_on `length pat - i`
            >- (rpt STRIP_TAC
                >> ONCE_REWRITE_TAC[checkPrefixRLVecRecur_def,checkPrefixRLVecShiftRecur_def]
                >> simp[])
            >- (rpt STRIP_TAC
                >> ONCE_REWRITE_TAC[checkPrefixRLVecRecur_def,checkPrefixRLVecShiftRecur_def]
                >> simp[]
                >> `sub search (shift + PRE (length pat) - i)
                        = sub (Vector (DROP shift (toList search))) (PRE (length pat) - i)`
                        by (`? slst. search = Vector slst`
                                by rw[vector_nchotomy]
                            >> fs[sub_def,length_def,toList_thm]
                            >> `shift + PRE (length pat) - i < LENGTH slst`
                                    suffices_by rw[EL_DROP]
                            >> rw[])
                >> simp[])
            )
        >- fs[length_def,LENGTH_DROP,length_toList])
    >- (ONCE_REWRITE_TAC[checkPrefixRLVecShift_def, checkPrefixRLVec_def]
        >> simp[length_def,LENGTH_DROP,length_toList])
    );

val _ = export_theory();

