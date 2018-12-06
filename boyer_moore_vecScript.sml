open HolKernel boolLib bossLib Parse;

open arithmeticTheory;
open listTheory;
open rich_listTheory;

open mlvectorTheory;
open regexp_compilerTheory;

open stringTheory;

open helper_funcsVecTheory;

open boyer_mooreTheory;

val _ = new_theory"boyer_moore_vec";

(* -- IMPLICIT CHARACTER MISMATCH TABLE CONSTRUCTION -- *)
(* Assess potential shift based on character mismatch rule *)
val checkDeltaCVec_def =
	Define
	`
	checkDeltaCVec pat all_chars j a d =
		((d = j+1) \/ (sub pat (j-d) = sub all_chars a))
	`;

(* Find minimum valid character mismatch based shift *)
val cmRecurVec_def =
    tDefine "cmRecurVec"
    `
    cmRecurVec pat all_chars j a d =
        if (j+1 < d) then d
        else if (checkDeltaCVec pat all_chars j a d) then d
        else (cmRecurVec pat all_chars j a (d+1))
    `
    (WF_REL_TAC `measure (\(p, c, j, a, d). SUC j - d)`
    >> fs[ADD1,checkDeltaCVec_def]);

val cmValVec_def =
    Define
    `
    cmValVec pat all_chars j a = cmRecurVec pat all_chars j a 1
    `;

(* Confirm vector version conforms to original *)
val CHECK_DELTAC_VEC_COR_THM = store_thm(
    "CHECK_DELTAC_VEC_COR_THM",
    ``checkDeltaCVec pat all_chars j a d =
		checkDeltaC (toList pat) (toList all_chars) j a d``,
	rw[checkDeltaCVec_def, checkDeltaC_def]
	>> `pat = fromList (toList pat)`
			by rw[toList_fromList]
	>> `all_chars = fromList (toList all_chars)`
			by rw[toList_fromList]
	>> qabbrev_tac `P = toList pat`
	>> qabbrev_tac `A = toList all_chars`
	>> rw[sub_def,fromList_def]);

val CMRECUR_VEC_COR_THM = store_thm(
    "CMRECUR_VEC_COR_THM",
    ``cmRecurVec pat all_chars j a d
		= cmRecur (toList pat) (toList all_chars) j a d``,
	Induct_on `SUC j - d`
	>- (ONCE_REWRITE_TAC[cmRecurVec_def,cmRecur_def]
		>> rpt STRIP_TAC
		>> `j + 1 <= d`
				by rw[ADD1]
		>> Cases_on `j + 1 = d`
		>- (simp[CHECK_DELTAC_VEC_COR_THM]
			>> `cmRecurVec pat all_chars j a (d + 1)
					= cmRecur (toList pat) (toList all_chars) j a (d + 1)`
					suffices_by rw[]
			>> ONCE_REWRITE_TAC[cmRecurVec_def,cmRecur_def]
			>> simp[])
		>- simp[])
	>- (ONCE_REWRITE_TAC[cmRecurVec_def,cmRecur_def]
		>> rpt STRIP_TAC
		>> `j + 1 > d`
				by simp[ADD1]
		>> simp[CHECK_DELTAC_VEC_COR_THM])
	);

val CMVAL_VEC_COR_THM = store_thm(
    "CMVAL_VEC_COR_THM",
    ``cmValVec pat all_chars j a = cmVal (toList pat) (toList all_chars) j a``,
	simp[cmValVec_def,cmVal_def,CMRECUR_VEC_COR_THM]
	);

(* -- IMPLICIT SUFFIX MATCH TABLE CONSTRUCTION -- *)
(* Assess potential shift based on suffix mismatch rule *)
val checkDeltaSVec_def =
    Define
    `
    checkDeltaSVec pat j d = 
        (((d >= SUC j) \/ ~(sub pat (j-d) = sub pat j)) /\
        (extractVec (MAX (SUC j) d,length pat) pat
            = extractVec ((MAX (SUC j) d) - d,length pat - d) pat))
    `;

(* Find minimum valid suffix mismatch based shift *)
val smRecurVec_def =
    tDefine "smRecurVec"
    `
    smRecurVec pat j d =
        if (length pat < d) then d
        else if (checkDeltaSVec pat j d) then d
        else (smRecurVec pat j (d+1))
    `
    (WF_REL_TAC `measure (\(p, j, d). SUC (length p) - d)`);

val smValVec_def =
    Define
    `
    smValVec pat j = smRecurVec pat j 1
    `;

(* Confirm vector version conforms to original *)
val CHECK_DELTAS_VEC_COR_THM = store_thm(
    "CHECK_DELTAS_VEC_COR_THM",
    ``checkDeltaSVec pat j d = checkDeltaS (toList pat) j d``,
	rw[checkDeltaSVec_def,checkDeltaS_def]
	>> `pat = fromList (toList pat)`
			by rw[toList_fromList]
	>> qabbrev_tac `P = toList pat`
	>> rw[sub_def,fromList_def,EXTRACT_VEC_COR_THM,
			length_def]);

val SMRECUR_VEC_COR_THM = store_thm(
    "SMRECUR_VEC_COR_THM",
    ``smRecurVec pat j d = smRecur (toList pat) j d``,
	Induct_on `length pat - d`
	>- (ONCE_REWRITE_TAC[smRecurVec_def,smRecur_def]
		>> simp[length_toList,CHECK_DELTAS_VEC_COR_THM]
		>> rpt STRIP_TAC
		>> `length pat <= d`
				by rw[]
		>> Cases_on `length pat = d`
		>- (simp[CHECK_DELTAS_VEC_COR_THM,length_toList]
			>> `smRecurVec pat j (d + 1)
					= smRecur (toList pat) j (d + 1)`
					suffices_by rw[]
			>> ONCE_REWRITE_TAC[smRecurVec_def,smRecur_def]
			>> simp[length_toList])
		>- simp[length_toList])
	>- (ONCE_REWRITE_TAC[smRecurVec_def,smRecur_def]
		>> rpt STRIP_TAC
		>> `length pat > d`
				by simp[ADD1]
		>> simp[CHECK_DELTAS_VEC_COR_THM,length_toList])
	);

val SMVAL_VEC_COR_THM = store_thm(
    "SMVAL_VEC_COR_THM",
    ``smValVec pat j = smVal (toList pat) j``,
	simp[smValVec_def,smVal_def,SMRECUR_VEC_COR_THM]);

(* -- ACTUAL MISMATCH TABLE CONSTRUCTION --  *)
(* Find mismatch table value at particular point based
   on best shift available between suffix mismatch table
   and character mismatch table *)
val mValVec_def =
    Define
    `
    mValVec calc_smVal pat all_chars j a =
        MAX calc_smVal (cmValVec pat all_chars j a)
    `;

(* Generate a row of mismatch table *)
val mSubTabVec_def =
    Define
    `
    mSubTabVec pat all_chars j =
        tabulate (length all_chars) (mValVec (smValVec pat j) pat all_chars j)
    `;

(* Generate mismatch table *)
val mTabVec_def =
    Define
    `
    mTabVec pat all_chars =
        tabulate (length pat) (mSubTabVec pat all_chars)
    `;

(* Confirm vector version conforms to original *)
val MVAL_VEC_COR_THM = store_thm(
    "MVAL_VEC_COR_THM",
    ``mValVec calc_smVal pat all_chars j a
		= mVal calc_smVal (toList pat) (toList all_chars) j a``,
	simp[mValVec_def,mVal_def]
	>> simp[CMVAL_VEC_COR_THM]);

val MSUBTAB_VEC_COR_THM = store_thm(
    "MSUBTAB_VEC_COR_THM",
    ``mSubTabVec pat all_chars j
		= Vector (mSubTab (toList pat) (toList all_chars) j)``,
	rw[mSubTabVec_def,mSubTab_def]
	>> rw[tabulate_def, length_toList]
	>> `!a. mVal (smVal (toList pat) j) (toList pat) (toList all_chars) j a
			= mValVec (smValVec pat j) pat all_chars j a`
			suffices_by metis_tac[]
	>> rw[SMVAL_VEC_COR_THM,MVAL_VEC_COR_THM]
	);

val MTAB_VEC_COR_A_THM = store_thm(
    "MTAB_VEC_COR_A_THM",
    ``!j. j < length pat ==> sub (mTabVec pat all_chars) j = Vector (EL j (mTab (toList pat) (toList all_chars)))``,
	simp[mTabVec_def,sub_def,tabulate_def,mTab_def]
	>> simp[length_toList]
	>> simp[EL_GENLIST]
	>> simp[MSUBTAB_VEC_COR_THM]);

val MTAB_VEC_COR_B_THM = store_thm(
    "MTAB_VEC_COR_B_THM",
    ``!j a. (a < length all_chars) /\ (j < length pat)
				==> (sub (sub (mTabVec pat all_chars) j) a
						= EL a (EL j (mTab (toList pat) (toList all_chars))))``,
	rpt STRIP_TAC
	>> simp[MTAB_VEC_COR_A_THM]
	>> simp[sub_def]);

(* -- BOYER-MOORE SEARCH IMPLEMENTATION -- *)
(* Checks to see if pat is prefix of search and skips verified bad alignments
   based on patTab and all_chars if not to recursively find the minimum
   solution. Returning length search indicates no substrings, returning
   length search + 1 indicates there's been an error likely due to a malformed
   patTab *)
val bmRecurVec_def =
    tDefine "bmRecurVec"
    `
    bmRecurVec pat patTab all_chars search i =
    	if
    		(length pat = 0) \/
    		(length search - i = 0)
    	then
    		0
    	else
	        if
	            ~(length pat <= length search - i)
	        then
	            (length search - i)
	        else
	            let
	                (j = checkPrefixRLVecShift pat search i)
	            in
	                if
	                    ~(j < length patTab)
	                then
	                    0
	                else
	                    let
	                        (a = findElemVec all_chars (sub search (i+j)))
	                    in
	                        if
	                            ~(a < length (sub patTab j))
	                        then
	                            (length search - i + 1)
	                        else
	                            let 
	                                (d = sub (sub patTab j) a)
	                            in
	                                if
	                                    ~(0 < d)
	                                then
	                                    (length search - i + 1)
	                                else
	                                    (d + (bmRecurVec pat patTab
	                                            all_chars search (i+d)))
    `
    (WF_REL_TAC `measure (\(_, _, _, search, i). length search - i)`
    >> rw[DROP]);
 
val BMRECUR_VEC_COR_THM = store_thm(
    "BMRECUR_VEC_COR_THM",
    ``! pat all_chars patTabVec patTabLst search i.
	(length pat = length patTabVec) /\
	(length patTabVec = LENGTH patTabLst) /\
	(!j. j < length patTabVec ==> (sub patTabVec j = Vector (EL j patTabLst)))
	==> (bmRecurVec pat patTabVec all_chars search i
			= bmRecur (toList pat) patTabLst (toList all_chars) (DROP i (toList search)))``,
	rpt STRIP_TAC
	>> completeInduct_on `length search - i`
	>> rpt STRIP_TAC
	>> `? plst. pat = Vector plst`
		by rw[vector_nchotomy]
	>> `? slst. search = Vector slst`
			by rw[vector_nchotomy]
	>> fs[toList_thm, length_def,LENGTH]
	>> rpt STRIP_TAC
	>> Cases_on `(plst <> []) /\ ((DROP i slst) <> [])`
	>- (`i < LENGTH slst`
			by (CCONTR_TAC
				>> `LENGTH slst <= i`
						suffices_by fs[DROP_NIL]
				>> simp[])
		>> `slst <> []`
				by (`LENGTH slst > 0`
						suffices_by simp[DECIDE ``a:num > 0 <=> a:num <> 0``]
					>> rw[])
		>> `0 < LENGTH plst`
				by (`0 <> LENGTH plst`
						suffices_by simp[DECIDE ``0 <> a:num ==> 0 < a:num``]
					>> fs[LENGTH_NIL])
		>> `patTabLst <> []`
					by (`LENGTH patTabLst > 0`
								suffices_by rw[LENGTH_NIL, DECIDE ``a:num > 0 <=> a:num <> 0``]
						>> rw[])
		>> rw[BMRECUR_NON_EMPTY_DEF]
		>- (ONCE_REWRITE_TAC[bmRecurVec_def]
			>> simp[length_def])
		>- (ONCE_REWRITE_TAC[bmRecurVec_def]
			>> simp[length_def]
			>> `~(checkPrefixRLVecShift (Vector plst) (Vector slst) i < LENGTH patTabLst)`
					suffices_by (Cases_on `LENGTH slst <= i`
								 >> simp[])
			>> `checkPrefixRLVecShift (Vector plst) (Vector slst) i = checkPrefixRL plst (DROP i slst)`
					suffices_by rw[]
			>> simp[CHECK_PREFIX_RL_VEC_SHIFT_COR_THM,toList_thm])
		>- (ONCE_REWRITE_TAC[bmRecurVec_def]
			>> simp[length_def]
			>> simp[CHECK_PREFIX_RL_VEC_SHIFT_COR_THM,toList_thm]
			>> `~(findElemVec all_chars (sub (Vector slst) (i + checkPrefixRL plst (DROP i slst))) <
					LENGTH (EL (checkPrefixRL plst (DROP i slst)) patTabLst))`
					suffices_by rw[]
			>> `findElemVec all_chars (sub (Vector slst) (i + checkPrefixRL plst (DROP i slst)))
					= findElem (toList all_chars) (EL (checkPrefixRL plst (DROP i slst)) (DROP i slst))`
					suffices_by rw[]
			>> simp[FIND_ELEM_VEC_COR_THM,toList_thm,sub_def]
			>> `i + checkPrefixRL plst (DROP i slst) < LENGTH slst`
					suffices_by (STRIP_TAC
								 >> fs[EL_DROP])
			>> `i + LENGTH patTabLst <= LENGTH slst`
					suffices_by simp[]
			>> fs[])
		>- (ONCE_REWRITE_TAC[bmRecurVec_def]
			>> simp[length_def,CHECK_PREFIX_RL_VEC_SHIFT_COR_THM,toList_thm]
			>> `findElemVec all_chars (sub (Vector slst) (i + checkPrefixRL plst (DROP i slst)))
					= findElem (toList all_chars) (EL (checkPrefixRL plst (DROP i slst)) (DROP i slst))`
					by (simp[FIND_ELEM_VEC_COR_THM,toList_thm,sub_def]
						>> `i + checkPrefixRL plst (DROP i slst) < LENGTH slst`
								suffices_by (STRIP_TAC
								 			 >> fs[EL_DROP])
						>> `i + LENGTH patTabLst <= LENGTH slst`
								suffices_by simp[]
						>> fs[])
			>> simp[sub_def])
		>- (ONCE_REWRITE_TAC[bmRecurVec_def]
			>> simp[length_def,CHECK_PREFIX_RL_VEC_SHIFT_COR_THM,toList_thm]
			>> `findElemVec all_chars (sub (Vector slst) (i + checkPrefixRL plst (DROP i slst)))
					= findElem (toList all_chars) (EL (checkPrefixRL plst (DROP i slst)) (DROP i slst))`
					by (simp[FIND_ELEM_VEC_COR_THM,toList_thm,sub_def]
						>> `i + checkPrefixRL plst (DROP i slst) < LENGTH slst`
								suffices_by (STRIP_TAC
								 			 >> fs[EL_DROP])
						>> `i + LENGTH patTabLst <= LENGTH slst`
								suffices_by simp[]
						>> fs[])
			>> simp[sub_def]
			>> qabbrev_tac `j = checkPrefixRL plst (DROP i slst)`
			>> qabbrev_tac `a = findElem (toList all_chars) (EL j (DROP i slst))`
			>> qabbrev_tac `d = EL a (EL j patTabLst)`
			>> rw[DROP_DROP_T]))
	>-  (Cases_on `plst = []`
		 >- (rw[bmRecur_def]
		 	 >> ONCE_REWRITE_TAC[bmRecurVec_def]
		 	 >> `0 = length (Vector [])`
		 	 		by metis_tac[length_def,LENGTH_NIL]
		 	 >> simp[])
		 >- (`DROP i slst = []`
		 		by fs[]
		 	>> rw[]
		 	>> `bmRecur plst patTabLst (toList all_chars) [] = 0`
		 			by (Cases_on `plst`
		 				>> fs[bmRecur_def])
		 	>> simp[]
		 	>> ONCE_REWRITE_TAC[bmRecurVec_def]
		 	>> `i >= LENGTH slst`
		 			suffices_by rw[length_def]
		 	>> metis_tac[DROP_NIL]))
	);


(* Calculates lookup table and all_chars to call bmRecur for the first time.
   That is: this implements the boyer-moore substring search algorithm to look
   for the first appearance of a substring in a string *)
val bmSearchVec_def =
    Define
    `
    bmSearchVec pat search =
        let
            all_chars = uniqueElemsVec search
        in
            bmRecurVec pat (mTabVec pat all_chars) all_chars search 0
    `;

val BMSEARCH_VEC_COR_THM = store_thm(
    "BMSEARCH_VEC_COR_THM",
    ``
	bmSearchVec pat search = bmSearch (toList pat) (toList search)
	``,
	rw[bmSearchVec_def, bmSearch_def]
	>> qabbrev_tac `patTabVec = mTabVec pat (uniqueElemsVec search)`
	>> qabbrev_tac `patTabLst = mTab (toList pat) (uniqueElems (toList search))`
	>> qabbrev_tac `all_chars = uniqueElemsVec search`
	>> `uniqueElems (toList search) = toList (all_chars)`
			by (qunabbrev_tac `all_chars`
				>> rw[UNIQUE_ELEMS_VEC_COR_THM]
				>> rw[toList_thm])
	>> rw[]
	>> `bmRecurVec pat patTabVec all_chars search 0
		= bmRecur (toList pat) patTabLst (toList all_chars) (DROP 0 (toList search))`
			suffices_by rw[DROP]
	>> `(length pat = length patTabVec) /\ (length patTabVec = LENGTH patTabLst) /\
			(!j. j < length patTabVec ==> (sub patTabVec j = Vector (EL j patTabLst)))`
			suffices_by metis_tac[BMRECUR_VEC_COR_THM]
	>> `length patTabVec = length pat`
			by rw[Abbr `patTabVec`, mTabVec_def,tabulate_def,length_def]
	>> simp[]
	>> rpt STRIP_TAC
	>- (rw[Abbr `patTabLst`, MTAB_DIM]
		>> `? patLst. pat = Vector patLst`
				by rw[vector_nchotomy]
		>> rw[length_def,toList_thm])
	>- (qunabbrev_tac `patTabVec`
		>> qunabbrev_tac `patTabLst`
		>> rw[MTAB_VEC_COR_A_THM])
	);

(* STRING SPECIALISATION *)
(* Generate our fixed char alphabet *)
val alphabetVec_def =
    Define
    `
    alphabetVec = tabulate 256 CHR
    `;

(* Checks to see if pat is prefix of search and skips verified bad alignments
   based on patTab and all_chars if not to recursively find the minimum
   solution. Returning length search indicates no substrings, returning
   length search + 1 indicates there's been an error likely due to a malformed
   patTab *)
val bmRecurVecString_def =
    tDefine "bmRecurVecString"
    `
    bmRecurVecString (pat:char vector) patTab (search:char vector) i =
    	if
    		(length pat = 0) \/
    		(length search - i = 0)
    	then
    		0
    	else
	        if
	            ~(length pat <= length search - i)
	        then
	            (length search - i)
	        else
	            let
	                (j = checkPrefixRLVecShift pat search i)
	            in
	                if
	                    ~(j < length patTab)
	                then
	                    0
	                else
	                    let
	                        a = ORD (sub search (i+j))
	                    in
	                        if
	                            ~(a < length (sub patTab j))
	                        then
	                            (length search - i + 1)
	                        else
	                            let 
	                                (d = sub (sub patTab j) a)
	                            in
	                                if
	                                    ~(0 < d)
	                                then
	                                    (length search - i + 1)
	                                else
	                                    (d + (bmRecurVecString pat patTab
	                                             search (i+d)))
    `
    (WF_REL_TAC `measure (\(_, _, search, i). length search - i)`
    >> rw[DROP]);

val BMRECUR_VEC_STRING_COR_THM = store_thm(
    "BMRECUR_VEC_STRING_COR_THM",
    ``bmRecurVecString pat patTab search i = bmRecurVec pat patTab alphabetVec search i``,
	completeInduct_on `length search - i`
	>> rpt STRIP_TAC
	>> ONCE_REWRITE_TAC[bmRecurVecString_def,bmRecurVec_def]
	>> `! (c:char). findElemVec alphabetVec c = ORD c`
			suffices_by rw[]
	>> STRIP_TAC
	>> `findElem (toList alphabetVec) c = ORD c`
			suffices_by rw[FIND_ELEM_VEC_COR_THM] 
	>> `toList alphabetVec = alphabet`
			suffices_by rw[ALPHABET_FIND_THM]
	>> ONCE_REWRITE_TAC[alphabetVec_def,alphabet_def]
	>> ONCE_REWRITE_TAC[tabulate_def]
	>> ONCE_REWRITE_TAC[toList_thm]
	>> simp[]);

val bmSearchVecString_def =
	Define
	`bmSearchVecString pat search = bmRecurVecString pat (mTabVec pat alphabetVec) search 0`;

val BMSEARCH_VEC_STRING_COR_THM = store_thm(
    "BMSEARCH_VEC_STRING_COR_THM",
    ``bmSearchVecString pat search = bmSearchString (toList pat) (toList search)``,
	rw[bmSearchVecString_def,bmSearchString_def]
	>> rw[BMRECUR_VEC_STRING_COR_THM]
	>> `bmRecurString (toList pat) (mTab (toList pat) alphabet) (toList search)
			= bmRecur (toList pat) (mTab (toList pat) alphabet) alphabet (toList search)`
			by rw[BMRECUR_STRING_THM]
	>> simp[]
	>> `alphabet = toList alphabetVec`
			by (ONCE_REWRITE_TAC[alphabet_def,alphabetVec_def]
				>> ONCE_REWRITE_TAC[tabulate_def]
				>> ONCE_REWRITE_TAC[toList_thm]
				>> simp[])
	>> simp[]
	>> qabbrev_tac `patTabVec = mTabVec pat alphabetVec`
	>> qabbrev_tac `patTabLst = mTab (toList pat) alphabet`
	>> `(length pat = length patTabVec) /\
		(length patTabVec = LENGTH patTabLst) /\
		(!j. j < length patTabVec ==> (sub patTabVec j = Vector (EL j patTabLst)))`
			suffices_by metis_tac[BMRECUR_VEC_COR_THM,DROP]
	>> rpt STRIP_TAC
	>- (qunabbrev_tac `patTabVec`
		>> rw[mTabVec_def]
		>> rw[tabulate_def,length_def,LENGTH_GENLIST])
	>- (qunabbrev_tac `patTabVec`
		>> qunabbrev_tac `patTabLst`
		>> rw[mTabVec_def,mTab_def]
		>> rw[tabulate_def,length_def,LENGTH_GENLIST]
		>> rw[length_toList])
	>- (qunabbrev_tac `patTabVec`
		>> qunabbrev_tac `patTabLst`
		>> `length (mTabVec pat alphabetVec) = length pat`
				suffices_by rw[MTAB_VEC_COR_A_THM]
		>> rw[mTabVec_def]
		>> rw[tabulate_def,length_def,LENGTH_GENLIST]
		>> rw[MTAB_VEC_COR_A_THM])
	);

val _ = export_theory();