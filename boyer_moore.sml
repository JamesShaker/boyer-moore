open listTheory;
open rich_listTheory;
open prim_recTheory;
open arithmeticTheory;
open pred_setTheory;
open pairTheory;
open boolTheory;

load "../../boyer-moore-hol/final_source/increasing_listTheory";
open increasing_listTheory;
load "../../boyer-moore-hol/final_source/helper_funcsTheory";
open helper_funcsTheory;
load "../../boyer-moore-hol/final_source/boyer_moore_specTheory";
open boyer_moore_specTheory;

(* -- IMPLICIT CHARACTER MISMATCH TABLE CONSTRUCTION -- *)
(* Assess potential shift based on character mismatch rule *)
val checkDeltaC_def =
    Define
    `
    checkDeltaC pat all_chars j a d =
        (d = j+1) \/ (EL (j-d) pat = EL a all_chars)
    `;

(* Relationship between checkDeltaC function
   and valid_cha_shift specification *)
val CHECK_DELTAC_THM=Q.prove(
    `!pat all_chars j a d . d IN valid_cha_shifts pat all_chars j a
                 <=> (1 <= d /\ d <= j+1 /\ checkDeltaC pat all_chars j a d)`,
    rw[valid_cha_shifts_def,checkDeltaC_def]
    >> Cases_on `d=j+1`
    >- simp[]
    >- (`(d <= j) <=> (d <= j + 1)`
            suffices_by metis_tac[]
        >> simp[])
    );

(* Check Delta C in terms of set comprehensions *)
val CHECK_DELTAC_SET = Q.prove(
    `valid_cha_shifts pat all_chars j a = {d | 1 <= d /\ d <= j+1
                        /\ checkDeltaC pat all_chars j a d}`,
    rw [CHECK_DELTAC_THM, EXTENSION]
    );

(* Find minimum valid character mismatch based shift *)
val cmRecur_def =
    Hol_defn "cmRecur"
    `
    cmRecur pat all_chars j a d =
        if (j+1 < d) then d
        else if (checkDeltaC pat all_chars j a d) then d
        else (cmRecur pat all_chars j a (d+1))
    `;
Defn.tgoal cmRecur_def;
e(WF_REL_TAC `measure (\x. (SUC ∘ FST ∘ SND ∘ SND) x - (SND ∘ SND ∘ SND ∘ SND) x)`);
e(fs[ADD1,checkDeltaC_def]);


val cmVal_def =
    Define
    `
    cmVal pat all_chars j a = cmRecur pat all_chars j a 1
    `;

(* Relationship between cmVal function and valid_cha_shift specification *)
g `(x < MIN_SET (valid_cha_shifts pat all_chars j a)) ==> (cmRecur pat all_chars j a x = MIN_SET (valid_cha_shifts pat all_chars j a))`;
e(fs[]);

g `cmVal pat all_chars j a = MIN_SET (valid_cha_shifts pat all_chars j a)`;
e(simp[cmVal_def]);
e(Induct_on `d`)

val CMVAL_THM = Q.prove(
    `cmVal pat all_chars j a = MIN_SET (valid_cha_shifts pat all_chars j a)`,
    simp[cmVal_def]
    >> `valid_cha_shifts pat all_chars j a =
        set (FILTER (checkDeltaC pat all_chars j a) (GENLIST SUC (j+1)))`
            by (rw[CHECK_DELTAC_SET,EXTENSION,MEM_FILTER,MEM_GENLIST]
                >> rw[EQ_IMP_THM] >> Cases_on `x` >> fs[])
    >> `valid_cha_shifts pat all_chars j a <> {}`
            by rw[CHA_SHIFT_EXISTS_THM]
    >> `FILTER (checkDeltaC pat all_chars j a) (GENLIST SUC (j+1)) <> []`
            by (CCONTR_TAC >> fs[])
    >> `increasing (GENLIST SUC (j+1))`
            by (irule GENLIST_SUC_INC >> fs[])
    >> `increasing (FILTER (checkDeltaC pat all_chars j a) (GENLIST SUC (j+1)))`
            by (drule FILTER_INC_PRES >> metis_tac[])
    >> fs[]
    >> irule HEAD_INC_MIN
    >> fs[]
    );

(* Proving bounds on cmVal function with valid input *)
val CMVAL_BND = Q.prove(
    `!j a. j < LENGTH pat ∧ a < LENGTH all_chars
           ==> 0 < cmVal pat all_char j a
               /\ cmVal pat all_char j a <= LENGTH pat`,
    simp[CMVAL_THM]
    >> REPEAT strip_tac
    >- (`0 <> MIN_SET (valid_cha_shifts pat all_char j a)`
            suffices_by rw[]
        >> `~(0 IN valid_cha_shifts pat all_char j a)`
            suffices_by metis_tac[CHA_SHIFT_EXISTS_THM,MIN_SET_LEM]
        >> simp[valid_cha_shifts_def])
    >- (`?x. (x IN valid_cha_shifts pat all_char j a) /\ (x <= LENGTH pat)`
            suffices_by metis_tac[MIN_SET_LEM, LESS_EQ_TRANS, MEMBER_NOT_EMPTY]
        >> simp[valid_cha_shifts_def]
        >> qexists_tac `j+1`
        >> simp[])        
    );

(* -- IMPLICIT SUFFIX MATCH TABLE CONSTRUCTION -- *)
(* Assess potential shift based on suffix mismatch rule *)
val checkDeltaS_def =
    Define
    `
    checkDeltaS pat j d = 
        ((d >= SUC j) \/ ~(EL (j-d) pat = EL j pat)) /\
        (extract (MAX (SUC j) d,LENGTH pat) pat
            = extract ((MAX (SUC j) d) - d,LENGTH pat - d) pat)
    `;

(* Relationship between checkDeltaS function
   and valid_suf_shift specification *)
val CHECK_DELTAS_THM=Q.prove(
    `! pat j d . d IN valid_suf_shifts pat j
                 <=> 1 <= d /\ d <= LENGTH pat /\ checkDeltaS pat j d`,
    ONCE_REWRITE_TAC [EQ_SYM_EQ]
    >> simp[valid_suf_shifts_def,checkDeltaS_def,EXTRACT_THM,LIST_EQ_REWRITE]
    >> rw[EQ_IMP_THM]
    >> simp[]
    >- (`MAX (SUC j) d = d`
            by simp[MAX_DEF]
        >> fs[]
        >> first_x_assum(qspec_then `i-d` mp_tac)
        >> simp[])
    >- (qabbrev_tac `M = MAX (SUC j) d`
        >> `d <= M`
                by rw[MAX_DEF,Abbr `M`]
        >> Q.UNDISCH_THEN `d<= LENGTH pat` assume_tac
        >> fs[]
        >> first_x_assum(qspec_then `i-M` mp_tac)
        >> simp[]
        >> `M <= i`
                by simp[MAX_DEF, Abbr `M`]
        >> simp[])
    >- (simp[MAX_DEF])
    >- (qabbrev_tac `M = MAX (SUC j) d`
        >> `d <= M`
                by rw[MAX_DEF,Abbr `M`]
        >> simp[])
    >- (simp[MAX_DEF])
    >- (qabbrev_tac `M = MAX (SUC j) d`
        >> `d <= M`
                by rw[MAX_DEF,Abbr `M`]
        >> simp[]
        >> `(j + 1) <= (M + x)`
                by rw[MAX_DEF,Abbr `M`]
        >> `d <= (M + x)`
                by rw[MAX_DEF,Abbr `M`]
        >> first_x_assum(qspec_then `M + x` mp_tac)
        >> simp[])
    );

(* Check Delta S in terms of set comprehensions *)
val CHECK_DELTAS_SET = Q.prove(
    `valid_suf_shifts pat j = { d | 1 <= d
                                    /\ d <= LENGTH pat
                                    /\ checkDeltaS pat j d}`,
    rw [CHECK_DELTAS_THM, EXTENSION]
    );


(* Find minimum valid suffix mismatch based shift *)
val smRecur_def =
    Define
    `
    smRecur pat j d =
        if (checkDeltaS pat j d) then d
        else (smRecur pat j (d+1))
    `;

val smVal_def =
    Define
    `
    smVal pat j = smRecur pat j 1
    `;

(* Relationship between smVal function and valid_suf_shift specification *)
val SMVAL_THM = Q.prove(
    `(pat <> []) /\ (j < LENGTH pat)
     ==> (smVal pat j = MIN_SET (valid_suf_shifts pat j))`,
    strip_tac
    >> `valid_suf_shifts pat j <> {}`
            by rw [SUF_SHIFT_EXISTS_THM]
    >> simp[smVal_def]
    >> `valid_suf_shifts pat j =
        set (FILTER (checkDeltaS pat j) (GENLIST SUC (LENGTH pat)))`
            by (rw[CHECK_DELTAS_SET,EXTENSION,MEM_FILTER,MEM_GENLIST]
                >> rw[EQ_IMP_THM] >> Cases_on `x` >> fs[])
       
    >> fs[]
    >> irule HEAD_INC_MIN
    >> `increasing (GENLIST SUC (LENGTH pat))`
            by (irule GENLIST_SUC_INC >> Cases_on `pat` >> fs[])
    >> `increasing (FILTER (checkDeltaS pat j) (GENLIST SUC (LENGTH pat)))`
            by (drule FILTER_INC_PRES >> metis_tac[])
    );

(* Proving bounds on smVal function with valid input *)
val SMVAL_BND = Q.prove(
    `!j . j < LENGTH pat
            ==> 0 < smVal pat j
                /\ smVal pat j <= LENGTH pat`,
    Cases_on `pat = []`
    >- simp[LENGTH]
    >- (simp[SMVAL_THM]
        >> REPEAT strip_tac
        >- (`0 <> MIN_SET (valid_suf_shifts pat j)`
                    suffices_by rw[]
            >> `~(0 IN valid_suf_shifts pat j)`
                    suffices_by metis_tac[SUF_SHIFT_EXISTS_THM,MIN_SET_LEM]
            >> simp[valid_suf_shifts_def])
        >- (`?x. (x IN valid_suf_shifts pat j) /\ (x <= LENGTH pat)`
                suffices_by metis_tac[MIN_SET_LEM, LESS_EQ_TRANS,
                                      MEMBER_NOT_EMPTY]
            >> simp[valid_suf_shifts_def]
            >> qexists_tac `LENGTH pat`
            >> simp[])
        )         
    );


(* -- ACTUAL MISMATCH TABLE CONSTRUCTION --  *)
(* Find mismatch table value at particular point based
   on best shift available between suffix mismatch table
   and character mismatch table *)
val mVal_def =
    Define
    `
    mVal calc_smVal pat all_chars j a =
        MAX calc_smVal (cmVal pat all_chars j a)
    `;

(* Generate a row of mismatch table *)
val mSubTab_def =
    Define
    `
    mSubTab pat all_chars j =
        GENLIST (mVal (smVal pat j) pat all_chars j) (LENGTH all_chars)
    `;

(* Generate mismatch table *)
val mTab_def =
    Define
    `
    mTab pat all_chars =
        GENLIST (mSubTab pat all_chars) (LENGTH pat)
    `;

(* Dimensional properties of mTab *)
val MTAB_DIM = Q.prove(
    `(LENGTH (mTab pat all_chars) = LENGTH pat)
     /\ (!j. j < LENGTH pat
             ==> (LENGTH (EL j (mTab pat all_chars))
                  = LENGTH all_chars))`,
    simp[mTab_def,mSubTab_def]
    );

(* Bounds on mTab values for valid inputs *)
val MTAB_BND = Q.prove(
    `!a j.  (j < LENGTH pat) /\ (a < LENGTH all_chars)
            ==> 0 < EL a (EL j (mTab pat all_chars))
                /\ EL a (EL j (mTab pat all_chars)) <= LENGTH pat`,
    simp[mTab_def,mSubTab_def,mVal_def]
    >> metis_tac[SMVAL_BND,CMVAL_BND]
    );

(* Important solution skipping capacity of mTab *)
val MTAB_THM = Q.prove(
    `!search j k a. ((pat <> [])
      /\ (k <= LENGTH search - LENGTH pat)
      /\ (j < LENGTH pat)
      /\ (!i. (j<i /\ i < LENGTH pat)
              ==> (EL i pat = EL (k+i) search))
      /\ (EL j pat <> EL (k+j) search)
      /\ (a < LENGTH all_chars)
      /\ (EL (k+j) search = EL a all_chars))
      ==>(!d. d < (EL a (EL j (mTab pat all_chars)))
              ==> ~((k+d) IN solutions pat search))`,
    strip_tac
    >> strip_tac
    >> strip_tac
    >> strip_tac
    >> strip_tac
    >> `(EL a (EL j (mTab pat all_chars)) = (smVal pat j)) \/ 
        (EL a (EL j (mTab pat all_chars)) = (cmVal pat all_chars j a))`
            by rw[mTab_def,mSubTab_def,mVal_def,EL_GENLIST,MAX_DEF]
    >- (fs[]
        >> fs[SMVAL_THM]
        >> `EL j pat <> EL (k+j) search`
                by rw[EQ_SYM_EQ]
        >> drule SUF_SKIP_NOT_SOL
        >> fs[])
    >- (fs[]
        >> fs[CMVAL_THM]
        >> `EL j pat <> EL (k+j) search`
                by rw[EQ_SYM_EQ]
        >> drule CHA_SKIP_NOT_SOL
        >> fs[])
    );



(* -- BOYER-MOORE SEARCH IMPLEMENTATION -- *)
(* Checks to see if pat is prefix of search and skips verified bad alignments
   based on patTab and all_chars if not to recursively find the minimum
   solution. Returning LENGTH search indicates no substrings, returning
   LENGTH search + 1 indicates there's been an error likely due to a malformed
   patTab *)
val bmRecur_def =
    tDefine "bmRecur"
    `
    (bmRecur [] _ _ _ = 0) /\
    (bmRecur _ _ _ [] = 0) /\
    (bmRecur pat patTab all_chars search =
        if
            ~(LENGTH pat <= LENGTH search)
        then
            (LENGTH search)
        else
            let
                (j = checkPrefixRL pat search)
            in
                if
                    ~(j < LENGTH patTab)
                then
                    0
                else
                    let
                        (a = findElem all_chars (EL j search))
                    in
                        if
                            ~(a < LENGTH (EL j patTab))
                        then
                            (LENGTH search + 1)
                        else
                            let 
                                (d = EL a (EL j patTab))
                            in
                                if
                                    ~(0 < d)
                                then
                                    (LENGTH search + 1)
                                else
                                    (d + (bmRecur pat patTab
                                            all_chars (DROP d search)))
    )
    `
    (WF_REL_TAC `measure (LENGTH ∘ SND ∘ SND ∘ SND)`
    >> rw[DROP]);

(* Simple theorem for cleaness enforcing one definition
   of bmRecur for non-null lists *)
val BMRECUR_NON_EMPTY_DEF = Q.prove(
    `(pat <> []) /\ (search <> [])
    ==>
    (bmRecur pat patTab all_chars search =
     if ¬(LENGTH pat ≤ LENGTH search) then LENGTH search
     else
       (let
          j = checkPrefixRL pat search
        in
          if ¬(j < LENGTH patTab) then 0
          else
            (let
               a = findElem all_chars (EL j search)
             in
               if ¬(a < LENGTH (EL j patTab)) then LENGTH search + 1
               else
                 (let
                    d = EL a (EL j patTab)
                  in
                    if ¬(0 < d) then LENGTH search + 1
                    else
                      d +
                      bmRecur pat patTab all_chars
                        (DROP d search))))
    )`,
    Cases_on `pat`
    >> Cases_on `search`
    >> fs[bmRecur_def]
    );

(* Proves that bmRecur returns correct solutions with valid inputs
   for patTab and all_chars *)
val BMRECUR_THM = Q.prove(
    `(LENGTH patTab = LENGTH pat)
     /\ (!j. j < LENGTH pat
             ==> (LENGTH (EL j patTab) = LENGTH all_chars))
     /\ (!a j. j < LENGTH pat /\ a < LENGTH all_chars
               ==> 0 < EL a (EL j patTab)
                   /\ EL a (EL j patTab) <= LENGTH pat)
     /\ (!search j k a. (pat <> [])
                         /\ k <= LENGTH search - LENGTH pat
                         /\ j < LENGTH pat
                         /\ (!i. j < i /\ i < LENGTH pat
                                 ==> (EL i pat = EL (k+i) search))
                         /\ (EL j pat <> EL (k+j) search)
                         /\ a < LENGTH all_chars
                         /\ (EL (k+j) search = EL a all_chars)
                         ==> !d. d < EL a (EL j patTab)
                                 ==> ~((k+d) IN solutions pat search))   
     ==> (!j. j < LENGTH search ==> MEM (EL j search) all_chars)
         ==> (bmRecur pat patTab all_chars search = solution pat search)`,
    strip_tac
    >> completeInduct_on `LENGTH search`
    >> fs[PULL_FORALL]
    >> rw[]
    >> Cases_on `pat =[]`
    >- (fs[bmRecur_def,solution_def,solutions_def]
        >> rw[IN_INSERT, MIN_SET_LEM,DECIDE ``(a <= 0) ==> (a = 0)``])
    >- (Cases_on `search = []`
        >- (Cases_on `pat`
            >> fs[bmRecur_def,solution_def,solutions_def,MIN_SET_THM])
        >- (rw[BMRECUR_NON_EMPTY_DEF]
            >> qabbrev_tac `j_i = checkPrefixRL pat search`
            >> qabbrev_tac `a_i = findElem all_chars (EL j_i search)`
            >> qabbrev_tac `d_i = EL a_i (EL j_i patTab)`
            >- (rename [`~(LENGTH pat <= LENGTH search)`]
                >> rw[solution_def,solutions_def,MIN_SET_THM])
            >- (rename [`~(j_i < LENGTH pat)`]
                >> `j_i <= LENGTH pat`
                        by rw[Abbr `j_i`, CHECK_PREFIX_RL_BND]
                >> `pat = TAKE (LENGTH pat) search`
                        by metis_tac[DECIDE ``(x<=y) /\ ~(x<y) ==> (x=y)``,
                                     CHECK_PREFIX_RL_MATCH]
                >> pop_assum mp_tac
                >> simp[LIST_EQ_REWRITE,EL_TAKE]
                >> strip_tac
                >> simp[solution_def]
                >> `0 IN solutions pat search`
                        suffices_by metis_tac[DECIDE ``(a <= 0) ==> (a=0)``,
                                              MEMBER_NOT_EMPTY, MIN_SET_LEM,
                                              IN_INSERT]
                >> simp[solutions_def])
            >- (rename [`~(a_i < LENGTH all_chars)`]
                >> `MEM (EL j_i search) all_chars`
                        by rw[]
                >> `a_i = LENGTH all_chars`
                        by rw[Abbr `a_i`,
                              DECIDE ``(x<=y) /\ ~(x<y) ==> (x=y)``,
                              FIND_ELEM_BND]
                >> metis_tac[FIND_ELEM_NO_MATCH])
            >- (rename [`d_i = 0`]
                >> `0 < d_i`
                        by rw[Abbr `d_i`]
                >> fs[])
            >- (rename [`d_i <> 0`]
                >> `bmRecur pat patTab all_chars (DROP d_i search)
                    = solution pat (DROP d_i search)`
                        by fs[LENGTH_DROP,EL_DROP]
                >> simp[]
                >> `(LENGTH pat <= LENGTH search) /\ (d_i <= LENGTH search)
                    /\ (!x. x < d_i ==> ~(x IN solutions pat search))`
                        suffices_by metis_tac[SOL_SHF_THM]
                >> simp[]
                >> strip_tac
                >- (first_x_assum (qspecl_then [`a_i`,`j_i`] mp_tac)
                    >> fs[LESS_EQ_TRANS])
                >- (strip_tac
                    >> first_x_assum (qspecl_then [`search`,`j_i`,`0`,`a_i`,`x`]
                                                  mp_tac)
                    >> fs[Abbr `a_i`, Abbr `j_i`,Abbr `d_i`,
                          CHECK_PREFIX_RL_THM,FIND_ELEM_THM])
                )
            )
        )
    );

(* Calculates lookup table and all_chars to call bmRecur for the first time.
   That is: this implements the boyer-moore substring search algorithm to look
   for the first appearance of a substring in a string *)
val bmSearch_def =
    Define
    `
    bmSearch pat search =
        let
            all_chars = uniqueElems search
        in
            bmRecur pat (mTab pat all_chars) all_chars search
    `;

(* Final proof that the bmSearch function correctly searches
   for the first substring *)
val BMSEARCH_THM = Q.prove(
    `bmSearch pat search = solution pat search`,
    simp[bmSearch_def]
    >> irule BMRECUR_THM
    >- metis_tac [MTAB_THM]
    >- rw [MTAB_BND]
    >- rw [MTAB_DIM]
    >- rw [UNIQUE_ELEMS_THM]
    >- rw [MTAB_DIM]   
    );