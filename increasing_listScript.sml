open HolKernel boolLib bossLib Parse;

open listTheory;
open rich_listTheory;
open prim_recTheory;
open arithmeticTheory;
open pred_setTheory;
open pairTheory;
open boolTheory;

val _ = new_theory"increasing_list";

(* A definition of increasing lists *)
val increasing_def = 
    Define
    `
    (increasing (x::y::rst) = ((x <= y) /\ (increasing (y::rst))))
    /\ (increasing (x::[]) = T)
    /\ (increasing ([]) = F)
    `;

(* LEMMA ABOUT SUBLISTS OF INCREASING LISTS*)
val INCREASING_SUBLIST = store_thm(
	"INCREASING_SUBLIST",
	``!x y. (increasing (x::y)) /\ (y <> []) ==>
                                       increasing y``,	
  rw[increasing_def]
  >> Cases_on `y`
  >> fs[increasing_def]
  );

(* LEMMA ABOUT SNOCING ON TO END OF INCREASING LIST *)
val SNOC_LEMMA = store_thm(
	"SNOC_LEMMA",
	``!l x. ((increasing l) \/ (l = [])) /\ (!e. MEM e l ==> e <= x)
                              ==> increasing (SNOC x l)``,	
  Induct_on `l`
  (* handles base and reduces inductive *)
  >> rw[increasing_def]
  >> Cases_on `l`
  (* handles one case and reduces other *)
  >> rw[increasing_def]
  (* g1 *)
  >- fs[increasing_def]
  (* g2 *)
  >- (first_x_assum irule
      >> rpt conj_tac
      (* subgoal a*)
      >-(fs[]>> metis_tac[])
      (* subgoal b *)
      >-(fs[increasing_def]))
  );

(* LEMMA ABOUT GENLIST BEING INCREASING *)
val GENLIST_SUC_INC = store_thm(
	"GENLIST_SUC_INC",
	``!x. x > 0 ==> increasing (GENLIST SUC x)``,	
  Induct_on `x`
  >-fs[]
  >-(rw[GENLIST,increasing_def]
     >> irule SNOC_LEMMA
     >> rpt conj_tac
      >-rw[MEM_GENLIST]
      >-(Cases_on `x` >> rw[]))
  );


(* LEMMA WITH ALTERNATIVE CHARACTERISATION OF INCREASING*)
val INC_CONS_THM = store_thm(
	"INC_CONS_THM",
	``!h. increasing (h::t) =
                              (t=[]) \/ ((!e. MEM e t ==> h <= e)
                                         /\ (increasing t))``,	

                        Induct_on `t`
                        >> rw[increasing_def]
                        >> eq_tac
                        >> rw []
                        >- rw[]
                        >- fs[]
                        >- rw[]
                        >- metis_tac[arithmeticTheory.LESS_EQ_TRANS]
    );

(* FILTER either produces empty list or preserves increasing *)
val FILTER_INC_PRES = store_thm(
	"FILTER_INC_PRES",
	``!f l. increasing l
                                   ==> (increasing (FILTER f l))
                                       \/ ((FILTER f l) = [])``,	
                            Induct_on `l`
                            >> rw[INC_CONS_THM]
                            >> rw[listTheory.MEM_FILTER]
                            >> metis_tac[]
    );                      

(* HEAD OF INCREASING LIST IS THE MINIMUM *)
val HEAD_INC_MIN = store_thm(
	"HEAD_INC_MIN",
	``! l. increasing l ==> (HD l = MIN_SET (set l))``,	
                          Induct_on `l`>> rw[increasing_def, INC_CONS_THM]
                          >- rw[pred_setTheory.MIN_SET_THM]
                          >- (irule arithmeticTheory.LESS_EQUAL_ANTISYM
                              >> rpt conj_tac
                              >- rw[pred_setTheory.MIN_SET_LEM]
                              >- (`MIN_SET (h INSERT set l) IN h INSERT set l`
                                  by simp[pred_setTheory.MIN_SET_LEM]
                                  >> fs[]
                                 )
                            )
    );

val _ = export_theory();