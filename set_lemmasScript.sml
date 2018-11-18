open HolKernel boolLib bossLib Parse;

open listTheory;
open rich_listTheory;
open prim_recTheory;
open arithmeticTheory;
open pred_setTheory;
open pairTheory;
open boolTheory;


val _ = new_theory"set_lemmas";

(* Upper bound on members of set puts upper bound on MIN_SET *)
val MIN_SET_UPPER_BOUND = store_thm(
    "MIN_SET_UPPER_BOUND",
    ``(s <> {}) /\ (!e. e IN s ==> e <= l) 
     ==> (MIN_SET s <= l)``,
    rw[]
    >> irule LESS_EQ_TRANS
    >> Cases_on `s`
    >> fs[]
    >> qexists_tac `x`
    >> fs[]
    >> metis_tac[MIN_SET_LEM, IN_INSERT, NOT_INSERT_EMPTY]
    );

(* Being less than MIN_SET implies you are less than every element of the set *)
val MIN_SET_IS_LOWER_BOUND = store_thm(
    "MIN_SET_IS_LOWER_BOUND",
    ``(s <> {}) /\ (x < MIN_SET s)
     ==> (!a. a IN s ==> x < a)``,
    DISCH_TAC
    >> rw[]
    >> Cases_on `x < a`
    >> fs[]
    >> `a < MIN_SET s`
            by fs[MIN_SET_LEM]
    >>`MIN_SET s <= a`
            by fs[MIN_SET_LEM]
    >> fs[]
    );

val _ = export_theory();