Require Import untypedLC.

Definition App := \x~\y~x y.

(*** EXERCICES ***)

(* 1 Verif vlibre et vliees l'exp4 *)

Definition exp41 := \x~x y.

Print exp41.
Compute (vlibres exp41).
Compute (vliees exp41).

Definition exp42 := \v x y~u v y.

Print exp42.
Compute (vlibres exp42).
Compute (vliees exp42).

Definition exp43 := \x~x (\y~y x).

Print exp43.
Compute (vlibres exp43).
Compute (vliees exp43).

Definition exp44 := (\x y z~x z (y z)) u x w.

Print exp44.
Compute (vlibres exp44).
Compute (vliees exp44).

(* 2 Verif redex show cbn *)

Definition exp51 := (\x~x ((\y~y)x)) (\z~a).

Print exp51.
Compute(show_cbn exp51).

Definition exp52 := (\x~x x x) (\z~a).

Print exp52.
Compute(show_cbn exp52).

Definition exp53 := (\y~x) ((\x~x x)(\x~x x)).

Print exp53.
Compute(show_cbn exp53).

(* 3 show cbv et show cbn exp 6*)
Definition exp61 := (\x~x x) ((\y~x)(\y~x)).

Compute(show_cbn exp61).
Compute(show_cbv exp61).

Definition exp62 := (\y~x) ((\y~x)(\y~x)).

Compute(show_cbn exp62).
Compute(show_cbv exp62).

Definition exp63 := (\y~x) ((\x~x x)(\x~x x)).

Compute(show_cbn exp63).
Compute(show_cbv exp63).

(* 4 Verif exp8 *)
Definition exp81 := (\x~x x) ((\z~x)(\z~x)).
Definition exp82 := (\x~x y) (\a b~z).
Definition exp83 := (\y~z).
Definition exp84 := (\a~a a) x.
Definition exp85 := (\a b~x) y.
Definition exp86 := (\x~x x) ((\z~a)(\z~a)).

Compute(equiv_lexp exp81 exp82).
Compute(equiv_lexp exp81 exp83).
Compute(equiv_lexp exp81 exp84).
Compute(equiv_lexp exp81 exp85).
Compute(equiv_lexp exp81 exp86).

Compute(equiv_lexp exp82 exp83).
Compute(equiv_lexp exp82 exp84).
Compute(equiv_lexp exp82 exp85).
Compute(equiv_lexp exp82 exp86).

Compute(equiv_lexp exp83 exp84).
Compute(equiv_lexp exp83 exp85).
Compute(equiv_lexp exp83 exp86).

Compute(equiv_lexp exp84 exp85).
Compute(equiv_lexp exp84 exp86).
Compute(show_cbv exp84).

Compute(equiv_lexp exp85 exp86).
Compute(show_cbv exp86).


(* 5 Observer *)
Definition exp7 := (\x~(\y~x)z) y.
Compute(show_cbv exp7).
Compute(show_cbn exp7).

(* 6 *)
Definition exp9 := (\x~x x)(\x~x x)(\x~x). 
Compute(fnorm exp9).



