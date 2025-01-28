(*********************************************************)
(********************** Fiche 2 **************************)
(*********************************************************)

Require Import untypedLC.

(* 
!!! Important : on cherchera toujours le codage des fonctions
                 sur papier avant de les coder dans Coq comme des lexp.
*)

(*********************************************************)
(**** I - Codage des booléens et de la conditionnelle ****)
(*********************************************************)
(*
Exercice 1 - Coder dans Coq les booléens et la conditionnelle comme des lexp.
*)

Definition ctr := \x y·x.
Definition cfa := \x y·y.
Definition cif := \b m n· b m n.

(*
Exercice 2 - Vérifier (en utilisant red cbn ou show cbn) que l’application de 
             cif à vrai (ctr) et à faux (cfa) s’évalue correctement.
*)

Compute equiv_lexp (cif ctr x y) x. (* true *)
Compute equiv_lexp (cif ctr x y) y. (* false *)
Compute equiv_lexp (cif cfa x y) y. (* true *)
Compute equiv_lexp (cif cfa x y) x. (* false *)

(*********************************************************)
(********** II - Codage des opérateurs booléens **********)
(*********************************************************)
(*
Exercice 1 -  Coder dans Coq la version factorisée des opérateurs 
              and, or et not comme des lexp
*)

Definition cand :=  \a b x y·a (b x y) y.

Definition cor  :=  \a b·\x y·a x (b x y).

Definition cnot :=  \b~\x y~b y x.
(*
Exercice 2 - Vérifier avec red_cbn ou show_cbn les tables de vérité de ces trois opérateurs
*)

Compute equiv_lexp ( cand ctr ctr ) ctr.
Compute equiv_lexp ( cand cfa ctr ) cfa.
Compute equiv_lexp ( cand ctr cfa ) cfa.
Compute equiv_lexp ( cand cfa cfa ) cfa.
Compute equiv_lexp ( cor ctr ctr ) ctr.
Compute equiv_lexp ( cor cfa ctr ) ctr.
Compute equiv_lexp ( cor ctr cfa ) ctr.
Compute equiv_lexp ( cor cfa cfa ) cfa.

(* Bonus *)
(* A COMPLETER *)

(*********************************************************)
(**************** III - Codage des entiers ***************)
(*********************************************************)
(*
Exercice 1 - Coder dans Coq comme des lexp les 4 premiers entiers c0, c1, c2 et c3.
*)
Definition c0 := \f x~x.
Definition c1 := \f x~f x.
Definition c2 := \f x~f (f x).
Definition c3 := \f x~f (f (f x)).

(*
Exercice 2 - Coder dans Coq la fonction successeur d’un entier de Church comme une lexp 
             et la tester sur quelques exemples.
*)

Definition csucc := \n~\f x~f (n f x).

Compute equiv_lexp (csucc c2) c3.
Compute equiv_lexp (csucc c1) c2.
Compute equiv_lexp (csucc c0) c1.


(*********************************************************)
(************* IV - Opérations sur les entiers ***********)
(*********************************************************)
(*
Exercice 1 -  Coder dans Coq la fonction addition de deux entiers de Church comme une lexp,
              et la tester sur quelques exemples.
*)

Definition cadd := \n m~\f x~n f (m f x).

Definition c4 := csucc c3.
Definition c5 := csucc c4.
Definition c6 := csucc c5.
Definition c7 := csucc c6.
Compute equiv_lexp ( cadd c0 c1 ) c1.
Compute equiv_lexp ( cadd c1 c2 ) c3.
Compute equiv_lexp ( cadd c2 c3 ) c5.
Compute equiv_lexp ( cadd c3 c4 ) c7.
Compute equiv_lexp ( cadd c3 c3 ) c5.


(*
Exercice 2 -  Faire la même chose avec la multiplication de deux entiers de Church.
*)

Definition cmult := \n m~\f~n (m f).

Definition c8 := csucc c7.
Definition c9 := csucc c8.
Compute equiv_lexp ( cmult c2 c1 ) c2.
Compute equiv_lexp ( cmult c1 c0 ) c0.
Compute equiv_lexp ( cmult c2 c3 ) c6.
Compute equiv_lexp ( cmult c3 c3 ) c9.


(*
Exercice 3 -  Tester cadd et cmult sur des booléens. Les résultats ont-ils du sens ?
*)

Compute red_cbn ( cadd ctr cfa ).
Compute red_cbn ( cmult ctr ctr ).

(* Non *)

(* Bonus *)
(* A COMPLETER *)

(*********************************************************)
(************** V - Opérateurs de comparaison ************)
(*********************************************************)
(*
Exercice 1 - Coder dans Coq comme une lexp le test à zéro d'un entier de Church.
*)

Definition ceq0 := \n~\x y~n (\z~y) x.

(* 
   La tester sur quelques exemples dont c0. 
*)

Compute equiv_lexp ( ceq0 c2 ) cfa.
Compute equiv_lexp ( ceq0 c0 ) ctr.


(*********************************************************)
(******** V - Structures de données - les couples ********)
(*********************************************************)
(*
Exercice 1 - Coder dans Coq la fonction cpl rendant un couple formé de ses deux 
             arguments.
*)

Definition cpl   := \x1 x2~\k~k x1 x2.

(* 
   S'en servir pour définir le couple (false, true). 
*)

Definition cplft := cpl cfa ctr.
Compute red_cbn cplft.

(*
Exercice 2 - Coder dans Coq les fonctions fst et snd qui retournent respectivement
             le premier et le deuxième élément d’un couple.
             Tester sur le couple cplft.
*)

Definition fst := \c~c ctr.

Definition snd := \c~c cfa.

(*
   Tester sur le couple cplft.
*)

Compute equiv_lexp ( fst cplft ) cfa.
Compute equiv_lexp ( snd cplft ) ctr.


(*
Exercice 3 - Coder dans Coq la fonction cpland prenant en argument un couple de  booléens
             et rendant en résultat la conjonction de ses deux composantes.
*)

Definition cpland := \c~cand (fst c) (snd c).

Definition cpltt := cpl ctr ctr.
Definition cpltf := cpl ctr cfa.
Definition cplff := cpl cfa cfa.

(*
Tester cpland sur les couples (false,true) et (true,true) .
*)
Compute equiv_lexp ( cpland cplft ) cfa.
Compute equiv_lexp ( cpland cpltt ) ctr.
Compute equiv_lexp ( cpland cpltf ) cfa.
Compute equiv_lexp ( cpland cplff ) cfa.


(*********************************************************)
(************** VI - Codage du prédécesseur **************)
(*********************************************************)
(*
Exercice 1 - Coder dans Coq la fonction iter qui prend un entier de Church n, une
             fonction g et un argument x et qui applique n fois la fonction g sur x. 
*)

Definition iter := \n g x~n g x.

(* La tester avec c4, la fonction csucc et c0. *)

Compute equiv_lexp ( iter c0 csucc c0 ) c0.
Compute equiv_lexp ( iter c4 csucc c0 ) c4.

(*
Exercice 2 - Coder dans Coq la fonction cpred1 qui à partir d’un couple (x,y)
             donné en argument rend le couple (y,y+1). 
*)

Definition cpred1 := \c~\k~k (snd c) (csucc (snd c)).

(*
Tester cpred1 sur le codage du couple (1,2).
*)

Definition cpl12 := cpl c1 c2.
Compute equiv_lexp ( cpred1 cpl12 ) (cpl c2 c3).


(*
Exercice 3 - Coder dans Coq le prédécesseur d’un entier de Church
*)
Definition cpl00 := cpl c0 c0.
Definition cpred := \n~fst (iter n cpred1 cpl00).
Definition cpred_simple := \n~fst (iter n cpred1 cpl00).
(*
Tester sur quelques exemples dont c0.
*)
Compute red_cbn (cpred c1).

Compute equiv_lexp ( cpred c2 ) c1.
Compute ( ... )
...

(*********************************************************)
(************ VII - Combinateur de point fixe ************)
(*********************************************************)
(*
Exercice 2 - Définir dans Coq  Y comme une lexp
*)

Definition Y := ...

(* 
   On peut vérifier ici que les deux exemples trouvés à l'exercice précédent
   ont ou n'ont pas de forme normale 
*)

Compute (Y ... )
Compute (Y ... )
...

(*********************************************************)
(******* VII - Codage de définitions récursives  *********)
(*********************************************************)
(*
Exercice 1 - En utilisant les opérateurs définis précédemment (cif, ceq0, cmult, cpred), 
             définir dans Coq la fonctionnelle associée à fact.
*)

Definition cfonc := \f n· ...

(*
Exercice 2 - Définir la fonction factorielle dans Coq comme une lexp.
*)

Definition cfact := ...

(*
   La tester avec red_cbn sur de tout petits entiers (< 4).
*)

Compute ( ... )
Compute ( ... )
...

(* 
   S'il vous reste du temps vous pouvez traiter les exercices optionnels 
*)
