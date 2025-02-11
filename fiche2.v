
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

(* Format equiv_lexp (expression) output-expectation *)

(* Verifier cif + cond *)
Compute equiv_lexp (cif ctr x y) x. 
Compute equiv_lexp (cif ctr y x) y. 
Compute equiv_lexp (cif cfa x y) y. 
Compute equiv_lexp (cif cfa y x) x. 

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

(* Format equiv_lexp (expression) output-expectation *)
(* Verifier cand par rapport a la table de verite *)
Compute equiv_lexp ( cand ctr ctr ) ctr.
Compute equiv_lexp ( cand cfa ctr ) cfa.
Compute equiv_lexp ( cand ctr cfa ) cfa.
Compute equiv_lexp ( cand cfa cfa ) cfa.

(* Format equiv_lexp (expression) output-expectation *)
(* Verifier cor par rapport a la table de verite *)
Compute equiv_lexp ( cor ctr ctr ) ctr.
Compute equiv_lexp ( cor cfa ctr ) ctr.
Compute equiv_lexp ( cor ctr cfa ) ctr.
Compute equiv_lexp ( cor cfa cfa ) cfa.

(* Bonus *)

(*
Exercice 3- Codage non factorise
*)
Definition cand_nf := \a b~cif a (cif b ctr cfa) cfa. 
Definition cor_nf := \a b~cif a ctr (cif b ctr cfa).
Definition cnot_nf := \a~cif a cfa ctr.

(* 
Exercice 4 - Tester cand_nf, cor_nf, cnot_nf
 *)

(* Verifier cand_nf par rapport a la table de verite *)
Compute equiv_lexp ( cand_nf ctr ctr ) ctr.
Compute equiv_lexp ( cand_nf cfa ctr ) cfa.
Compute equiv_lexp ( cand_nf ctr cfa ) cfa.
Compute equiv_lexp ( cand_nf cfa cfa ) cfa.

(* Verifier cor_nf par rapport a la table de verite *)
Compute equiv_lexp ( cor_nf ctr ctr ) ctr.
Compute equiv_lexp ( cor_nf cfa ctr ) ctr.
Compute equiv_lexp ( cor_nf ctr cfa ) ctr.
Compute equiv_lexp ( cor_nf cfa cfa ) cfa.

(* Verifier cnot_nf *)
Compute equiv_lexp (cnot_nf cfa) ctr.
Compute equiv_lexp (cnot_nf ctr) cfa.

(* 
Exercice 5 - Codage cor compacte
*)
Definition cor_compacte := \a~a ctr.

(* Verifier cor_compacte *)
Compute equiv_lexp ( cor_compacte ctr ctr ) ctr.
Compute equiv_lexp ( cor_compacte cfa ctr ) ctr.
Compute equiv_lexp ( cor_compacte ctr cfa ) ctr.
Compute equiv_lexp ( cor_compacte cfa cfa ) cfa.


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

(* Format equiv_lexp (expression) output-expectation *)
(* Verifier cas c0 - c3 *)
Compute equiv_lexp (csucc c0) c1.
Compute equiv_lexp (csucc c1) c2.
Compute equiv_lexp (csucc c2) c3.
Compute equiv_lexp (csucc c3) (\f x~f (f (f (f x)))). (* equiv a c4 *)

(*********************************************************)
(************* IV - Opérations sur les entiers ***********)
(*********************************************************)
(*
Exercice 1 -  Coder dans Coq la fonction addition de deux entiers de Church comme une lexp,
              et la tester sur quelques exemples.
*)

Definition cadd := \n m~\f x~n f (m f x).

(* Definir c4-c7 en utilisant csucc *)
Definition c4 := csucc c3.
Definition c5 := csucc c4.
Definition c6 := csucc c5.
Definition c7 := csucc c6.
(* Reverifier csucc avec c6 *)
Compute equiv_lexp (csucc c6) (\f x~f (f (f (f (f (f (f x))))))). (* equiv a c7 *)

(* Verifier cas c0 + c0 *)
Compute equiv_lexp ( cadd c0 c0 ) c0.

(* Verifier cas c0 + ci, 2eme argument *)
Compute equiv_lexp ( cadd c0 c1 ) c1.
Compute equiv_lexp ( cadd c0 c2 ) c2.
Compute equiv_lexp ( cadd c0 c3 ) c3.
Compute equiv_lexp ( cadd c0 c4 ) c4.

(* Verifier cas ci + c0, 1er argument *)
Compute equiv_lexp ( cadd c5 c0 ) c5.
Compute equiv_lexp ( cadd c6 c0 ) c6.
Compute equiv_lexp ( cadd c7 c0 ) c7.
Compute equiv_lexp ( cadd c2 c0 ) c2.

(* Verifier cas general ci + cj *)
Compute equiv_lexp ( cadd c1 c2 ) c3.
Compute equiv_lexp ( cadd c2 c3 ) c5.
Compute equiv_lexp ( cadd c2 c4 ) c6.
Compute equiv_lexp ( cadd c5 c3 ) (csucc c7).

(* Verifer cas cj + cj *)
Compute equiv_lexp ( cadd c1 c1 ) c2.
Compute equiv_lexp ( cadd c2 c2 ) c4.
Compute equiv_lexp ( cadd c3 c3 ) c6.
Compute equiv_lexp ( cadd c4 c4 ) (csucc c7).

(*
Exercice 2 -  Faire la même chose avec la multiplication de deux entiers de Church.
*)

Definition cmult := \n m~\f~n (m f).

Definition c8 := csucc c7.
Definition c9 := csucc c8.
Definition c10 := csucc c9.


(* Verifier cas c0 * cx et cx * c0 *)
Compute equiv_lexp ( cmult c0 c0 ) c0.
Compute equiv_lexp ( cmult c0 c1 ) c0.
Compute equiv_lexp ( cmult c0 c2 ) c0.
Compute equiv_lexp ( cmult c0 c3 ) c0.
Compute equiv_lexp ( cmult c4 c0 ) c0.
Compute equiv_lexp ( cmult c6 c0 ) c0.
Compute equiv_lexp ( cmult c8 c0 ) c0.


(* Verifier cas c1 * cx (identité multiplicative) *)
Compute equiv_lexp ( cmult c1 c0 ) c0.
Compute equiv_lexp ( cmult c1 c1 ) c1.
Compute equiv_lexp ( cmult c1 c2 ) c2.
Compute equiv_lexp ( cmult c1 c3 ) c3.
Compute equiv_lexp ( cmult c1 c4 ) c4.
Compute equiv_lexp ( cmult c5 c1 ) c5.
Compute equiv_lexp ( cmult c6 c1 ) c6.
Compute equiv_lexp ( cmult c7 c1 ) c7.
Compute equiv_lexp ( cmult c8 c1 ) c8.


(* Verifier cas général ci * cj *)
Compute equiv_lexp ( cmult c2 c2 ) c4.
Compute equiv_lexp ( cmult c2 c3 ) c6.
Compute equiv_lexp ( cmult c2 c4 ) c8.
Compute equiv_lexp ( cmult c3 c3 ) c9.
Definition c12 := cadd c6 c6.
Compute equiv_lexp ( cmult c3 c4 ) c12.
Compute equiv_lexp ( cmult c4 c4 ) (cadd c12 c4).

(*
Exercice 3 -  Tester cadd et cmult sur des booléens. Les résultats ont-ils du sens ?
*)

Compute red_cbn ( cadd ctr ctr ).
Compute red_cbn ( cadd ctr cfa ).
Compute red_cbn ( cadd cfa cfa ).
Compute red_cbn ( cmult ctr ctr ).
Compute red_cbn ( cmult ctr cfa ).
Compute red_cbn ( cmult cfa cfa ).

(* Non, il y a pas de sens arithmetique, le codage de bool est utilise pour un autre
objectif. Deplus, quand on fait cadd bool et bool, on obtient les expressions redexes 
correspond respectivement a ctr ctr cfa mais leur interpretation arithmetique n'a 
aucun sens  *)

(* Bonus *)
(*
Exercice 4: Preuve de la commutativite de cadd et de cmult
Pour chaque cadd et cmult, je fais 2 preuves differente

CADD:
  Pour tout nombre entier de Church a et b, on a
    (cadd a b) = (\n m~\f x~n f (m f x)) a b = \f x~a f (b f x)
    => f^(a) ( f^(b) (x) ) = f^(a+b) (x)
    (cadd b a) = (\n m~\f x~n f (m f x)) b a = \f x~b f (a f x)
    => f^(b) ( f^(a) (x) ) = f^(b+a) (x)
  Alors (cadd a b) = (cadd b a)

CMULT: 
    Pour tout nombre entier de Church a et b, on a
    (cmult a b) = (\n m~\f~n (m f)) a b = \f~a (b f)
    => (b f)^(a) = (f^(b))^a = f^(b*a)
    (cmult b a) = (\n m~\f~n (m f)) b a = \f~b (a f)
    => (a f)^(b) = (f^(a))^b = f^(a*b)
  Alors (cmult a b) = (cmult b a)
*)

(*
Exercice 5: Codage de l'exponentielle
*)

Definition cexp := \n m~m n.

(* Verifier cexp *)
(* Verifier cas c0^n et n^c0 *)
Compute equiv_lexp ( cexp c0 c1 ) c0.
Compute equiv_lexp ( cexp c0 c5 ) c0.
Compute equiv_lexp ( cexp c0 c8 ) c0.
Compute equiv_lexp ( cexp c0 c10 ) c0.
Compute equiv_lexp ( cexp c0 c12 ) c0.

(* Observer cn^0 qui renvoie la fonction identite *)
Compute red_cbn (cexp c3 c0).

(* Verifier cas cn^c1 *)
Compute equiv_lexp ( cexp c1 c1 ) c1.
Compute equiv_lexp ( cexp c2 c1 ) c2.
Compute equiv_lexp ( cexp c3 c1 ) c3.
Compute equiv_lexp ( cexp c4 c1 ) c4.
Compute equiv_lexp ( cexp c5 c1 ) c5.
Compute equiv_lexp ( cexp c6 c1 ) c6.

(* Verfier cas c1^cn *)
Compute equiv_lexp ( cexp c1 c1 ) c1.
Compute equiv_lexp ( cexp c1 c3 ) c1.
Compute equiv_lexp ( cexp c1 c5 ) c1.
Compute equiv_lexp ( cexp c1 c6 ) c1.
Compute equiv_lexp ( cexp c1 c8 ) c1.
Compute equiv_lexp ( cexp c1 c10 ) c1.

(* Verifier cas cn^cm *)
Compute equiv_lexp ( cexp c2 c2 ) c4.
Compute equiv_lexp ( cexp c2 c3 ) c8.
Compute equiv_lexp ( cexp c3 c2 ) c9.
Definition c16 := cadd c12 c4.
Definition c27 := cadd c16 (cadd c10 c1).
Compute equiv_lexp ( cexp c3 c3 ) c27.

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
(******** VI - Structures de données - les couples ********)
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
Tester cpland sur les couples (false,true) et (true,true) 
et le reste de la table de verite.
*)
Compute equiv_lexp ( cpland cpltt ) ctr.
Compute equiv_lexp ( cpland cplft ) cfa.
Compute equiv_lexp ( cpland cpltf ) cfa.
Compute equiv_lexp ( cpland cplff ) cfa.


(*********************************************************)
(************** VII - Codage du prédécesseur **************)
(*********************************************************)
(*
Exercice 1 - Coder dans Coq la fonction iter qui prend un entier de Church n, une
             fonction g et un argument x et qui applique n fois la fonction g sur x. 
*)

Definition iter := \n g x~n g x.

(* La tester avec c4, la fonction csucc et c0. *)

(* Tester 0 fois cn *)
Compute equiv_lexp ( iter c0 csucc c1 ) c1.
Compute equiv_lexp ( iter c0 csucc c2 ) c2.
Compute equiv_lexp ( iter c0 csucc c3 ) c3.
Compute equiv_lexp ( iter c0 csucc c4 ) c4.
Compute equiv_lexp ( iter c0 csucc c5 ) c5.
Compute equiv_lexp ( iter c0 csucc c6 ) c6.
Compute equiv_lexp ( iter c0 csucc c7 ) c7.
Compute equiv_lexp ( iter c0 csucc c8 ) c8.
Compute equiv_lexp ( iter c0 csucc c9 ) c9.

(* Tester n fois Cn *)
Compute equiv_lexp ( iter c1 csucc c0 ) c1.
Compute equiv_lexp ( iter c4 csucc c2 ) c6.
Compute equiv_lexp ( iter c7 csucc c1 ) c8.
Compute equiv_lexp ( iter c4 csucc c0 ) c4.
Compute equiv_lexp ( iter c5 csucc c2 ) c7.
Definition c18 := cadd c9 c9.
Compute equiv_lexp ( iter c9 csucc c9 ) c18.


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
Definition cpl75 := cpl c7 c5.
Compute equiv_lexp ( cpred1 cpl75 ) (cpl c5 c6).


(*
Exercice 3 - Coder dans Coq le prédécesseur d’un entier de Church
*)
Definition cpl00 := cpl c0 c0.
Definition cpred := \n~fst (iter n cpred1 cpl00).
Definition cpred_simple := \n~fst (n cpred1 cpl00).
(*
Tester sur quelques exemples dont c0.
*)
Compute equiv_lexp ( cpred c1 ) c0.
Compute equiv_lexp ( cpred c2 ) c1.
Compute equiv_lexp ( cpred c3 ) c2.
Compute equiv_lexp ( cpred c4 ) c3.
Compute equiv_lexp ( cpred c5 ) c4.
Compute equiv_lexp ( cpred c6 ) c5.
Compute equiv_lexp ( cpred c7 ) c6.
Compute equiv_lexp ( cpred c8 ) c7.
Compute equiv_lexp ( cpred (cmult c5 c6) ) (cadd (cmult c3 c9) c2).
Compute equiv_lexp ( cpred_simple c8 ) c7.
Compute equiv_lexp ( cpred_simple c1 ) c0.
Compute equiv_lexp ( cpred_simple c2 ) c1.
Compute equiv_lexp ( cpred_simple c3 ) c2.
Compute equiv_lexp ( cpred_simple c4 ) c3.
Compute equiv_lexp ( cpred_simple c5 ) c4.
Compute equiv_lexp ( cpred_simple c6 ) c5.
Compute equiv_lexp ( cpred_simple c7 ) c6.
Compute equiv_lexp ( cpred_simple c8 ) c7.

(* Bonus *)
(*
Exercice 4 - Codage de la soustraction
*)
Definition csous := \n m~iter m cpred n.

(* Verifier cas cn - c0 *)
Compute equiv_lexp (csous c1 c0) c1.
Compute equiv_lexp (csous c3 c0) c3.
Compute equiv_lexp (csous c5 c0) c5.
Compute equiv_lexp (csous c7 c0) c7.
Compute equiv_lexp (csous c9 c0) c9. 

(* Verifier cas c0 - cn ## Ca devait etre 0 dans tous les cas *)
Compute equiv_lexp (csous c0 c0) c0.
Compute equiv_lexp (csous c0 c9) c0.
Compute equiv_lexp (csous c0 c1) c0.
Compute equiv_lexp (csous c0 c4) c0.
Compute equiv_lexp (csous c0 c5) c0.

(* Verifier cas cn - cm *)
Compute equiv_lexp (csous c1 c1) c0.
Compute equiv_lexp (csous c9 c5) c4.
Compute equiv_lexp (csous c9 c7) c2.
Compute equiv_lexp (csous c9 c4) c5.

(* Les cas cn - cm avec cm > cn ## Pareil que c0 - cn *)
Compute equiv_lexp (csous c1 c10) c0.
Compute equiv_lexp (csous c2 c9) c0.
Compute equiv_lexp (csous c3 c8) c0.
Compute equiv_lexp (csous c4 c7) c0.

(* 
Exercice 5 - Codage de la definition du inferieur ou egal
*)
Definition leq := \n m~ceq0 (csous n m).

(* Verifier des cas vrai *)
Compute equiv_lexp (leq c0 c5) ctr.
Compute equiv_lexp (leq c1 c4) ctr.
Compute equiv_lexp (leq c2 c9) ctr.
Compute equiv_lexp (leq c3 c10) ctr.

(* Verifier des cas faux *)
Compute equiv_lexp (leq c4 c1) cfa.
Compute equiv_lexp (leq c3 c2) cfa.
Compute equiv_lexp (leq c5 c0) cfa.
Compute equiv_lexp (leq c9 c5) cfa.

(*********************************************************)
(************ VIII - Combinateur de point fixe ************)
(*********************************************************)
(*
Exercice 2 - Définir dans Coq  Y comme une lexp
*)


Definition Y := \f~(\x~f (x x))(\x~f (x x)).


(* 
   On peut vérifier ici que les deux exemples trouvés à l'exercice précédent
   ont ou n'ont pas de forme normale 
*)
(* Exemple a de forme normale *)
Compute red_cbn ( Y c0 ).
(* Exemple n'a pas de forme normale *)
Compute red_cbn ( Y c1 ).


(*********************************************************)
(******* IX - Codage de définitions récursives  *********)
(*********************************************************)
(*
Exercice 1 - En utilisant les opérateurs définis précédemment (cif, ceq0, cmult, cpred), 
             définir dans Coq la fonctionnelle associée à fact.
*)

Definition cfonc := \f n· cif (ceq0 n) c1 ( cmult n ( f (cpred n) ) ).

Compute equiv_lexp ( cfonc Y c0 ) c1.
Compute equiv_lexp ( cfonc Y c1 ) c1.

(*
Exercice 2 - Définir la fonction factorielle dans Coq comme une lexp.
*)

Definition cfact := Y cfonc.

(*
   La tester avec red_cbn sur de tout petits entiers (< 4).
*)
(* Tester cas particulier c0 c1 *)
Compute equiv_lexp ( cfact c0 ) c1.
Compute equiv_lexp ( cfact c1 ) c1.

(* Tester cas general *)
Compute equiv_lexp ( cfact c2 ) c2.
Compute equiv_lexp ( cfact c3 ) c6.


(*********************************************************)
(************** X - Structure de donnees  ****************)
(*********************************************************)
(*** 6.2 Type somme: entier ou boolean ***)
(* 
Exercice 1 - Codage des injections
*)
Definition injA := \x~\k1 k2~k1 x.
Definition injB := \x~\k1 k2~k2 x.

(* 
Exercice 2
*)
Definition cdouble := \x~cadd x x.
Definition inj := \i~i cdouble cnot.
(* Tester *)
Compute equiv_lexp (inj (injA c1) ) c2.
Compute equiv_lexp (inj (injA c2) ) (csucc c3).
Compute equiv_lexp (inj (injB cfa) ) ctr.
Compute equiv_lexp (inj (injB ctr) ) cfa.

(*** 6.3 Type donnee optionnelle ***)
(* 
Exercice 1: Codage
*)
Definition Some := \x~\k1 k2~k1 x.
Definition None := \k1 k2~k2.  

(*
Exercice 2: Fonction qui prend en entree cn renvoie 
            Some c0 si Null, Some cn + 1 sinon
*)
Definition osucc := \n~n (\k~Some (csucc n)) (Some c0).
(* Verifier cas particulier c0 *)
Compute equiv_lexp (osucc None) (Some c0).
Compute equiv_lexp (osucc c0) (Some c0). (*None a le meme format que c0*)

(* Verifier cas general *)
Compute equiv_lexp (osucc c1) (Some c2).
Compute equiv_lexp (osucc c2) (Some c3).
Compute equiv_lexp (osucc c4) (Some c5).
Compute equiv_lexp (osucc c7) (Some c8).
Compute equiv_lexp (osucc (cmult c3 c6)) (Some (csous (cmult c4 c5) c1)).

(*** 6.4 Type algebrique: Les arbres binaires ***)
(*
Exercice 1: Codage de la feuille et du noeud
*)
Definition cleaf := \n k1 k2~k1 n.
Definition cnode := \l r k1 k2~k2 l r.
Definition arb1 := cnode (cnode (cleaf c1) (cleaf c2)) (cleaf c3).
Definition arb_simple := cnode (cleaf c1) (cleaf c2).
(*
Exercice 2: Codage de la fonction isleaf
*)
Definition isleaf := \a~a (\n~ctr) (\l r~cfa).

Definition arb2 := cnode (cleaf c4) (cnode (cleaf c5) (cleaf c6)).
Definition arb3 := cnode (cnode (cleaf c7) (cleaf c8)) (cleaf c9).
Definition arb4 := cnode (cnode (cleaf c10) (cnode (cleaf c1) (cleaf c12))) (cleaf c3).

(* Verifier isleaf avec les feuille *)
Compute equiv_lexp (isleaf (cleaf c1)) ctr.
Compute equiv_lexp (isleaf (cleaf c3)) ctr.
Compute equiv_lexp (isleaf (cleaf c12)) ctr.

(* Verifier isleaf avec les arbres *)
Compute equiv_lexp (isleaf arb1) cfa.
Compute equiv_lexp (isleaf arb2) cfa.
Compute equiv_lexp (isleaf arb3) cfa.
Compute equiv_lexp (isleaf arb4) cfa.

(*
Exercice 3: Codage de la fonction sumTree
*)
Definition sumTree := (\f a~ a (\n~n) (\l r~cadd (f l) (f r))).
Definition SumTree := Y sumTree.

(* Verifier avec les arbres *)
Compute equiv_lexp (SumTree arb1) c6.
Compute equiv_lexp (SumTree arb_simple) c3.
Compute equiv_lexp (SumTree arb2) (cadd c12 c3).










