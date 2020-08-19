From hahn Require Import Hahn.
Require Import Omega.
Require Import Bool List.
Export ListNotations.
Require Import Arith Arith.EqNat.
Require Extraction.

Inductive is_smallest : nat -> list nat -> Prop :=
  smallest_unit : forall n, is_smallest n [n]
| smallest_head : forall n m tl, 
    n <= m -> is_smallest m tl -> is_smallest n (n::tl)
| smallest_tail : forall n m tl, 
    m <  n -> is_smallest m tl -> is_smallest m (n::tl).

Hint Constructors is_smallest.

Lemma exfalso' : forall T : Prop, False -> T.
Proof.
	intros T TT.
	destruct TT.
	(* apply False_ind.
	apply TT. *)
Qed.

Definition exfalso'' : forall T : Prop, False -> T := 
	fun T TT => 
				match TT with
				end.

Print exfalso''.

Theorem smallest_exists l (NNIL : [] <> l) : {n | is_smallest n l}.
(* Hint: *)
(* SearchAbout le. ->  le_gt_dec *)
Proof.
	(* Print list. *)
	(* Print list_ind. *)
	(* Print is_smallest_ind. *)
	(* generalize dependent NNIL. *)
	(* generalize dependent l. *)
	  
	induction l.
	{ 
		exfalso.
		red in NNIL.
		apply NNIL.
		auto. 
	}
	
	destruct l as [ |hd tl].
	{
		(* exists a.
		apply smallest_unit. *)
		(* exists a.
		constructor . *)
		eexists. constructor.
	}
	{	
		apply IHl.
	}

	(* assert ({n0 : nat | is_smallest n0 (n :: l)}) as HH. *)
	(* { apply IHl. desf.} *)
	(* assert ([] <> hd :: tl) as HH.
	{
		desf.
	}
	apply IHl in HH.
	destruct HH as [n0 NN]. *)
	(* destruct IHl as [n NN]. *)
Qed.

Require Extraction. 
Extraction Language Haskell.
Extraction smallest_exists.

Lemma smallest_with_n a n tl (LE : a <= n)
      (SST : is_smallest a (a :: tl)) :
  is_smallest a (a :: n :: tl).
(* Hint: le_gt_dec, omega *)
Proof.
Admitted.
 
Lemma smallest_without_n a n tl
      (SST : is_smallest a (a :: n :: tl)) :
  is_smallest a (a :: tl).
Proof.
Admitted.

Inductive is_sorted : list nat -> Prop :=
  sorted_nil  : is_sorted []
| sorted_one  : forall n, is_sorted [n]
| sorted_cons : forall n tl
                       (STL : is_sorted tl)
                       (SST : is_smallest n (n::tl)),
    is_sorted (n::tl).

Hint Constructors is_sorted.

Inductive is_inserted : nat -> list nat -> list nat -> Prop :=
  ins_head : forall n tl, is_inserted n tl (n::tl)
| ins_tail : forall n m tl tl'
                    (INS : is_inserted n tl tl'),
    is_inserted n (m::tl) (m::tl').

Hint Constructors is_inserted.

Lemma head_is_smallest a l (SS : is_sorted (a::l)) :
  is_smallest a (a::l).
Proof.
Admitted.

Lemma tail_is_sorted a l (SS : is_sorted (a::l)) :
  is_sorted l.
Proof.
Admitted.

Lemma insert_bigger a b l l'
      (SST : is_smallest a (a::l))
      (LT : a < b)
      (INS : is_inserted b l l') :
  is_smallest a (a::l').
Proof.
Admitted.

Lemma insert_sorted a l (SORT : is_sorted l) :
  {l' | is_inserted a l l' & is_sorted l'}.
(* Hint: le_gt_dec *)
Proof.
Admitted.

Lemma is_inserted_perm a l l' (INS : is_inserted a l l') : Permutation (a :: l) l'.
(* Hint: perm_swap *)
Proof.
Admitted.

Theorem sort l : {l' | Permutation l l' & is_sorted l'}.
Proof.
Admitted.

Print sort.

Extraction Language OCaml.
Recursive Extraction sort.