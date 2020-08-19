From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Exercise1.
Definition impl_distr (A B C : Prop) :
  (A -> (B -> C)) <-> ((A -> B) -> (A -> C))
(* (A -> B -> C) -> (A -> B) -> (A -> C) /\
   ((A -> B) -> A -> C) -> A -> B -> C  *)
:= conj 
    (fun abc ab => fun a => abc a (ab a))
    (fun abac a b => abac (fun _ => b) a).

  (* . Admitted.   <-- replace this line with ":=" *)
(* Provide an explicit proof term here, do not use tactics *)
End Exercise1.


(** Use SSReflect tactics below *)
Section Exercise2.
Variable DNE : forall A : Prop, ~ ~ A -> A.

Lemma drinker_paradox (P : nat -> Prop) :
  exists x, P x -> forall y, P y.
Proof.
  apply: DNE.
  move=> not_dp.
  apply: (not_dp).
  exists 0=> _ y.
  apply: DNE=> not_py.
  apply: (not_py).
  case: not_dp.
  by exists y => /not_py.
Qed.
End Exercise2.


Section Exercise3.

Lemma helper n m:
  (minn n m <> n) -> minn n m = m.
Proof.
  move: (leq_total n m) => /orP.
  case.
  - move/ minn_idPl=> //.
  move/ minn_idPr=> //.
Qed.

Lemma helper2 m n p :
  m <= n -> p <= n - m -> m + p <= n.
Proof.
  move=> m_le_n p_le_n_sub_m.
  by move: (leq_subRL p m_le_n) <-.
Qed.

Lemma min_plus_minus m n p :
  minn n m + minn (n - m) p = minn n (m + p).
Proof.
  case (@minn_idPl n m).
  move/ minn_idPl.
  - move=> min_n.
    move:(min_n) => /minn_idPl => ->.
    move:(min_n).
    rewrite -subn_eq0.
    move/ eqP => ->.
    rewrite min0n addn0.
    move: (leq_add min_n (leq0n p)).
    rewrite addn0.
    by move/minn_idPl.
  
  move/ helper.
  move=> min_m.
  move:(min_m) => ->.
  move: (min_m).
  move/ minn_idPr.
  move=> m_le_n.
  case (@minn_idPl (n - m) p).
  - move=> min_n_sub_m.
    rewrite min_n_sub_m.
    move: (min_n_sub_m).
    move/ minn_idPl.
    rewrite (leq_subLR n m p) => /minn_idPl ->.
    rewrite addnC.
    by apply subnK.

  move/ helper.
  move=> min_p.
  rewrite min_p.
  move: min_p => /minn_idPr.
  move=> p_le_n_sub_m.
  rewrite minnC.
  by move: (helper2 m_le_n p_le_n_sub_m) => /minn_idPl => ->.
Qed.
End Exercise3.



Section Exercise4.
Variables B C : Type.

(** This is the category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

Lemma monic_inj (f : B -> C) : monic f -> injective f.
Proof.
  move=> monic_f x1 x2 e.
  suffices: f \o (fun _ : unit => x1) = f \o (fun _ : unit => x2);
    first by apply monic_f.
  by rewrite/ comp e.
Qed.  

End Exercise4.



Section Exercise5.
(** Continuation-passing style list sum function
    See https://en.wikipedia.org/wiki/Continuation-passing_style *)

(** Recursive helper function *)
Fixpoint sumn_cont' {A} (l : seq nat) (k : nat -> A) : A :=
  if l is (x :: xs) then sumn_cont' xs (fun answer => k (x + answer))
  else k 0.

(** The main definition *)
Definition sumn_cont (l : seq nat) : nat :=
  sumn_cont' l (fun x => x).

Lemma correct_sumn_cont' (X : Type) l (f : nat -> X) :
  sumn_cont' l f = f (sumn l).
Proof.
  elim: l f=> //= a l IH f.
  by rewrite IH.
Qed.

(** Prove that the continuation-passing style list sum function is correct w.r.t
    the standard [sumn] function *)
Lemma sumn_cont_correct l :
  sumn_cont l = sumn l.
Proof.
  by apply: correct_sumn_cont'.
Qed.

End Exercise5.



Section Exercise6.

(* Prove [8x = 6y + 1] has no solutions in [nat] *)

Lemma uninjective (A B : eqType) (f : A -> B) (x1 x2 : A) :
  f x1 != f x2 -> x1 != x2.
Proof.
  move=> neqf.
  apply/ negP => //.
  case/ eqP.
  move=> eqx.
  move: neqf.
  rewrite eqx.
  by case/ negP.
Qed.


Lemma no_solution x y :
  8*x != 6*y + 1.
Proof.
  assert (NEQ : (odd (8*x) != (odd (6 * y).+1))).
  - apply/ negP.
    move=> //=.
    rewrite odd_mul=> //=.
    assert (ODD6 : (~odd (6 * y))).
    + rewrite odd_mul=> //=.
    rewrite odd_mul=> //=.
  rewrite addnS addn0.
  by move: (uninjective NEQ).
Qed.
End Exercise6.



Section Exercise7.

Lemma dup {A} : A -> A * A. Proof. by []. Qed.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+1 -> P n.+2) -> 
  forall n, P n.
Proof.
  move=> p0 p1 Istep n; suffices: P n /\ P n.+1 by case.
  by elim: n=> // n [/Istep pn12] /dup[/pn12].
Qed.

Lemma perenos x (POS : 2 <= x):
  (x.-1 %/ 2 = x %/ 2 - 1) -> (1 + x.-1 %/ 2 = x %/ 2).
Proof.
  move=> ->.
  rewrite addnC subnK=> //.
  by move: (@leq_div2r 2 2 x)  => ->.
Qed.

Lemma odd_eq_odd_2  n :
  ~~ odd n.+2 = ~~ odd n.
Proof.
  by apply Bool.negb_involutive.
Qed.


Lemma ex_leq x n :
  (x <= n) -> (forall y, y <= n -> x != y) -> False.
Proof.
  move=> le_n_x H.
  move: (H x le_n_x).
  by move/ eqP.
Qed.

Lemma upper2 x :
  (x <= 2) -> (x != 0) -> (x != 1) -> (x != 2) -> False.
Proof.
  move: (@ex_leq x 2) => H.
  move=> x_le_2 x_ne_0 x_ne_1 x_ne_2.
  move: (H x_le_2)=> HH.
  suffices: (forall y : nat, y <= 2 -> x != y).
  move => H2.
  by move: (HH H2).
  case=>//.
  case=>//.
  by case=>//.
Qed.

Lemma exercise n :
  ~~ odd n ->
  (n.-1 %/ 2) = (n %/ 2 - 1).
Proof.
  elim/nat_ind2: n => //.
  move=> n IH1 _.
  move: (leq_total 2 n) => /orP.
  case.
  - move=> n_ge_1 not_oddn.
    rewrite -addn2.
    rewrite divnDr=> //.
    suffices: (2 %/ 2 = 1) => // ->.
    rewrite -addnBA=> //.
    rewrite subnn addn0 addnC -subn1.
    rewrite -addnBA=> //.
    + rewrite divnDl=> //.
      suffices: (2 %/ 2 = 1) => // ->.
      rewrite subn1.
      rewrite perenos=> //.
      rewrite IH1=> //.
      by rewrite -odd_eq_odd_2.
    rewrite (leq_trans _ n_ge_1)=> //=.

  case: (@eqP _ n 0).
  move=> n_0.
  by rewrite n_0.

  case: (@eqP _ n 1).
  move=> n_1.
  by rewrite n_1.

  case: (@eqP _ n 2).
  move=> n_2.
  by rewrite n_2.

  move/eqP => n_not_2 /eqP => n_not_1 /eqP => n_not_0.
  move=> n_le_2.
  by move: (upper2 n_le_2 n_not_0 n_not_1 n_not_2).
Qed.
End Exercise7.




Section Exercise8.
(** [def] is the default value, i.e. we assume type [T] is not empty *)
Variables (T : Type) (def : T).

(**
What is "leftpad"?

Leftpad is a function that takes a character, a length, and a string (which we encode as a sequence),
and pads the string to that length.
It pads it by adding the character to the left, e.g.

Compute leftpad 0 5 [:: 1; 2; 3]. (* returns [:: 0; 0; 1; 2; 3], i.e. we pad the input "string"
                                     to the length of 5 by prepending two zeros to the left *)
Compute leftpad 0 2 [:: 1; 2; 3]. (* returns [:: 1; 2; 3]: we return the original input because
                                     the required length (2) is smaller than the length of the input *)
*)

Definition leftpad (c : T) (n : nat) (s : seq T) : seq T :=
  ncons (n - size s) c s.

(** Prove the following three properties of the leftpad function *)

Lemma length_max_spec c n s :
  size (leftpad c n s) = maxn n (size s).
Proof.
  by rewrite size_ncons addnC -maxnE maxnC.
Qed.
(** Local alias for the [nth] function returning the n-th element of the input sequence *)
Local Notation nth := (nth def).

Lemma prefix_spec c n s :
  forall i, i < n - size s -> nth (leftpad c n s) i = c.
Proof.
  move=> i.
  by rewrite nth_ncons => ->.
Qed.

Lemma suffix_spec c n s i :
  nth (leftpad c n s) (n - size s + i) = nth s i.
Proof.
  rewrite nth_ncons addKn.
  case: ifP=> //=.
  by rewrite ltnNge leq_addr.
Qed.
End Exercise8.


Section Exercise9.
Lemma exercise9 n : 12 <= n -> exists x y, x * 4 + y * 5 = n.
Proof.
  move=> GTn.
  case: (@eqP _ (n %% 5) 0)=> n_mod_5.
  - exists 0.
    exists (n %/ 5).
    by rewrite mul0n add0n -(addn0 (n %/ 5 *5)) -{3}n_mod_5 -divn_eq.

  exists ((n %/ 4) - (n %% 4)).
  exists (n %% 4).
  rewrite mulnBl addnBAC.
  rewrite -addnBA.
  rewrite -(mulnBr).
  suffices: (5 - 4 = 1)=> // ->.
  by rewrite muln1 -divn_eq.

  - suffices: (5 = 4 + 1) => // ->.
    rewrite mulnDr.
    apply: leq_addr.
  
  rewrite leq_pmul2r=> //.
  suffices: (3 <= n %/ 4).
  suffices: (n %% 4 <= 3).
  - apply: leq_trans.
  - rewrite -ltnS.
    by apply ltn_pmod.
  
  move: GTn.
  by apply: (leq_div2r 4).
Qed.
End Exercise9.


Section Exercise10.

(**
Prove that for arbitrary propositions [p1], [p2], ..., [pn],
    p1 <-> p2 <-> p3 <-> ... <-> pn
if and only if
    p1 -> p2 -> p3 -> ... -> pn -> p1
 *)

Fixpoint pairup_props (conn : Prop -> Prop -> Prop) (s : seq Prop) : Prop :=
  if s is (p1 :: ((p2 :: s'') as s')) then conn p1 p2 /\ pairup_props conn s'
  else True.  (** it is possible to not add [True] at the end, but let us keep it simple *)

Definition equiv (s : seq Prop) : Prop :=
  pairup_props iff s.

Definition circ (s : seq Prop) : Prop :=
  if s is (p1 :: s') then
    pairup_props (fun p q => p -> q) (s ++ [:: p1])
  else True.

Arguments equiv : simpl nomatch.
Arguments circ : simpl nomatch.
Arguments pairup_props : simpl nomatch.

Section Test.
Variables p1 p2 p3 p4 : Prop.
Compute equiv [:: p1; p2; p3; p4].
Compute circ [:: p1; p2; p3; p4].
End Test.

Lemma equiv_iff_circ (s : seq Prop) :
  equiv s <-> circ s.
Proof.
Admitted.
End Exercise10.


Section OptionalExerciseForExtraCredit.
Variable T : Type.

Inductive btree : Type :=
| BTempty
| BTnode (l : btree) (a : T) (r : btree).

Implicit Type bt : btree.

(** A generic binary tree size algorithm *)
Fixpoint bin_size bt : nat :=
  if bt is (BTnode l _ r) then (bin_size l + bin_size r).+1
  else 0.

Fixpoint is_brtree brt : bool :=
  if brt is (BTnode l _ r) then
    [&& is_brtree l,
        is_brtree r &
        (bin_size l == bin_size r)
        ||
        (bin_size l == (bin_size r).+1)]
  else
    true.
Arguments is_brtree : simpl never.

(** Compute the difference between the size of a left subtree [brt] and [s] (the size of the right subtree) *)
Fixpoint brt_diff brt s : nat :=
  if brt is (BTnode l _ r) then
    if s == 0 then 1
    else if odd s then brt_diff l (s %/ 2)
    else brt_diff r (s.-1 %/ 2)
  else 0.

(** Optional assignment for extra credit *)
Lemma brt_diff_correct brt (s : nat) :
  is_brtree brt ->
  (bin_size brt == s) ||
  (bin_size brt == s.+1) ->
  brt_diff brt s = bin_size brt - s.
Proof.
Admitted.
End OptionalExerciseForExtraCredit.