From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Section InductionExercises.

(** * Arithmetic expression language *)

(** Inspired by "Exercises on Generalizing the Induction Hypothesis"
    (https://homes.cs.washington.edu/~jrw12/InductionExercises.html), James Wilcox (2017).
    Adapted to SSReflect syntax and Mathcomp library.
*)

(** Here is a (trivial) language of arithmetic expressions
   consisting of nested additions and subtractions of constants. *)
Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr & expr.

(** Let us define a special notation for our language.
    We reuse the standard arithmetic notations here, but only inside
    double square brackets (see examples below) *)
Declare Custom Entry expr.
Notation "'[[' e ']]'" := e (e custom expr at level 2).
Notation "x + y" := (Plus x y) (in custom expr at level 2, right associativity).
Notation "x - y" := (Minus x y) (in custom expr at level 2, right associativity).
Notation "` x ` " := (Const x) (in custom expr at level 2, x constr).
Notation "( x )" := x (in custom expr, x at level 2).
Notation "x" := x (in custom expr at level 0, x ident).

(** Here is how we write Plus (Const 0) (Minus (Const 2) (Const 1)) *)
Check [[
          `0` + (`2` - `1`)
      ]].
(** And this is Plus (Plus (Const 0) (Const 1)) (Const 2) *)
Check [[
          (`0` + `1`) + `2`
      ]].

(** Here is a straightforward evaluation function for the expression language. *)
Fixpoint eval_expr (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => eval_expr e1 + eval_expr e2
  | Minus e1 e2 => eval_expr e1 - eval_expr e2
  end.

(** Alternatively, this can be written like so
Fixpoint eval_expr (e : expr) : nat :=
  match e with
  | [[ `n` ]] => n
  | [[ e1 + e2 ]] => eval_expr e1 + eval_expr e2
  | [[ e1 - e2 ]] => eval_expr e1 - eval_expr e2
  end.
 *)

(** Some unit tests *)
Check erefl : eval_expr [[ `0` + (`2` - `1`) ]] = 1.
Check erefl : eval_expr [[ (`0` + `1`) + `2` ]] = 3.


(** * Compiling arithmetic expressions to a stack language *)

(** Here is a "low-level" stack language which can serve as the target language
for a compiler from the arithmetic expression language above.

A program in this language is a list of instructions, each of which manipulates
a stack of natural numbers. There are instructions for pushing constants onto
the stack and for adding/subtracting the top two elements of the stack, popping them, and
pushing the result. *)

Inductive instr := Push (n : nat) | Add | Sub.

Notation " << n >> " := (Push n) (at level 0, n constr).
Notation " <<+>> " := (Add) (at level 0).
Notation " <<->> " := (Sub) (at level 0).

Definition prog := seq instr.

Definition stack := seq nat.

(**
 The [run] function is an interpreter for this language.
 It takes a program (list of instructions) and the current stack,
 and processes the program instruction-by-instruction, returning the final stack.
 *)
Fixpoint run (p : prog) (s : stack) : stack :=
  if p is (i :: p') then
    let s' :=
        match i with
        | Push n => n :: s
        | Add => if s is (a1 :: a2 :: s') then a2 + a1 :: s'
                 else s
        | Sub => if s is (a1 :: a2 :: s') then a2 - a1 :: s'
                 else s
        end
    in
    run p' s'
  else s.

(** Unit test *)
Check erefl : run [:: <<30>>; <<20>>; <<2>>; <<+>>; <<10>>; <<->>; <<+>>] [::] = [:: 42].

(* [:: <<30>>; <<20>>; <<2>>; <<+>> *)
(*  ; <<10>>; <<->>; <<+>>] *)

(* [:: [[`30`]] ; [[ `2` + `20` ]] ; <<10>>; <<->>; <<+>>] *)
(* [:: [[`30`]] ; [[ (`2` + `20`) - `10` ]] ; <<+>>] *)


(** Now here is a compiler from "high-level" expressions to "low-level" stack
programs. Take a minute to understand how it works. (Try it on a few example
expressions, and try passing the results into [run] with various initial stacks.)
*)
Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [:: Push n]
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [:: Add]
  | Minus e1 e2 => compile e1 ++ compile e2 ++ [:: Sub]
  end.

(** Here is one unit test: *)
Check erefl :
  compile [[`30` + ((`20` + `2`) - `10`)]] = [:: <<30>>; <<20>>; <<2>>; <<+>>; <<10>>; <<->>; <<+>>].


(** Here is a correctness theorem for the compiler: it preserves the meaning of
programs. By "meaning", in this case, we just mean final answer computed by the
program. For high-level expression, the answer is the result of calling
[eval_expr]. For stack programs, the answer is whatever [run] leaves on the top of
the stack. The correctness theorem states that these answers are the same for an
expression and the corresponding compiled program. *)

Lemma run_is_linear (prog1 prog2 : prog) (s : stack) :
  run (prog1 ++ prog2) s = run prog2 (run prog1 s).
Proof.
  move: s.
  elim: prog1=> [| //=]; first by constructor.
Qed.


Lemma compile_correct_gen_s e s :
  run (compile e) s = (eval_expr e) :: s.
Proof.
  move: s.
  elim: e; try constructor;
    move=> e He e0 He0 s //=;
    rewrite run_is_linear;
    rewrite run_is_linear;
    by rewrite He0 He.
Qed.

Theorem compile_correct e :
  run (compile e) [::] = [:: eval_expr e].
Proof.
  apply: compile_correct_gen_s e [::].
Qed.


(** Hints (SPOILER ALERT):
     1. You will need to generalize the lemma as we did before.
        Think of what happens when we run a stack program in an arbitrary stack (not
        necessarily empty as above).
     2. If the first think didn't work for you, then let me expand this more.
        Basically, [run] does not change the stack we start with.
     3. OK, here is the formal statement of Hint 2: [run (compile e) s = (eval_expr e) :: s].
     4. To prove the lemma of Hint 3 you will probably need to state and prove a lemma
        about running a concatenation of two stack programs.
 *)




(** Optional exercise: decompiler *)

(* Print option. *)

Fixpoint decompile_rec 
  (p : prog) (seqexpr : seq expr) : option expr :=
    if p is (i :: p') then
      match i with
        | <<n>> => decompile_rec p'  ((Const n) :: seqexpr)
        | <<+>> => 
          if seqexpr is (e2 :: e1 :: seqexpr') 
          then decompile_rec p' ((Plus e1 e2) :: seqexpr')
          else None
        | <<->> =>
          if seqexpr is (e2 :: e1 :: seqexpr')
          then decompile_rec p' ((Minus e1 e2) :: seqexpr')
          else None
      end
    else
      (* if size seqexpr is 1 then (ohead seqexpr) else None *)
      ohead seqexpr
  .

(** Implement a decompiler turning a stack program into the corresponding expression *)
Definition decompile (p : prog) : option expr := 
  decompile_rec p [::]
.

(* Compute decompile [:: <<30>>; <<20>>; <<2>>; <<+>>; <<10>>; <<->>; <<+>>]. *)


(** Unit test *)

Check erefl :
decompile [:: <<30>>; <<20>>; <<2>>; <<+>>; <<10>>; <<->>; <<+>>] = some [[ `30` + (`20` + `2`) - `10` ]].

(* Check erefl : *)
Compute decompile [:: <<30>>; <<20>>].
(* = None. *)

Check erefl :
decompile [:: <<30>>; <<+>>] = None.


(** Optional: Prove your implementation is correct by showing that [decompile] cancels [compile]. *)
Lemma decompile_compile e :
  decompile (compile e) = Some e.
Proof. admit. Admitted.

Lemma some_inj (T : Type) (x y : T) :
  (x = y) <-> (Some x = Some y).
Proof. 
  split.
  - move=> xy. by rewrite xy.
  apply: Some_inj.
Qed.


(** Optional: Show our [compile] function is [injective] *)
Lemma compile_inj :
  injective compile.
Proof.
  rewrite/ injective.
  move=> e1 e2 He.
  rewrite some_inj.
  rewrite -!decompile_compile.
  by rewrite He.
Qed.


End InductionExercises.




Section BooleanReflection.

(** A spec for boolean equality *)
Variant eq_xor_neq (T : eqType) (x y : T) : bool -> bool -> Set :=
  | EqNotNeq of x = y : eq_xor_neq x y true true
  | NeqNotEq of x != y : eq_xor_neq x y false false.


Lemma eqVneq (T : eqType) (x y : T) :
  eq_xor_neq x y (y == x) (x == y).
Proof.
  rewrite eq_sym.
  by case: (altP eqP); constructor.
Qed.
(** Hint: Use [case: (altP eqP)] to get the right assumptions.
          Also, try using [case: eqP] instead and see the difference. *)


(** Use [eqVneq] to prove the following *)
Lemma eqVneq_example (T : eqType) (w x y z : T) :
  w == x -> z == y ->
  (x == w) /\ (y == z) /\ (z == y).
Proof.
  case: eqVneq=> //=.
  case: eqVneq=> //=.
Qed.
(** Hint: use [case: eqVneq] *)


Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof.
  apply: (iffP andP); rewrite / is_true;
   rewrite -Bool.andb_true_iff.
  
   - case: a; by case b.
  case: a; by case.
Qed.

Arguments andX {a b}.

(** Prove the following lemma using [andX] lemma and [rewrite] tactic.
    USE ONLY [move] and [rewrite] to solve this.
    No [case] or [=> []] or any other form of case-splitting is allowed! *)
Lemma andX_example a b :
  a && b -> b && a && a && b.
Proof.
  (* Set Printing Coercions. *)
  move/ andX.
  rewrite Bool.andb_comm.
  rewrite Bool.andb_assoc.
  rewrite Bool.andb_assoc.
  rewrite Bool.andb_diag.
  rewrite -Bool.andb_assoc.
  rewrite Bool.andb_diag.
  rewrite Bool.andb_comm.
  move/ andX.
  done.
Qed.
(** Hint: [reflect]-lemmas may act like functions (implications) *)

(** Optional exercise: implement a multi-rewrite rule for the [maxn] and [minn] functions *)
Variant max_min_multirule (m n : nat) :
   nat -> nat -> nat -> nat -> Set :=
  | MaxMinNatLe of m <= n : max_min_multirule m n ...(** Fill in the indices *)
  | MaxMinNatGe of m >= n : max_min_multirule m n ...(** Hint: look at the lemma [maxminP] below *)
.

Lemma maxminP m n : max_min_multirule m n (minn n m) (minn m n)
                                          (maxn n m) (maxn m n).
Proof.
  
Qed.

(** Use [case: maxminP] to prove the following *)
Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Proof.

Qed.

End BooleanReflection.
