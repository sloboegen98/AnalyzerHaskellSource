(** ... continuing from the previous seminar  *)

(** For more formal treatment of syntax turn to the reference manual:
    https://coq.github.io/doc/v8.11/refman/language/gallina-specification-language.html#syntax-of-terms *)

    From mathcomp Require Import ssreflect.

    Module My.
    
    Inductive nat : Type :=
    | O
    | S of nat.
    
    (** Some more syntactic sugar *)
    Fixpoint addn_sugar (n m : nat) {struct n} : nat :=
      if n is S n' then S (addn_sugar n' m) else m.
    
    (** Some more syntactic sugar *)
    Definition addn_sugar' :=
      fix rc (n m : nat) {struct n} : nat :=
      if n is S n' then S (rc n' m) else m.
    
    (* Print addn. *)
    Print addn_sugar.
    
    Fixpoint addn (n m : nat) {struct n} : nat :=
      if n is S n' then S (addn n' m)
      else m.
    
    (** Alternative implementation by recursion on the second parameter *)
    Fixpoint addn' (n m : nat) {struct m} :=
      if m is S m' then S (addn' n m')
      else n.
    
    Variable z : nat.
    Compute addn O z.
    Compute addn' O z.
    
    
    (** Exercise *)
    Fixpoint muln (n m : nat) : nat :=
      if n is S n' then
        addn m (muln n' m)
      else O.
    
    Compute muln (S (S (S O))) (S (S O)).  (* 3 * 2 is 6 *)
    Compute muln (S (S O)) O.              (* 2 * 0 is 0 *)
    
    
    
    
    (** mutual induction *)
    (* You can define mutually recursive functions using "with" *)
    Fixpoint is_even (n : nat) : bool :=
      if n is S n' then is_odd n'
      else true
    with is_odd n :=
      if n is S n' then is_even n'
      else false.
    
    Compute is_even (S (S (S O))).
    Compute is_even (S (S O)).
    Compute is_odd (S (S (S O))).
    Compute is_odd (S (S O)).
    
    
    (** Exercise:
        write a function [applyn] which applies [n] times
        a function [f] on natural numbers to an input [x] *)
    Definition applyn :=
      fun (f : nat -> nat) =>
        fix rec n x {struct n} : nat :=
        if n is S n' then
          f (rec n' x)
        else x.
    Check applyn :
      (nat -> nat) -> nat -> nat -> nat.
    Compute applyn (addn (S (S O))) (S (S (S O))) O.
    (* Exercise: implement multiplication using applyn *)
    
    End My.
    
    (** After closing a module, the identifiers defined in it,
        get prefixed with the module's name *)
    Check My.nat.
    Check My.applyn.
    
    From mathcomp Require Import ssrbool ssrnat.
    
    (** We have now access to standard boolean functions,
        e.g. here is how exclusive disjunction is implemented in the
        standard library: *)
    Print addb.
    (** It's called [addb] because it is essentially addition mod j *)
    
    (** Now that we can define our own stuff let's just use what
        the standard library already have *)
    
    (** Some interactive queries, [About] tells you more than [Check] *)
    About nat.
    About S.
    
    (** We have some syntactic sugar like [42]  *)
    Check 42.  (* internally this a pile of 42 [S]'s ending with [O] *)
    Check S (S (S O)).  (* Coq displays this back to us as [3] *)
    
    (** This decimal notation does not work for [My.nat] because
        it is only associated with the standard [nat] type.
        Although, it's possible to implement decimal notations for
        our own types. *)
    
    (** Coq lets us control what we see.
        E.g. here is how to switch off all the syntactic sugar: *)
    Set Printing All.
    Check 5 + 4.  (* [+] is a notation for [addn] *)
    (**
    addn (S (S (S (S (S O))))) (S (S (S (S O))))
         : nat
    *)
    Unset Printing All.  (** Let's switch it on back again *)
    
    (** How to find out what notations mean: *)
    Locate ".+1".     (* Notation "n .+1" := (S n). *)
    
    Variable x : nat.
    Check x.+1.  (* means [S x] *)
    
    
    
    From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
    
    Module MyNamespace.
    
    (** Now we can use currying to model functions of arbitrary arity,
        but what about functions returning multiple results,
        e.g. Euclidean division: returns quotient and reminder?  *)
    
    Inductive prodn : Type :=
      | pairn of nat & nat.
    
    (** Now it's possible to implement such function,
       it'll have the following type
       [divmod : nat -> nat -> prodn] *)
    
    (** But it'd be hard to create a specialized product type for each
        combination of types, e.g. [nat] and [bool], [bool] and [nat],
        [bool] and [bool] and so on.
        This is why inductive types can be parameterized: *)
    
    Section ProductType.
    
    Inductive prod (A B : Type) : Type :=
      | pair of A & B.
    
    
    (** Important: [prod] is not a type, it's a type constructor!
        E.g. [prod nat nat] is a type (equivalent to [prodn]),
        but e.g. the following is not well-typed: *)
    
    Fail Check nat -> nat -> prod nat.
    (** Error message:
        The term "prod nat" has type "Type -> Type"
        which should be Set, Prop or Type. *)
    
    Check prod.
    (**
    prod
         : Type -> Type -> Type
    i.e. [prod] takes to types to make a new type
    *)
    
    (** Let's see the type of [pair] *)
    About pair.
    (* pair : forall A B : Type, A -> B -> prod A B *)
    
    
    (** Intermezzo: dependent types and [forall]
        In Coq, it's possible to give a type to a function
        which returns different values in different branches of
        [if] (or [match]) expressions: *)
    
    Definition foo : forall n : nat, if n is S n' then nat else bool :=
      fun n : nat =>
        if n is S n' then 1 else true.
    
    (** End of intermezzo *)
    
    
    (** Explicit binding of type constructor's parameters for
        data constrtuctors
      *)
    Check pair nat bool 42 true : prod nat bool.
    (** This is a pair of the number [42] and the boolean value [true],
        notice that we need to pass their respective types explicitly *)
    
    (** Passing explicitly types can be very annoying, especially
        when the system can infer those for us.
        E.g. Coq knows that [42]'s type is [nat] and
        [true]'s type is [bool] so it can, in principle,
        help us with that.
        And indeed, Coq has _implicit arguments_ mechanism.
        Here is how we active it for [pair]: *)
    Arguments pair [A B] _ _.
    (** [Arguments pair [A B] _ _] means that the types [A] and [B] are
        going to be inferred, so the user does not have to supply those.
        For instance, it's easier to create a pair now : *)
    Check pair 42 true.
    (** Notice that [pair nat bool 42 true] does not typecheck: *)
    Fail Check pair nat bool 42 true : prod nat bool.
    (** Does it mean that we magically can escape passing all the arguments
        explicitly?
        No, it does not. [pair] still has the same type as it the point
        of its definition. We just changed the way the user supplies its
        arguments. To forbid Coq from implicitly supplying the arguments
        we can use [@] syntax, which locally switches off inference: *)
    Check @pair nat bool 42 true : prod nat bool.
    
    (** There is a way to turn this behavior on by default: *)
    Set Implicit Arguments.
    (** From now on Coq will try to figure out which
        arguments can be made implicit. *)
    
    (** Working with pairs using [prod] and [pair] is not very common,
        because people usually prefer more suggestive notations like
        [A * B] for the product type or [(a, b)] for pairs.
        Coq lets us introduce our own notations which modify its
        parser on-the-fly. *)
    
    (** Here is a notation for the product type.
        I'll explain some elements of it below. *)
    Notation "A * B" := (prod A B) (at level 40, left associativity) : type_scope.
    
    
    (** Notation scopes *)
    
    (** The programmer may reuse the same symbol for multiple
        functions (terms). Have you noticed we just reused [*] symbol
        to mean type product? You can find out what [*] can also mean
        using the [Locate] command: *)
    Locate "*".
    (* "m * n" := muln m n : nat_scope (default interpretation) *)
    
    (** "default interpretation" means that when Coq is not sure
        about the purpose of [*], it will assume it is being used
        as the multiplication symbol, so the following fails: *)
    Fail Check nat * bool.
    (* The term "nat" has type "Set" while it is expected to have type "nat". *)
    
    (** Here we have to give a hint to Coq that we mean a product type here: *)
    Check (nat * nat)%type.
    (** we do this by specifying the notation scope with [%type] *)
    
    (** Here is another way of doing that: *)
    Check (nat * bool) : Type.
    (** now Coq knows that the term in the parentheses is supposed to
        be a type (remember that in Coq there is almost no difference
        between terms/programs and types), so Coq knows how to
        interpret [*] (it certainly cannot be multiplication) *)
    
    (** Here is yet another way of changing the default meaning of [*] *)
    Open Scope type_scope.
    Locate "*".
    (* "A * B" := prod A B : type_scope (default interpretation) *)
    (** [Open Scope] changes the default interpretation of notations *)
    
    Check (nat * nat).  (* now this works *)
    (** When you open a new notation scope Coq uses stack discipline
        to track your actions, so we can change the notation scope back. *)
    Close Scope type_scope.
    Fail Check (nat * nat).
    Locate "*".
    (* "m * n" := muln m n : nat_scope (default interpretation) *)
    
    
    (** Let us mention the role of [left associativity]
        in the above notation definition, which I repeatt
        here for convenience:
    
    Notation "A * B" := (prod A B) (at level 40, left associativity) : type_scope.
    *)
    
    (** To model tuples of sizes more than two one may use
        nested tuples. For example, a triple of elements of
        types [nat], [bool], and [nat] can be modelled like so: *)
    Check ((nat * bool) * nat)%type.
    
    (** [left associativity] lets us write drop the parentheses
        and write it as *)
    Check (nat * bool * nat)%type.
    
    (** Notice that if we associate parentheses to the right,
        like so *)
    Check (nat * (bool * nat))%type.
    (** this will be a different, though isomorphic, type. *)
    
    
    (** Having introduced notation for the [prod] type constructor,
       it would be nice to add notation for the [pair] data contructor
       to be able to write e.g. [(42, true)] instead of
       [pair 42 true], which is as you already know
       a shorthand for [@pair nat bool 42 true]. *)
    
    (** Here is a rather weak approach: *)
    Notation "( p ; q )" := (pair p q).
    Check (1; false).
    (** It's weak because the following wouldn't work:
    [Check (1; false; 2)]
    *)
    
    (** But we would want to use triples, quadruples, etc.
        In this case, recursive notations come to the rescue. *)
    Notation "( p , q , .. , r )" := (pair .. (pair p q) .. r)
                                       : core_scope.
    
    Check (1, false) : nat * bool.
    Check (1, false, 3) : nat * bool * nat.
    Check (1, false, 3, true) : nat * bool * nat * bool.
    
    (** Now, let's define projections on pairs: *)
    Definition fst {A B : Type} : A * B -> A :=
      fun p => match p with | pair a b => a end.
    
    Notation "p .1" := (fst p).
    
    Definition snd {A B : Type} : A * B -> B :=
      fun p => match p with | pair a b => b end.
    
    Notation "p .2" := (snd p).
    
    Compute (1, true).1. (** reduces to [1], the first component *)
    Compute (1, true).2. (** reduces to [true], the second component *)
    
    (** Here we define a function which swaps two components
        of the inpute pair *)
    Definition swap {A B : Type} : A * B -> B * A :=
      fun p =>
        match p with
        | pair a b => pair b a
        end.
    
    End ProductType.
    
    
    
    Section SumType.
    
    (** Sum type *)
    
    Inductive sum (A B : Type) : Type :=
    | inl of A
    | inr of B.
    
    Notation "A + B" := (prod A B) (at level 50, left associativity) : type_scope.
    
    (** explained during the seminar *)
    
    End SumType.
    
    
    
    
    
    (** As explained during the seminar there is
        a correspondence between functional terms and types
        on one side and proofs and propositions on the other.
        Type theory lets us manipulate proofs as
        first-class objects, i.e. pass those to functions,
        pack them into data structures, return from functions,
        etc. *)
    
    Section Intuitionistic_Propositional_Logic.
    
    (** Implication *)
    
    (** Implication corresponds to the function type.
        Having a proof of [A] implies [B], amounts to
        having a function of type [A -> B] which
        transforms a proof of proposition [A] into
        a proof of proposition [B].
    
        Here is a proof that [A] implies [A].
        This corresponds to the identity function *)
    Definition A_implies_A (A : Prop) :
      A -> A
    :=
      fun proof_A : A => proof_A.
    
    (** Yet another example: *)
    Definition A_implies_B_implies_A (A B : Prop) :
      A -> B -> A
    :=
      fun proof_A => fun proof_B => proof_A.
    
    (** This corresponds to the classic [const] function *)
    
    
    (** Conjunction *)
    
    (** We know that the conjunction of propositions
        [A] and [B] is provable when we can have
        proofs of both propositions packed together.
        Here is how we express it using Coq's inductive
        types. *)
    Inductive and (A B : Prop) : Prop :=
      | conj of A & B.
    
    Notation "A /\ B" := (and A B) : type_scope.
    
    (** Notice the strong resemblance between [and] and [prod]:
    Inductive prod (A B : Type) : Type :=
      | pair of A & B.
    *)
    
    (** Let's prove that conjunction is commutative *)
    Definition andC (A B : Prop) :
      A /\ B -> B /\ A                (* proposition *)
    :=
    (* the proof of [A /\ B -> B /\ A] *)
      fun proof_AandB =>
        match proof_AandB with
        | conj proofA proofB => conj proofB proofA
        end.
    (* end of the proof of [A /\ B -> B /\ A] *)
    
    (** Have you noticed that the proof of
        [A /\ B -> B /\ A] looks exactly the same
        as the function that swaps the two components of a pair?
    
    Definition swap {A B : Type} : A * B -> B * A :=
      fun p =>
        match p with
        | pair a b => pair b a
        end.
    *)
    
    (** to be continued... *)
    End Intuitionistic_Propositional_Logic.
    