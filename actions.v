Require Import String.
Require Import List.

Inductive types : Set := 
| Boolean : types
| ID : types
.

Inductive ioh : Set :=
| Input : ioh
| Output : ioh
| Internal : ioh
.

(* amount of types -> types of payload -> name -> tid *)
Inductive actionInput : Type :=
| inputEvent: nat -> list types -> string -> nat -> actionInput
.

(* amount of values -> values in payload -> name -> tid *)
Inductive actionOutput : Type :=
| outputEvent : nat -> list (nat + bool) -> string -> nat -> actionOutput
.

(* Equality of a list of types l and list of values l' in payloads of actions.
This fixpoint is required by Definition 4.3 to define Event Signature Equality. *)
Fixpoint eq_types_payloads (l:list types)(l':list (nat + bool)) : Prop := 
  match l,l' with 
    | ID :: ts, (inl _) :: vs => eq_types_payloads ts vs 
    | Boolean :: ts, (inr _) :: vs => eq_types_payloads ts vs
    | nil,nil => True 
    | _,_ => False
  end.

(* Definition 4.3 of Event Signature Equality for input and output actions. *)
Definition eq_in_out (i:actionInput)(o:actionOutput) := 
  match i,o with
  | (inputEvent n ts name tid),(outputEvent n' pes' name' tid') => 
    n=n' /\ name=name' /\ tid=tid' /\ eq_types_payloads ts pes'
  end
.

Notation "A =io= B" := (eq_in_out A B)(at level 25, left associativity).

Inductive actionMatch : Type :=
| matchEvent : forall (tid : nat)(i : actionInput)(o: actionOutput), i =io= o -> actionMatch
.

Inductive dbacc : Set := 
| Delete : dbacc
| Read : dbacc 
| Create : dbacc
| Update : dbacc 
.

(* accessed id -> type of database operation -> tid  *)
Inductive actionDB : Type := 
| dbAccess : nat -> dbacc -> nat -> actionDB
.

(* Boolean formula, here in the course of this proof abstracted as 
simply the evaluation of the formula [true,false]*)
(* name -> formula -> tid *)
Inductive actionGuard : Type :=
| guard : string ->bool -> nat -> actionGuard
.

(* Definition 4.2 *)
Inductive action : ioh -> Type := 
| input : actionInput -> action Input
| output: actionOutput -> action Output
| matches : actionMatch -> action Internal
| db : actionDB -> action Internal
| gu : actionGuard -> action Internal
.

(* Helper for the matching of synchronization actions *)
Definition s_equal_depth_io {t1 t2:ioh} (a:action t1)(b:action t2) : Prop :=
  match a,b with 
    | input (inputEvent n ts name tid), input (inputEvent n' ts' name' tid') => 
      n=n' /\ ts = ts' /\ name=name' /\ tid = tid' 
    | output (outputEvent n pes name tid),output (outputEvent n' pes' name' tid') => 
      n = n' /\ name = name' /\ pes = pes' /\ tid = tid'
    | _,_ => False
  end.

(* Identity of Actions *)
Definition act_identity {t1 t2:ioh} (a:action t1)(b:action t2) : Prop :=
  match a,b with 
    | input (inputEvent n ts name tid), input (inputEvent n' ts' name' tid') => 
      n=n' /\ ts = ts' /\ name=name' /\ tid = tid'
    | output (outputEvent n pes name tid),output (outputEvent n' pes' name' tid') => 
      n = n' /\ name = name' /\ pes = pes' /\ tid = tid' 
    | matches (matchEvent tid ai ao eq_proof), matches (matchEvent tid' ai' ao' eq_proof') => 
      tid = tid' /\ s_equal_depth_io (input ai) (input ai') /\ s_equal_depth_io (output ao) (output ao')
    | db (dbAccess id op tid),db (dbAccess id' op' tid') => 
      id=id' /\ op = op' /\ tid=tid'
    | gu (guard name b tid),gu (guard name' b' tid') => 
      name=name' /\ b=b' /\ tid=tid'
    | _,_ => False
  end.

Notation "A =i= B" := (act_identity A B)(at level 25, left associativity).

(* Helper expressing that types of values in two lists of payload values are equal *)
Fixpoint eq_sig_pl_pl (l:list (nat + bool))(l':list (nat + bool)) : Prop := 
  match l,l' with 
    | ((inl _) :: ls) ,((inl _) :: ls' ) => eq_sig_pl_pl ls ls'
    | ((inr _) :: ls) ,((inr _) :: ls' ) => eq_sig_pl_pl ls ls'
    | nil,nil => True
    | _,_ => False 
  end.

Definition sig_eq_actions (a:action Output)(b:action Output) : Prop := 
  match a,b with 
    | output (outputEvent n vs name tid),output (outputEvent n' vs' name' tid') =>
      n=n' /\ name=name' /\ tid=tid' /\ eq_sig_pl_pl vs vs'
    | _,_ => False
  end.

Notation "A <-o-> B" := (sig_eq_actions A B)(at level 25, left associativity).

(* Definition 4.10 *)
Definition act_equiv {t1 t2:ioh}(a:action t1)(b:action t2) : Prop :=
  (* case (i) *)
  a =i= b \/ 
  ( match a,b with 
  (* case (ii) *)
  | input (a_internal), output (b_internal) => a_internal =io= b_internal
  | output (a_internal), input (b_internal) => b_internal =io= a_internal
  | output (_) as a', output (_) as b' => a'<-o-> b'
  (* case (iii) *)
  (* p' is carried here, because for the transitivity proof we need to know the i' is input output equal to o' *)
  | matches (matchEvent tid i o p), matches (matchEvent tid' i' o' p') =>
      (input i) =i= (input i') /\ (i =io= o') /\ (i' =io= o) /\ ((output o) <-o-> (output o'))
  (* case (iv) *)
  | matches (matchEvent tid i o p), input i' => (input i') =i= (input i) /\ i' =io= o
  | matches (matchEvent tid i o p), output o' => (output o =i= output o' \/ output o <-o-> output o') /\ i =io= o'
  (* case (v) *)
  | input i, matches (matchEvent tid i' o' p) => (input i) =i= (input i') /\ i =io= o'
  | output o, matches (matchEvent tid i' o' p) => (output o =i= output o' \/ output o <-o-> output o') /\ i' =io= o
  | _,_ => False
  end
  )
.

Notation "A <--> B" := (act_equiv A B)(at level 25, left associativity).

Require Import Program.
Require Import RelationClasses.


Lemma act_identity_refl {t:ioh} : forall (a : action t), a =i= a.
Proof.
destruct a; dependent destruction a; simpl; 
  try (dependent destruction i); try (dependent destruction o); 
  repeat (split; eauto using eq_refl).
Qed.

Lemma act_identity_sym {t1 t2: ioh} : forall (a : action t1)(b : action t2), a =i= b -> b =i= a.
Proof.
intros a b a_identical_b.
destruct a; destruct b; dependent destruction a; dependent destruction a0; 
simpl in *; try contradiction; try  firstorder (subst;auto).
- dependent destruction i; dependent destruction o; dependent destruction i0; dependent destruction o0.
  firstorder (subst;auto).
-dependent destruction i; dependent destruction o; dependent destruction i0; dependent destruction o0.
  firstorder (subst;auto).
Qed.

Ltac depdestr_list xs :=
  lazymatch xs with
  | nil       => idtac
  | ?h :: ?t  =>
      dependent destruction h;
      simpl in *; subst;
      depdestr_list t
  end.

Tactic Notation "multidepdestr" constr_list(xs) :=
  depdestr_list xs.


Lemma act_identity_trans {t1 t2 t3 : ioh} : forall (a : action t1)(b: action t2)(c: action t3),
 a =i= b /\ b =i= c -> a =i= c.
Proof.
intros a b c [H H'].
destruct a, b, c; dependent destruction a0; dependent destruction a1; dependent destruction a;
 try (simpl in H; simpl in H'; contradiction); try firstorder(subst;auto).
all: dependent destruction i; dependent destruction o; dependent destruction i0; dependent destruction o0; dependent destruction i1; dependent destruction o1; firstorder (subst;auto).
Qed.

Lemma act_equiv_refl {t1 : ioh} : forall (a:action t1), a <--> a.
Proof.
intros a;destruct a; left; auto using act_identity_refl.
Qed.

Lemma eq_sig_pl_pl_refl : forall (pes : list( nat + bool)), eq_sig_pl_pl pes pes.
Proof.
induction pes.
- simpl; auto.
- destruct a; simpl; eauto using IHpes.
Qed.

Lemma eq_sig_pl_pl_sym : forall (l l' : list (nat + bool)), eq_sig_pl_pl l l' -> eq_sig_pl_pl l' l.
Proof.
induction l.
- induction l'. 
  + eauto.
  + intros. destruct a; simpl in H; contradiction. 
- induction l'.
  + intros. simpl in H. destruct a; contradiction.
  + intros. destruct a,a0;(simpl in *; exact (IHl l' H) || simpl in H; contradiction). 
Qed.

Lemma sig_pl_sym : forall (a b:action Output), a <-o-> b -> b <-o-> a.
Proof.
intros a b H.
dependent destruction a. 
dependent destruction b.
simpl in *.
dependent destruction a. dependent destruction a0.
firstorder (subst;auto).
auto using eq_sig_pl_pl_sym.
Qed.

Lemma eq_types_payloads_eq : forall (lt lt':list types)(lp:list (nat+bool)), eq_types_payloads lt lp /\ eq_types_payloads lt' lp -> lt = lt'.
Proof.
induction lt.
- destruct lt'.
  + eauto.
  + intros lp [H0 H1]. exfalso. destruct lp; eauto. simpl in H1; destruct t; contradiction.
- induction lt'.
  + induction lp. 
    * intros [H0 H1]. simpl in H0; destruct a; contradiction.
    * intros [H0 H1]. simpl in H1; contradiction.
  + induction lp.
    * intros [H0 H1]. simpl in H1; destruct a0; contradiction.
    *  intros [H0 H1]. destruct a1,a0,a; try (simpl in H0; contradiction || simpl in H1; contradiction).
      ** f_equal. simpl in H0,H1. apply (IHlt lt' lp). eauto.
      ** f_equal. simpl in H0,H1. apply (IHlt lt' lp). eauto.
Qed.

Lemma type_payloads_impl_sig : forall (ts : list types)(pes pes' : list (nat + bool)), 
  eq_types_payloads ts pes /\ eq_types_payloads ts pes' -> eq_sig_pl_pl pes pes'.
Proof.
induction ts.
- destruct pes; destruct pes'; intros [H H0];
  try (simpl in H0; contradiction); try (simpl in H1; contradiction).
  + simpl in *. trivial.
- destruct pes; destruct pes'; intros [H H0]; destruct a; try (simpl in H; simpl in H0; contradiction);
    simpl in H; destruct s; try contradiction;
    simpl in H0; destruct s0; try contradiction;
    simpl; eauto using IHts.
Qed.

Lemma eq_types_payloads_sig_pl_pl_trans : forall (tl: list types)(pl pl':list (nat + bool)), eq_types_payloads tl pl /\ eq_sig_pl_pl pl pl' -> eq_types_payloads tl pl'.
Proof.
induction tl.
- intros pl pl' [H0 H1]. destruct pl; destruct pl'; simpl in *; auto || contradiction.
- intros pl pl' [H0 H1]. destruct pl,pl'; simpl in H0,H1; destruct a; 
   try ( contradiction || destruct s; ( contradiction || destruct s0; try contradiction; simpl; eauto using IHtl)).
Qed.

Lemma eq_sig_pl_pl_trans : forall  (a b c: list (nat + bool)), eq_sig_pl_pl a b /\ eq_sig_pl_pl b c -> eq_sig_pl_pl a c.
Proof.
induction a.
- intros b c [H0 H1]. destruct b.
  + destruct c; trivial.
  + destruct c; trivial; simpl in H0; contradiction.
- destruct b.
  + destruct c; intros [H0 H1]; simpl in H0; destruct a; contradiction.
  + destruct c; intros [H0 H1]; try (simpl in H1; destruct s; contradiction).
    destruct a,s,s0; simpl in *; try (eauto using IHa); try (contradiction).
Qed.


Theorem act_equiv_sym {t1 t2: ioh} : forall (a:action t1)(b:action t2), a <--> b -> b <--> a.
Proof.
intros a b H.
destruct a,b; destruct H as [H|H]; 
  (* eliminate cases where a direct contradiction can be applied *) 
  try contradiction;
  (* for a = b with a and b being the same type it can be solved by using s_equal symmetry *)
  try (simpl in H; destruct a; contradiction).
- left; apply (act_identity_sym (input a)(input a0) H).
- right; trivial.
- right; trivial.
- right; trivial.
- left. apply (act_identity_sym (output a)(output a0) H).
- right. auto using sig_pl_sym.
- dependent destruction a0. right. split.
  + destruct H as [H0 H1]. destruct H0.
    * left. apply (act_identity_sym (output a)(output o) H).
    * right. auto using sig_pl_sym.
  + destruct H. trivial.
- dependent destruction a. right. trivial.
- dependent destruction a. right.
  + destruct H as [H0 H1]. destruct H0. split.
    * left. apply (act_identity_sym (output o)(output a0) H).
    * trivial.
    * split.
       ** right. auto using sig_pl_sym.
       ** trivial.
- dependent destruction a0. dependent destruction a.
  + left. simpl in *. dependent destruction i0. dependent destruction i. 
dependent destruction o0. dependent destruction o.
  simpl in *. firstorder (subst; auto).
- dependent destruction a0. dependent destruction a. simpl in *.
  dependent destruction i. dependent destruction i0. dependent destruction o. dependent destruction o0.
  right. simpl in *. firstorder (subst; auto). apply (eq_sig_pl_pl_sym l0 l2 H5).
- left. auto using act_identity_sym.
- left. auto using act_identity_sym.
Qed.

Lemma id_act_in_io_io_trans: forall (a : actionInput)(a0 : actionInput)(a1 : actionOutput),  (input a) =i= (input a0) /\ a0 =io= a1 -> a =io= a1.
Proof.
intros a a0 a1 [H H'].
destruct a, a0, a1.
simpl in *.
firstorder (subst; auto).
Qed.

Lemma id_act_out_io_io_trans: forall (a : actionOutput)(a0 : actionOutput)(a1 : actionInput),  (output a) =i= (output a0) /\ a1 =io= a0 -> a1 =io= a.
Proof.
intros a a0 a1 [H H'].
destruct a, a0, a1.
simpl in *.
firstorder (subst; auto).
Qed.

Theorem eq_io_trans_s_equal : forall (a c : actionInput)(o : actionOutput), a =io= o /\ c =io= o -> input a =i= input c.
Proof.
intros a c o [H0 H1].
dependent destruction a; dependent destruction o; dependent destruction c.
simpl in *.
firstorder (subst;auto).
eauto using eq_trans,eq_types_payloads_eq.
Qed.



Theorem eq_in_out_output_swap : forall (i : actionInput)(o o' : actionOutput),
  output o =i= output o' /\ i =io= o -> i =io= o'.
Proof.
intros o o' i.
dependent destruction o; dependent destruction o'; dependent destruction i.
intros [H H0].
simpl in *.
firstorder (subst; auto).
Qed.

Theorem eq_in_out_input_swap : forall (i i':actionInput)(o:actionOutput),
  input i' =i= input i /\ i =io= o ->  i' =io= o.
Proof.
intros i i' o. 
destruct i,i',o.
intros [H H0].
simpl in *.
firstorder (subst;auto).
Qed.

Theorem eq_io_sig_eq_impl_io_eq : forall (a : actionInput)(b c : actionOutput),
  a =io= b /\ output b <-o-> output c -> a =io= c. 
Proof.
intros a b c.
dependent destruction a; dependent destruction b; dependent destruction c.
intros [H0 H1].
simpl in *.
firstorder (subst; auto).
eauto using eq_types_payloads_sig_pl_pl_trans.
Qed.

Theorem eq_in_eq_in_sig_trans : forall (a : actionInput)(b c: actionOutput), a =io= b /\ a =io= c -> output b <-o-> output c.
Proof.
intros a b c [H H0].
dependent destruction a; dependent destruction b; dependent destruction c.
simpl in *.
firstorder (subst; auto).
eauto using eq_trans,type_payloads_impl_sig.
Qed.

Lemma s_equal_impl_sig_eq : forall (a b : action Output), a =i= b -> a <-o-> b.
Proof.
intros a b H.
dependent destruction a. dependent destruction b.
destruct a,a0.
simpl in *.
firstorder (subst;auto).
induction l0.
- simpl. trivial.
- destruct a; simpl; eauto using IHl0.
Qed.

Theorem eq_sig_sym : forall (a b:action Output), a <-o-> b -> b <-o-> a.
Proof.
intros a b H.
dependent destruction a; dependent destruction b.
simpl in *.
destruct a, a0.
firstorder (subst; auto).
eauto using eq_sig_pl_pl_sym.
Qed.

Theorem sig_pl_pl_eq_trans : forall (a b c : action Output), a <-o-> b /\ b <-o-> c -> a <-o-> c.
Proof.
intros a b c [H0 H1].
dependent destruction a; dependent destruction b; dependent destruction c.
dependent destruction a; dependent destruction a0; dependent destruction a1.
simpl in *.
firstorder (subst; auto).
eauto using eq_trans, eq_sig_pl_pl_trans.
Qed.

Theorem s_equal_sig_eq_out_impl_sig_eq_out : forall (a b c : action Output),
      a =i= b /\ b <-o-> c -> a <-o-> c.
intros a b c [H H0].
dependent destruction a; dependent destruction b; dependent destruction c.
dependent destruction a; dependent destruction a0; dependent destruction a1.
simpl in *.
firstorder (subst; auto).
Qed.

Theorem s_eql_swap_output_sig : forall (a b c: action Output), a <-o-> b /\ b =i= c -> a <-o-> c.
Proof.
intros a b c [H0 H1].
dependent destruction a; dependent destruction b; dependent destruction c.
dependent destruction a; dependent destruction a0; dependent destruction a1.
simpl in *.
firstorder (subst;auto).
Qed.

Lemma infer_matches_eq: forall (i i0 : actionInput)(o o0: actionOutput)(tid tid0:nat)(e:i =io= o)(e0:i0 =io= o0),
 matches (matchEvent tid i o e) =i= matches (matchEvent tid0 i0 o0 e0) -> (input i) =i= (input i0) /\ i =io= o /\ (output o) <-o-> (output o0).
Proof.
intros i i0 o o0 tid tid0 e e0.
intros H.
simpl in H. destruct i. destruct o. destruct i0. destruct o0.
simpl in *.
firstorder (subst; auto).
eauto using eq_sig_pl_pl_refl.
Qed.



Create HintDb act.
Hint Resolve
     act_identity_trans act_identity_sym id_act_in_io_io_trans
     eq_io_trans_s_equal eq_in_out_output_swap
     eq_io_sig_eq_impl_io_eq eq_in_eq_in_sig_trans
     eq_in_out_input_swap s_equal_impl_sig_eq eq_sig_sym
     sig_pl_pl_eq_trans s_equal_sig_eq_out_impl_sig_eq_out
     s_eql_swap_output_sig infer_matches_eq id_act_out_io_io_trans
  : act.


Theorem act_equiv_trans {t1 t2 t3: ioh} : forall (a:action t1)(b:action t2)(c:action t3), a <--> b /\ b <--> c -> a <--> c.
Proof.
intros a b c.
dependent inversion a; subst.
dependent inversion b; subst.
dependent inversion c; subst.
all: intros H; destruct H as [H H']; inversion H; inversion H'.
all: try contradiction.
all: first [(simpl in H1; destruct a1; contradiction)|idtac].
all: first [(simpl in H0; destruct a0; contradiction)| idtac].
- left; eauto with act.
- right;  eauto with act.
- destruct a2. right. destruct H1. split; eauto with act.
- destruct c; try (simpl in H1; destruct a1; contradiction); right; eauto with act.
- destruct c; try contradiction.
  + left. eauto with act.
  + right. eauto with act.
  + destruct a2;  right; split; destruct H1 as [[H1ll | H1lR] H1r]; eauto with act.
- destruct a1. inversion c; subst; destruct H0 as [H0l H0r]; 
  destruct c; try inversion H1; right; destruct a1; split;apply (infer_matches_eq i i0 o o0 tid tid0 e e0) in H1; destruct H1 as [H1l [H1m H1r]]; eauto with act.
- destruct a1. destruct c; try inversion H1.
  + destruct H0 as [H0l H0r], H1 as [H1l H1r]. left. eauto with act.
  + destruct H0 as [H0l H0r], H1 as [[H1l1 | H1l2] H1r], H2 as [H21 | H22]; right; eauto with act.
  + destruct a1. destruct H0 as [H0l H0r], H1 as [H1l [H1ml [H1mr H1r]]]. right. split; eauto with act.
- destruct c; destruct b; try ( simpl in H0; destruct a0; contradiction); try (simpl in H1; destruct a2; contradiction).
  + left. eauto with act.
- destruct b; destruct c; 
  try contradiction; 
  try (simpl in H0; destruct a0; contradiction); 
  try ( destruct a2; simpl in H0; destruct a0; contradiction).
  + right. eauto with act.
  + right. eauto with act.
  + destruct a2. destruct H1 as [[H1l1 | H1l2] H1r ]; right; split; try eauto with act.
- destruct b; destruct c; try contradiction; try (simpl in H1; destruct a1; contradiction).
  + right. eauto with act. 
  + right. eauto with act.
  + right. destruct a1. destruct a2. destruct H0 as [[H0l1 | H0l2] H0r]; apply (infer_matches_eq i i0 o o0 tid tid0 e e0) in H1; split;
    try (destruct H1 as [H1l [H1m H1r]]; eauto with act);
    try (right; destruct H1 as [H1l [H1m H1r]]; eauto with act).
- destruct b; destruct c; try contradiction; try (destruct a1; contradiction).
  + right; eauto with act.
  + destruct a2. destruct H1 as [H1l H1r].
    right. split.
    * right. eauto with act.
    * eauto with act.
  + right. eauto with act.
  + right. eauto with act.
  + destruct a2. destruct H1 as [[H1l1 | H1l2] H1r]; right; split; try (eauto with act); try (right; eauto with act).
  + destruct a1. destruct H0 as [[H0l1 | H0l2] H0r], H1 as [H1l H1r]; right; eauto with act.
  + destruct a1. destruct H1 as [[H1l1 | H1l2] H1r], H0 as [[H0l1 | H0l2] H0r]; right; eauto with act.
  + destruct a1, a2. intuition; right; split; try (eauto with act); try (right; eauto with act).
- destruct b; try (simpl in H0; destruct a0; contradiction);
  destruct c; try (simpl in H1; destruct a1; contradiction).
  left; eauto with act.
- destruct b; try (simpl in H0; destruct a0; contradiction).
  destruct a1. destruct c; try contradiction.
  + intuition. destruct a0. apply (infer_matches_eq i0 i o0 o tid0 tid e0 e) in H0; intuition.
    right. split; eauto with act.
  + intuition. destruct a0. apply (infer_matches_eq i0 i o0 o tid0 tid e0 e) in H0; intuition.
    right. split. 
    * right. eauto with act.
    * eauto with act.
    * destruct a0. apply (infer_matches_eq i0 i o0 o tid0 tid e0 e) in H0. intuition.
      right. split.
      ** right. eauto with act.
      ** eauto with act.
  + destruct a1. destruct a0. intuition. apply (infer_matches_eq i1 i o1 o tid1 tid e1 e) in H0. intuition.
    right.
    repeat (split; eauto with act).
- destruct a0; destruct b; destruct c; intuition; try (simpl in H1; destruct a0; contradiction).
  + right; repeat (split; eauto with act).
  + right. split. left; eauto with act. eauto with act.
  + right. split.
    * right; eauto with act.
    * eauto with act.
  + right. destruct a0; destruct a1. apply (infer_matches_eq i0 i1 o0 o1 tid0 tid1 e0 e1) in H1. intuition; eauto with act.
- destruct a0, b, c; try contradiction;
   try (destruct a0; contradiction).  
  + right. intuition.
    * right; eauto with act.
    * eauto with act.
  + destruct a1. right.
    intuition; eauto with act.
  + right; intuition; eauto with act.
  + right. intuition; eauto with act.
  + destruct a1; right; intuition; eauto with act.
  + destruct a0; right; intuition; eauto with act.
  + destruct a0; right; intuition; eauto with act.
  + destruct a0; destruct a1; right; intuition; eauto with act.
- destruct b; try (simpl in H0; destruct a0; contradiction).
  destruct c; try (simpl in H1; destruct a1; contradiction).
  left; eauto with act.
- destruct b; try (simpl in H0; destruct a0; contradiction).
- destruct b; try (simpl in H0; destruct a0; contradiction).
  destruct c; try (simpl in H1; destruct a1; contradiction).
  left; eauto with act.
- destruct b; try (simpl in H0; destruct a0; contradiction).
Qed.






