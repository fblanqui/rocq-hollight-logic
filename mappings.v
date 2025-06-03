Require Import HOLLight_Real_With_N.mappings HOLLight.mappings HOLLight_Logic1.mappings.
Require Import Coq.NArith.BinNat.
Require Import Reals.
From Equations Require Import Equations.
Require Import Coq.Lists.List.

Set Bullet Behavior "Strict Subproofs".

Require Import HOLLight_Logic1.make_opam.

Instance WF_CALLORDER : WellFounded CALLORDER := thm_WF_CALLORDER.

Tactic Notation "exist" uconstr(x1) uconstr(x2) :=
  exists x1 ; exists x2.
Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) :=
  exists x1 ; exists x2 ; exists x3.
Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4.
Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4 ; exists x5.

Definition EMI := ClassicalEpsilon.excluded_middle_informative.

Definition istriv_with_witness env n t : {istriv env n t = TT} + {istriv env n t = FF} +
  {istriv env n t = Exception}.
Proof. destruct (istriv env n t) ; auto. Defined.

Lemma length_lengthN_equality_eq {A : Type} (l l' : list A) :
  (length l = length l') = (lengthN l = lengthN l').
Proof.
  do 2 rewrite <- length_of_nat_N. apply prop_ext ; intro H.
  now rewrite H. now apply Nnat.Nat2N.inj.
Qed.

Lemma length_lengthN_gt_eq {A : Type} (l l' : list A) :
  (length l > length l')%nat = (lengthN l > lengthN l').
Proof.
  do 2 rewrite <- length_of_nat_N.
  unfold N.gt. rewrite <- Nnat.Nat2N.inj_compare.
  apply prop_ext ; apply Compare_dec.nat_compare_gt.
Qed.

Require Import Classical_sets.

Lemma FINITE_Singleton {A : Type'} (x : A) : FINITE (Singleton x).
Proof.
  rewrite FINITE_eq_finite. rewrite Singleton_from_Empty. right. left.
Qed.

Fixpoint rm_dup {A : Type'} (l : list A) :=
  match l with
  | nil => nil
  | a::l => let l':= rm_dup l in COND (List.In a l) l' (a::l') end.

Lemma CARD_by_list {A : Type'} (E : Ensemble A) (l : list A) :
  set_of_list l = E -> CARD E = lengthN (rm_dup l).
Proof.
  intros H. rewrite <- H. clear H. induction l.
  - simpl. rewrite thm_CARD_EQ_0. reflexivity. rewrite FINITE_eq_finite. left.
  - simpl. rewrite (proj2 thm_CARD_CLAUSES).
    do 2 apply COND_intro ; intros H H'.
    + exact IHl.
    + rewrite thm_IN_SET_OF_LIST in H'. destruct (H H').
    + rewrite <- thm_IN_SET_OF_LIST in H. destruct (H' H).
    + simpl. now f_equal.
    + apply thm_FINITE_SET_OF_LIST.
Qed.

Lemma Union_comm {A : Type} (E1 E2 : Ensemble A) :
  Union E1 E2 = Union E2 E1.
Proof.
  ext a. apply prop_ext ; intro H ; destruct H ; (try now left) ; now right.
Qed.

Lemma Union_assoc {A : Type} (E1 E2 E3 : Ensemble A) :
  Union (Union E1 E2) E3 = Union E1 (Union E2 E3).
Proof.
  ext a. apply prop_ext ; intro H ; destruct H.
  - destruct H. now left. right. now left.
  - right. now right.
  - left. now left.
  - destruct H. left. all : now right.
Qed.

Lemma CARD_Union_min_l {A : Type'} (E1 E2 : Ensemble A) :
  FINITE E1 -> FINITE E2 -> CARD E1 <= CARD (Union E1 E2).
Proof.
  intros H1 H2. apply thm_CARD_SUBSET. split.
  apply thm_SUBSET_UNION. now apply thm_FINITE_UNION_IMP.
Qed.

Lemma CARD_Union_min_r {A : Type'} (E1 E2 : Ensemble A) :
  FINITE E1 -> FINITE E2 -> CARD E2 <= CARD (Union E1 E2).
Proof.
  intros H1 H2. apply thm_CARD_SUBSET. split.
  apply thm_SUBSET_UNION. now apply thm_FINITE_UNION_IMP.
Qed.

Lemma FINITE_lUmapfvt : forall l, FINITE (list_Union (map free_variables_term l)).
Proof.
  induction l. rewrite FINITE_eq_finite. left.
  apply thm_FINITE_UNION_IMP. split;auto.
  apply thm_FVT_FINITE.
Qed.

Ltac le_refl := match goal with |- ?a <= ?b => replace b with a ; try reflexivity end.

Equations? unify (c :list (N*term) * list (term * term)) : 
  option (list (N*term)) by wf c CALLORDER :=
  unify (env,_) with EMI (LOOPFREE env) => {
    unify _ (right _ H) => None;
    unify (env,nil) _ => Some env;
    unify (env , (V n , t') :: eqs) _
    with EMI (List.In n (map fst env)) => {
      unify (env , (V n , t') :: eqs) (left _ H) (left _ H') =>
        unify (env , (assoc n env , t') :: eqs);
      unify (env , (V n , t') :: eqs) (left _ H) (right _ H')
      with istriv_with_witness env n t' => {
        | inright _ H'' => None;
        | inleft _ (left _ H'') => unify (env,eqs);
        | inleft _ (right _ H'') => unify ((n,t') :: env , eqs)}};
    unify (env , (Fn n l , V n') :: eqs) (left _ H) =>
      unify (env , (V n' , Fn n l) :: eqs);
    unify (env , (Fn n l , Fn n' l') :: eqs) (left _ H)
    with EMI (n = n' /\ length l = length l') => {
      | right _ _ => None;
      | left _ H' => unify (env , zip l l' ++ eqs)}}.
Proof.
  1,2,4,5 : right ; repeat split ; auto.
  1,2 : right ; left ; exist n t' eqs ; auto.
  - right. right. exist n' n l eqs. auto.
  - left. exist n' l l' eqs. rewrite <- length_lengthN_equality_eq. auto.
  - left. unfold MEASURE. unfold MLEFT. simpl.
    let E1 := fresh "E1" in
    match goal with |- _ < CARD (Union (Union ?sn ?e1)
      (Union (Union ?e3 ?e2) (Union ?e4 ?e5))) - CARD ?e5 =>
      remember e1 as E1 ; remember e2 as E2 ; remember e3 as E3 ;
      remember e4 as E4 ; remember e5 as E5 ; remember sn as Sn end.
    assert (FE1 : FINITE E1). rewrite HeqE1. apply FINITE_lUmapfvt.
    assert (FE2 : FINITE E2). rewrite HeqE2. apply FINITE_lUmapfvt.
    assert (FE3 : FINITE E3). rewrite HeqE3. apply thm_FVT_FINITE.
    assert (FE4 : FINITE E4). rewrite HeqE4. apply FINITE_lUmapfvt.
    assert (FE5 : FINITE E5). rewrite HeqE5. apply FINITE_lUmapfvt.
    assert (FSn : FINITE Sn). rewrite HeqSn. apply FINITE_Singleton.
    assert (H'0 : ~ IN n E5). intro H1. rewrite HeqE5 in H1.
      rewrite thm_IN_LIST_UNION in H1. unfold Basics.compose in H1.
      rewrite <- (map_map fst V) in H1. induction (map fst env). inversion H1.
      inversion_clear H1. contradiction H'. left. now destruct H0.
      apply IHl ; auto. intro Hf. apply H'. now right.
    replace (CARD (Ensembles.Union Sn E5)) with (CARD E5 + 1).
    match goal with |- ?n - _ < ?m - _ => replace m with n end.
    + rewrite N.sub_add_distr. apply N.sub_lt.
      2 : exact N.lt_0_1.
      assert (Sn_E5 : CARD (Intersection Sn E5) = 0).
        match goal with |- CARD ?a = 0 => replace a with (Empty_set (U := N)) end.
        rewrite thm_CARD_EQ_0. reflexivity. rewrite FINITE_eq_finite. left.
        ext k. apply prop_ext ; intro H0 ; destruct H0.
        rewrite HeqSn in H0. destruct H0. destruct (H'0 H1).
      transitivity (CARD (Ensembles.Union Sn E5) - CARD E5).
      * le_refl. rewrite thm_CARD_UNION_GEN.
        match goal with |- _ = _ - ?a - _ => replace a with 0 end.
        rewrite <- N.add_sub_assoc. rewrite <- N.add_sub_assoc.
        match goal with |- _ = _ + ?a => replace a with 0 end.
        rewrite N.add_0_r. replace Sn with (INSERT n Ensembles.Empty_set).
        rewrite thm_CARD_SING. reflexivity. now rewrite HeqSn , Singleton_from_Empty.
        generalize (CARD E5) as k. apply N.peano_ind. auto.
        intros k IHk. rewrite succ_eq_add_1. rewrite N.add_comm at 1.
        rewrite N.sub_add_distr. rewrite <- N.add_sub_assoc.
        rewrite <- N.add_sub_assoc. now rewrite Nadd_sub. now rewrite N.sub_0_r.
        apply N.le_0_l. now rewrite N.sub_0_r. apply N.le_0_l. auto.
      * apply N.sub_le_mono_r. do 2 rewrite <- Union_assoc.
        apply CARD_Union_min_r. apply thm_FINITE_UNION_IMP.
        split ; apply thm_FINITE_UNION_IMP ; auto.
        apply thm_FINITE_UNION_IMP. auto.
    + rewrite (Union_assoc E3). rewrite <- (Union_assoc E4).
      rewrite (Union_comm E4). rewrite (Union_assoc Sn).
      rewrite <- (Union_assoc E3). rewrite (Union_comm E3).
      do 2 rewrite <- (Union_assoc E2). rewrite (Union_comm E2).
      rewrite (Union_assoc Sn). rewrite (Union_comm E2).
      do 2 rewrite <- (Union_assoc E1). rewrite (Union_comm E1).
      now rewrite (Union_assoc (Union Sn E1)).
    + rewrite HeqSn. rewrite Singleton_from_Empty.
      fold (INSERT n Empty_set). rewrite <- thm_lemma.
      rewrite (proj2 thm_CARD_CLAUSES) ; auto.
      apply COND_intro. intro H0. destruct (H'0 H0).
      intros _. apply N.add_1_r.
Qed.

Ltac COND_True := let H := fresh in
  apply COND_intro ; [intro H | intro H ; contradiction H ] ; auto.

Ltac COND_False := let H := fresh in
  apply COND_intro ; [intro H ; apply (absurd _ H) | intro H ] ; auto.

Lemma unify_def : unify = (@ε ((prod N (prod N (prod N (prod N N)))) -> (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term))) (fun unify' : (prod N (prod N (prod N (prod N N)))) -> (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term)) => forall _268410 : prod N (prod N (prod N (prod N N))), forall pr : prod (list (prod N term)) (list (prod term term)), (unify' _268410 pr) = (@COND (option (list (prod N term))) (~ (LOOPFREE (@fst (list (prod N term)) (list (prod term term)) pr))) (@None (list (prod N term))) (@COND (option (list (prod N term))) ((@snd (list (prod N term)) (list (prod term term)) pr) = (@nil (prod term term))) (@Some (list (prod N term)) (@fst (list (prod N term)) (list (prod term term)) pr)) (@tpcases (option (list (prod N term))) (fun f : N => fun fargs : list term => fun g : N => fun gargs : list term => @COND (option (list (prod N term))) ((f = g) /\ ((@lengthN term fargs) = (@lengthN term gargs))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@app (prod term term) (@zip term term fargs gargs) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@None (list (prod N term)))) (fun x : N => fun t : term => @COND (option (list (prod N term))) (@List.In N x (@List.map (prod N term) N (@fst N term) (@fst (list (prod N term)) (list (prod term term)) pr))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@cons (prod term term) (@pair term term (@assoc N term x (@fst (list (prod N term)) (list (prod term term)) pr)) t) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@COND (option (list (prod N term))) ((istriv (@fst (list (prod N term)) (list (prod term term)) pr) x t) = Exception) (@None (list (prod N term))) (@COND (option (list (prod N term))) ((istriv (@fst (list (prod N term)) (list (prod term term)) pr) x t) = TT) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr)))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@cons (prod N term) (@pair N term x t) (@fst (list (prod N term)) (list (prod term term)) pr)) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))))) (fun f : N => fun args : list term => fun x : N => unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@cons (prod term term) (@pair term term (V x) (Fn f args)) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@mappings.hd (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr)))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0))))))))))))).
Proof.
  align_ε'.
  - intros (env,eqs). funelim (unify (env,eqs)).
    3 : COND_True. 
    all : COND_False.
    COND_True.
    all : COND_False ; try discriminate ; unfold tpcases ; simpl.
    1,5 : COND_True.
    2-5 : COND_False.
    2-4 : rewrite H''.
    2,3 : COND_False ; try discriminate.
    2,4 : COND_True.
    1,3 : now rewrite <- length_lengthN_equality_eq.
    COND_False. discriminate.
  - intros g _ Hg. ext (env,eqs). funelim (unify (env,eqs)) ;
    rewrite Hg ; (try match goal with H : _ |- _ =>
      specialize (H g Hg) as H ; match type of H with _ = ?b =>
        transitivity b ; auto end end) ; (* rewrite is not working for some reason *)
        clear Hg.
    3 : COND_True. 
    all : COND_False.
    COND_True.
    all : COND_False ; try discriminate ; unfold tpcases ; simpl.
    1,5 : COND_True.
    2-5 : COND_False.
    2-4 : rewrite H''.
    2,3 : COND_False ; try discriminate.
    2,4 : COND_True.
    1,3 : now rewrite <- length_lengthN_equality_eq.
    COND_False. discriminate.
Qed.

Definition unifies v l := Forall (fun c => termsubst v (fst c) = termsubst v (snd c)) l.

Lemma unifies_def : unifies = (fun _268411 : N -> term => fun _268412 : list (prod term term) => @List.Forall (prod term term) (@ε ((prod term term) -> Prop) (fun f : (prod term term) -> Prop => forall s : term, forall t : term, @eq Prop (f (@pair term term s t)) ((termsubst _268411 s) = (termsubst _268411 t)))) _268412).
Proof.
  ext v l. unfold unifies. f_equal.
  align_ε'. reflexivity.
  intros f' H H'. ext (t,t'). now rewrite H'.
Qed.

Inductive is_Some (A : Type) : option A -> Prop :=
  is_Some_def : forall a, is_Some A (Some a).

Inductive is_None (A : Type) : option A -> Prop :=
  is_None_def : is_None A None.

Lemma Some_None_cover (A : Type) : forall a : option A, is_Some A a \/ is_None A a.
Proof.
  induction a.
  left. exact (is_Some_def A a). right. exact (is_None_def A).
Qed.

Definition on_Some (A : Type) :=
{| case := is_Some A ; negcase := is_None A ; cover_proof := Some_None_cover A |}.

Definition THE {_211969 : Type'} : (option _211969) -> _211969 := @ε ((prod N (prod N N)) -> (option _211969) -> _211969) (fun THE' : (prod N (prod N N)) -> (option _211969) -> _211969 => forall _274433 : prod N (prod N N), forall x : _211969, (THE' _274433 (@Some _211969 x)) = x) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))).

Definition the {A : Type'} (x : option A) :=
  match x with None => THE None | Some a => a end.

Lemma THE_def {_211969 : Type'} : (@the _211969) = (@ε ((prod N (prod N N)) -> (option _211969) -> _211969) (fun THE' : (prod N (prod N N)) -> (option _211969) -> _211969 => forall _274433 : prod N (prod N N), forall x : _211969, (THE' _274433 (@Some _211969 x)) = x) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))).
Proof. partial_align (on_Some _211969). Qed.

Definition unifier l := fold_right valmod V (SOLVE nil l).

Lemma unifier_def : unifier = (fun _274434 : list (prod N term) => @Basics.apply (list (prod N term)) (N -> term) (fun sol : list (prod N term) => @Datatypes.id (N -> term) (@fold_right_with_perm_args (prod N term) (N -> term) (@valmod term N) sol V)) (SOLVE (@nil (prod N term)) _274434)).
Proof. exact (eq_refl unifier). Qed.

Definition Unifies subst E := forall f f' : form,
  IN f E /\ IN f' E -> formsubst subst f = formsubst subst f'.

Lemma Unifies_def : Unifies = (fun _275904 : N -> term => fun _275905 : form -> Prop => forall p : form, forall q : form, ((@IN form p _275905) /\ (@IN form q _275905)) -> (formsubst _275904 p) = (formsubst _275904 q)).
Proof. exact (eq_refl Unifies). Qed.

Definition mgu : (form -> Prop) -> N -> term := fun _276282 : form -> Prop => @ε (N -> term) (fun i : N -> term => (Unifies i _276282) /\ (forall j : N -> term, (Unifies j _276282) -> forall p : form, (qfree p) -> (formsubst j p) = (formsubst j (formsubst i p)))).

Lemma mgu_def : mgu = (fun _276282 : form -> Prop => @ε (N -> term) (fun i : N -> term => (Unifies i _276282) /\ (forall j : N -> term, (Unifies j _276282) -> forall p : form, (qfree p) -> (formsubst j p) = (formsubst j (formsubst i p))))).
Proof. exact (eq_refl mgu). Qed.

Definition ismgu E subst :=
  Unifies subst E /\
  (forall subst' : N -> term, Unifies subst' E ->
  exists subst'' : N -> term, termsubst subst' = Basics.compose (termsubst subst'') (termsubst subst)).

Lemma ismgu_def : ismgu = (fun _276290 : form -> Prop => fun _276291 : N -> term => (Unifies _276291 _276290) /\ (forall j : N -> term, (Unifies j _276290) -> exists k : N -> term, (termsubst j) = (@Basics.compose term term term (termsubst k) (termsubst _276291)))).
Proof. exact (eq_refl ismgu). Qed.

Definition renaming (subst : N -> term) :=
  exists subst' : N -> term, forall t,
  (termsubst subst' (termsubst subst t)) = t /\
  (termsubst subst (termsubst subst' t)) = t.

Lemma renaming_def : renaming = (fun _276319 : N -> term => exists j : N -> term, ((@Basics.compose term term term (termsubst j) (termsubst _276319)) = (@Datatypes.id term)) /\ ((@Basics.compose term term term (termsubst _276319) (termsubst j)) = (@Datatypes.id term))).
Proof.
  ext subst. apply prop_ext ; intros (subst' , H) ; exists subst'.
  - split ; apply fun_ext ; apply H.
  - intro t ; split ; revert t ; apply ext_fun ; apply H.
Qed.

(*****************************************************************************)
(* Logic/resolution.ml *)
(*****************************************************************************)

Definition atom f := match f with Atom _ _ => True | _ => False end.

Lemma atom_def : atom = (@ε ((prod N (prod N (prod N N))) -> form -> Prop) (fun atom' : (prod N (prod N (prod N N))) -> form -> Prop => forall _276403 : prod N (prod N (prod N N)), ((atom' _276403 FFalse) = False) /\ ((forall p : N, forall l : list term, (atom' _276403 (Atom p l)) = True) /\ ((forall q : form, forall r : form, (atom' _276403 (FImp q r)) = False) /\ (forall x : N, forall q : form, (atom' _276403 (FAll x q)) = False)))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))).
Proof. total_align. Qed.

(* negatomic formulae *)
Definition literal f :=
  match f with
  | Atom _ _ | FImp (Atom _ _) FFalse => True
  | _ => False end.

Lemma literal_def : literal = (fun _276404 : form => (atom _276404) \/ (exists q : form, (atom q) /\ (_276404 = (Not q)))).
Proof.
  ext f. apply prop_ext ; intro H.
  - destruct f;auto. destruct f1 ; destruct f2 ; auto. right.
    now exists (Atom n l).
  - destruct H as [H|(f',(H,e))]. induction f;auto. destruct H. rewrite e.
    now induction f'.
Qed.

(* finite set of negatomic formulae *)
Definition clause c := finite c /\ Included c literal.

Lemma clause_def : clause = (fun _276409 : form -> Prop => (@FINITE form _276409) /\ (forall p : form, (@IN form p _276409) -> literal p)).
Proof.
  ext c. unfold clause.
  now rewrite (FINITE_eq_finite).
Qed.

Inductive negative : form -> Prop := negative_intro : forall f, negative (Not f).
Lemma negative_def : negative = (fun _276554 : form => exists q : form, _276554 = (Not q)).
Proof.
  ext f. apply prop_ext ; intro H. inversion H. now exists f0.
  destruct H as (f',H). rewrite H. exact (negative_intro f').
Qed.

Inductive positive : form -> Prop :=
  | positive_FFalse : positive FFalse
  | positive_Atom : forall n l, positive (Atom n l)
  | positive_FImp : forall f f', f' <> FFalse -> positive (FImp f f')
  | positive_FAll : forall n f, positive (FAll n f).

Lemma positive_def : positive = (fun _276559 : form => ~ (negative _276559)).
Proof.
  ext f. apply prop_ext ; intro H.
  - intro H'. inversion H'. inversion H.
    1,2,4 : rewrite <- H1 in H0 ; inversion H0.
    rewrite <- H2 in H0. injection H0. intro contr.
    now symmetry in contr.
  - destruct f ; try now constructor.
    destruct f2. contradiction H.
    all : now constructor.
Qed.

Definition FNot f := match f with FImp f' FFalse => f' | _ => Not f end.

Lemma FNot_def : FNot = (fun _276564 : form => @COND form (negative _276564) (@ε form (fun q : form => (Not q) = _276564)) (Not _276564)).
Proof.
  ext f. apply COND_intro ; intro H.
  - inversion H. align_ε'. reflexivity.
    intros f' _ H'. now injection H'.
  - destruct f;auto. destruct f2;auto.
    contradiction H. split.
Qed.

Definition resolve f cl cl' := Union (Subtract cl f) (Subtract cl' (FNot f)).

Lemma resolve_def : resolve = (fun _276622 : form => fun _276623 : form -> Prop => fun _276624 : form -> Prop => @Ensembles.Union form (@Ensembles.Subtract form _276623 _276622) (@Ensembles.Subtract form _276624 (FNot _276622))).
Proof. exact (eq_refl resolve). Qed.

Inductive presproof (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | presproof_assumption : forall cl, IN cl hyps -> presproof hyps cl
  | presproof_resolve : forall f cl cl', presproof hyps cl ->
                        presproof hyps cl' -> IN f cl -> IN (FNot f) cl' ->
                        presproof hyps (resolve f cl cl'). 

Lemma presproof_def : presproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall presproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((presproof' cl1) /\ ((presproof' cl2) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2)))))) -> presproof' a') -> presproof' a).
Proof. ext hyps. ind_align'. Qed.

Definition interp cl := fold_right FOr FFalse (list_of_set cl).

Lemma interp_def : interp = (fun _276649 : form -> Prop => @fold_right_with_perm_args form form FOr (@list_of_set form _276649) FFalse).
Proof. exact (eq_refl interp). Qed.

Definition instance_of cl cl' := (exists subst : N -> term, cl = IMAGE (formsubst subst) cl').

Lemma instance_of_def : instance_of = (fun _282937 : form -> Prop => fun _282938 : form -> Prop => exists i : N -> term, _282937 = (@IMAGE form form (formsubst i) _282938)).
Proof. exact (eq_refl instance_of). Qed.

Definition FVS cl := UNIONS (IMAGE free_variables cl).

Lemma FVS_def : FVS = (fun _282949 : form -> Prop => @UNIONS N (@GSPEC (N -> Prop) (fun GEN_PVAR_527 : N -> Prop => exists p : form, @SETSPEC (N -> Prop) GEN_PVAR_527 (@IN form p _282949) (free_variables p)))).
Proof. exact (eq_refl FVS). Qed.

Definition rename : (form -> Prop) -> (N -> Prop) -> N -> term := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> (N -> Prop) -> N -> term) (fun i : (prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> (N -> Prop) -> N -> term => forall _285948 : prod N (prod N (prod N (prod N (prod N N)))), forall cl : form -> Prop, forall s : N -> Prop, ((@FINITE N s) /\ (clause cl)) -> (renaming (i _285948 cl s)) /\ ((@Ensembles.Intersection N (FVS (@IMAGE form form (formsubst (i _285948 cl s)) cl)) s) = (@Ensembles.Empty_set N))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))))).

Lemma rename_def : rename = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> (N -> Prop) -> N -> term) (fun i : (prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> (N -> Prop) -> N -> term => forall _285948 : prod N (prod N (prod N (prod N (prod N N)))), forall cl : form -> Prop, forall s : N -> Prop, ((@FINITE N s) /\ (clause cl)) -> (renaming (i _285948 cl s)) /\ ((@Ensembles.Intersection N (FVS (@IMAGE form form (formsubst (i _285948 cl s)) cl)) s) = (@Ensembles.Empty_set N))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))))).
Proof. exact (eq_refl rename). Qed.

Inductive resproof (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | resproof_assumption : forall cl, IN cl hyps -> resproof hyps cl
  | resproof_rm_opposable :
      forall cl1 cl2 cl2' ps1 ps2 subst, resproof hyps cl1 -> resproof hyps cl2 ->
      IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2' -> Included ps1 cl1 ->
      Included ps2 cl2' -> ps1 <> Empty_set -> ps2 <> Empty_set ->
      (exists subst', Unifies subst' (Union ps1 (IMAGE FNot ps2))) ->
      mgu (Union ps1 (IMAGE FNot ps2)) = subst ->
      resproof hyps (IMAGE (formsubst subst) (Union (Setminus cl1 ps1) (Setminus cl2' ps2))).

Lemma resproof_def : resproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall resproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((resproof' cl1) /\ ((resproof' cl2) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_533 : form => exists p : form, @SETSPEC form GEN_PVAR_533 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_534 : form => exists p : form, @SETSPEC form GEN_PVAR_534 (@IN form p ps2) (FNot p))))) = i))))))))))) -> resproof' a') -> resproof' a).
Proof.
  ext hyps. fastind_align. now left. 
  right. exist cl1 cl2 cl2' ps1 ps2. exists subst.
  repeat split;auto.
  apply (resproof_rm_opposable hyps cl1 cl2) ; auto. now exists i'.
Qed.

Definition isaresolvent cl c := match c with (cl1,cl2) =>
  let y := IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 in
  exists ps1 ps2 : form -> Prop, Included ps1 cl1 /\ Included ps2 y /\
  ps1 <> Empty_set /\ ps2 <> Empty_set /\
  (exists subst : N -> term, Unifies subst (Union ps1 (IMAGE FNot ps2))) /\
  cl = IMAGE (formsubst (mgu (Union ps1 (IMAGE FNot ps2)))) (Union (Setminus cl1 ps1) (Setminus y ps2)) end.

Lemma isaresolvent_def : isaresolvent = (fun _289554 : form -> Prop => fun _289555 : prod (form -> Prop) (form -> Prop) => @Basics.apply (form -> Prop) Prop (fun cl2' : form -> Prop => @Datatypes.id Prop (exists ps1 : form -> Prop, exists ps2 : form -> Prop, (@Ensembles.Included form ps1 (@fst (form -> Prop) (form -> Prop) _289555)) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i : N -> term, Unifies i (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_540 : form => exists p : form, @SETSPEC form GEN_PVAR_540 (@IN form p ps2) (FNot p))))) /\ (@Basics.apply (N -> term) Prop (fun i : N -> term => @Datatypes.id Prop (_289554 = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form (@fst (form -> Prop) (form -> Prop) _289555) ps1) (@Ensembles.Setminus form cl2' ps2))))) (mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_541 : form => exists p : form, @SETSPEC form GEN_PVAR_541 (@IN form p ps2) (FNot p)))))))))))) (@IMAGE form form (formsubst (rename (@snd (form -> Prop) (form -> Prop) _289555) (FVS (@fst (form -> Prop) (form -> Prop) _289555)))) (@snd (form -> Prop) (form -> Prop) _289555))).
Proof. ext cl (cl1,cl2). reflexivity. Qed.

(*****************************************************************************)
(* Logic/given.ml *)
(*****************************************************************************)

Definition FIRSTN {A : Type'} n (l : list A) := firstn (N.to_nat n) l.

Lemma FIRSTN_def {_216234 : Type'} : (@FIRSTN _216234) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> (list _216234) -> list _216234) (fun FIRSTN' : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> (list _216234) -> list _216234 => forall _289585 : prod N (prod N (prod N (prod N (prod N N)))), (forall l : list _216234, (FIRSTN' _289585 (NUMERAL N0) l) = (@nil _216234)) /\ (forall n : N, forall l : list _216234, (FIRSTN' _289585 (N.succ n) l) = (@COND (list _216234) (l = (@nil _216234)) (@nil _216234) (@cons _216234 (@mappings.hd _216234 l) (FIRSTN' _289585 n (@tl _216234 l)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof.
  N_rec_align. intros n l.
  unfold FIRSTN. rewrite Nnat.N2Nat.inj_succ, COND_list.
  now destruct l.
Qed.

Definition tautologous cl := (exists f : form, IN f cl /\ IN (FNot f) cl).

Lemma tautologous_def : tautologous = (fun _290199 : form -> Prop => exists p : form, (@IN form p _290199) /\ (@IN form (FNot p) _290199)).
Proof. exact (eq_refl tautologous). Qed.

Definition subsumes cl cl' := exists subst, Included (IMAGE (formsubst subst) cl) cl'.

Lemma subsumes_def : subsumes = (fun _290204 : form -> Prop => fun _290205 : form -> Prop => exists i : N -> term, @Ensembles.Included form (@IMAGE form form (formsubst i) _290204) _290205).
Proof. exact (eq_refl subsumes). Qed.

Definition SUBSUMES E E' := forall cl', IN cl' E' -> exists cl, IN cl E /\ subsumes cl cl'.

Lemma SUBSUMES_def : SUBSUMES = (fun _290276 : (form -> Prop) -> Prop => fun _290277 : (form -> Prop) -> Prop => forall cl' : form -> Prop, (@IN (form -> Prop) cl' _290277) -> exists cl : form -> Prop, (@IN (form -> Prop) cl _290276) /\ (subsumes cl cl')).
Proof. exact (eq_refl SUBSUMES). Qed.

Definition allresolvents E E' :=
  fun cl => (exists c1 c2 : form -> Prop, IN c1 E /\ IN c2 E' /\ isaresolvent cl (c1, c2)).

Lemma allresolvents_def : allresolvents = (fun _290388 : (form -> Prop) -> Prop => fun _290389 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_542 : form -> Prop => exists c : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_542 (exists c1 : form -> Prop, exists c2 : form -> Prop, (@IN (form -> Prop) c1 _290388) /\ ((@IN (form -> Prop) c2 _290389) /\ (isaresolvent c (@pair (form -> Prop) (form -> Prop) c1 c2)))) c)).
Proof.
  ext E E'. symmetry. exact (SPEC_elim).
Qed.

Definition allntresolvents E E' cl := IN cl (allresolvents E E') /\ ~ tautologous cl.

Lemma allntresolvents_def : allntresolvents = (fun _290400 : (form -> Prop) -> Prop => fun _290401 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_543 : form -> Prop => exists r : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_543 ((@IN (form -> Prop) r (allresolvents _290400 _290401)) /\ (~ (tautologous r))) r)).
Proof.
  ext E E'. symmetry. exact (SPEC_elim).
Qed.

Definition resolvents cl l := list_of_set (allresolvents (Singleton cl) (set_of_list l)).

Lemma resolvents_def : resolvents = (fun _315994 : form -> Prop => fun _315995 : list (form -> Prop) => @list_of_set (form -> Prop) (allresolvents (@INSERT (form -> Prop) _315994 (@Ensembles.Empty_set (form -> Prop))) (@set_of_list (form -> Prop) _315995))).
Proof.
  ext cl l. unfold resolvents. now rewrite Singleton_from_Empty.
Qed.

Fixpoint replace (cl : form -> Prop) l :=
  match l with
  | nil => cl::nil
  | cl'::l' => COND (subsumes cl cl') (cl::l') (cl'::(replace cl l')) end.

Lemma replace_def : replace = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (form -> Prop) -> (list (form -> Prop)) -> list (form -> Prop)) (fun replace' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (form -> Prop) -> (list (form -> Prop)) -> list (form -> Prop) => forall _316246 : prod N (prod N (prod N (prod N (prod N (prod N N))))), (forall cl : form -> Prop, (replace' _316246 cl (@nil (form -> Prop))) = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (forall c : form -> Prop, forall cl : form -> Prop, forall cls : list (form -> Prop), (replace' _316246 cl (@cons (form -> Prop) c cls)) = (@COND (list (form -> Prop)) (subsumes cl c) (@cons (form -> Prop) cl cls) (@cons (form -> Prop) c (replace' _316246 cl cls))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))))))).
Proof. total_align. Qed.

Definition incorporate cl cl' l :=
  COND (tautologous cl' \/ Exists (fun cl0 : form -> Prop => subsumes cl0 cl') (cl :: l)) l
  (replace cl' l).

Lemma incorporate_def : incorporate = (fun _316633 : form -> Prop => fun _316634 : form -> Prop => fun _316635 : list (form -> Prop) => @COND (list (form -> Prop)) ((tautologous _316634) \/ (@List.Exists (form -> Prop) (fun c : form -> Prop => subsumes c _316634) (@cons (form -> Prop) _316633 _316635))) _316635 (replace _316634 _316635)).
Proof. exact (eq_refl incorporate). Qed.

Definition insert {A : Type'} (a : A) l := COND (List.In a l) l (a :: l).

Lemma insert_def {_218810 : Type'} : (@insert _218810) = (fun _316826 : _218810 => fun _316827 : list _218810 => @COND (list _218810) (@List.In _218810 _316826 _316827) _316827 (@cons _218810 _316826 _316827)).
Proof. exact (eq_refl (@insert _218810)). Qed.

Definition step c :=
  match snd c with
  | nil => c
  | a::l' => (insert a (fst c), fold_right (incorporate a) l' (resolvents a (a :: (fst c)))) end.

Lemma step_def : step = (fun _316838 : prod (list (form -> Prop)) (list (form -> Prop)) => @COND (prod (list (form -> Prop)) (list (form -> Prop))) ((@snd (list (form -> Prop)) (list (form -> Prop)) _316838) = (@nil (form -> Prop))) (@pair (list (form -> Prop)) (list (form -> Prop)) (@fst (list (form -> Prop)) (list (form -> Prop)) _316838) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838)) (@Basics.apply (list (form -> Prop)) (prod (list (form -> Prop)) (list (form -> Prop))) (fun new : list (form -> Prop) => @Datatypes.id (prod (list (form -> Prop)) (list (form -> Prop))) (@pair (list (form -> Prop)) (list (form -> Prop)) (@insert (form -> Prop) (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838)) (@fst (list (form -> Prop)) (list (form -> Prop)) _316838)) (@fold_right_with_perm_args (form -> Prop) (list (form -> Prop)) (incorporate (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838))) new (@tl (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838))))) (resolvents (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838)) (@cons (form -> Prop) (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838)) (@fst (list (form -> Prop)) (list (form -> Prop)) _316838))))).
Proof.
  ext (l,l'). rewrite COND_list. now destruct l'.
Qed.

Fixpoint given n p :=
  match n with
  | O => p
  | S n => step (given n p) end.

Definition giveN n := given (N.to_nat n).

Lemma given_def : giveN = (@ε ((prod N (prod N (prod N (prod N N)))) -> N -> (prod (list (form -> Prop)) (list (form -> Prop))) -> prod (list (form -> Prop)) (list (form -> Prop))) (fun given' : (prod N (prod N (prod N (prod N N)))) -> N -> (prod (list (form -> Prop)) (list (form -> Prop))) -> prod (list (form -> Prop)) (list (form -> Prop)) => forall _316850 : prod N (prod N (prod N (prod N N))), (forall p : prod (list (form -> Prop)) (list (form -> Prop)), (given' _316850 (NUMERAL N0) p) = p) /\ (forall n : N, forall p : prod (list (form -> Prop)) (list (form -> Prop)), (given' _316850 (N.succ n) p) = (step (given' _316850 n p)))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))).
Proof.
  N_rec_align. intros. unfold giveN. now rewrite (Nnat.N2Nat.inj_succ).
Qed.

Definition Used init n := set_of_list (fst (giveN n init)).
Definition Unused init n := set_of_list (snd (giveN n init)).

Lemma Used_def : Used = (fun _316851 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _316852 : N => @set_of_list (form -> Prop) (@fst (list (form -> Prop)) (list (form -> Prop)) (giveN _316852 _316851))).
Proof. exact (eq_refl Used). Qed.
Lemma Unused_def : Unused = (fun _316863 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _316864 : N => @set_of_list (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN _316864 _316863))).
Proof. exact (eq_refl Unused). Qed.

Fixpoint Subnat init n := 
  match n with
  | O => Empty_set
  | S n => match snd (given n init) with
    | nil => Subnat init n
    | a::l => INSERT a (Subnat init n) end end.

Definition Sub init n : (form -> Prop) -> Prop := Subnat init (N.to_nat n).

Lemma Sub_def0 {A B : Type'} (l : list A) (x : B) f :
  match l with nil => x | a::l' => f a l' end =
  match l with nil => x | a::l' => f (mappings.hd l) (mappings.tl l) end.
Proof. now destruct l. Qed.

Lemma Sub_def : Sub = (@ε ((prod N (prod N N)) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> (form -> Prop) -> Prop) (fun Sub' : (prod N (prod N N)) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> (form -> Prop) -> Prop => forall _316881 : prod N (prod N N), (forall init : prod (list (form -> Prop)) (list (form -> Prop)), (Sub' _316881 init (NUMERAL N0)) = (@Ensembles.Empty_set (form -> Prop))) /\ (forall init : prod (list (form -> Prop)) (list (form -> Prop)), forall n : N, (Sub' _316881 init (N.succ n)) = (@COND ((form -> Prop) -> Prop) ((@snd (list (form -> Prop)) (list (form -> Prop)) (giveN n init)) = (@nil (form -> Prop))) (Sub' _316881 init n) (@INSERT (form -> Prop) (@HOLLight_Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN n init))) (Sub' _316881 init n))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))).
Proof.
  N_rec_align.
  intros init n. rewrite COND_list. unfold Sub.
  rewrite Nnat.N2Nat.inj_succ. unfold giveN. simpl.
  apply (Sub_def0 (snd (given (N.to_nat n) init))).
Qed.

Fixpoint breaknat init n :=
  match n with
  | O => lengthN (snd init)
  | S n => let k := breaknat init n in
           k + lengthN (snd (giveN k init)) end.

Definition break init n := breaknat init (N.to_nat n).

Lemma break_def : break = (@ε ((prod N (prod N (prod N (prod N N)))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> N) (fun break' : (prod N (prod N (prod N (prod N N)))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> N => forall _328646 : prod N (prod N (prod N (prod N N))), (forall init : prod (list (form -> Prop)) (list (form -> Prop)), (break' _328646 init (NUMERAL N0)) = (@lengthN (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN (NUMERAL N0) init)))) /\ (forall n : N, forall init : prod (list (form -> Prop)) (list (form -> Prop)), (break' _328646 init (N.succ n)) = (N.add (break' _328646 init n) (@lengthN (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN (break' _328646 init n) init)))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))).
Proof.
  N_rec_align.
  intros. unfold break. now rewrite Nnat.N2Nat.inj_succ.
Qed.

Definition level init n := Sub init (break init n).

Lemma level_def : level = (fun _328647 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _328648 : N => Sub _328647 (break _328647 _328648)).
Proof. exact (eq_refl level). Qed.

(*****************************************************************************)
(* Logic/linear.ml *)
(*****************************************************************************)

Inductive ppresproof : Ensemble (Ensemble form) -> Ensemble form -> Prop :=
  | ppresproof_assumption : forall cl, clause cl -> ppresproof (Singleton cl) cl
  | ppresproof_resolve : forall f hyps hyps' cl cl', ppresproof hyps cl ->
                        ppresproof hyps' cl' -> IN f cl -> IN (FNot f) cl' ->
                        ppresproof (Union hyps hyps') (resolve f cl cl').

Lemma ppresproof_def : ppresproof = (fun a0 : (form -> Prop) -> Prop => fun a1 : form -> Prop => forall ppresproof' : ((form -> Prop) -> Prop) -> (form -> Prop) -> Prop, (forall a0' : (form -> Prop) -> Prop, forall a1' : form -> Prop, (((a0' = (@INSERT (form -> Prop) a1' (@Ensembles.Empty_set (form -> Prop)))) /\ (clause a1')) \/ (exists p : form, exists asm1 : (form -> Prop) -> Prop, exists asm2 : (form -> Prop) -> Prop, exists c1 : form -> Prop, exists c2 : form -> Prop, (a0' = (@Ensembles.Union (form -> Prop) asm1 asm2)) /\ ((a1' = (resolve p c1 c2)) /\ ((ppresproof' asm1 c1) /\ ((ppresproof' asm2 c2) /\ ((@IN form p c1) /\ (@IN form (FNot p) c2))))))) -> ppresproof' a0' a1') -> ppresproof' a0 a1).
Proof.
  ind_align'.
  - left. split. exact (Singleton_from_Empty cl). exact H.
  - unfold INSERT. rewrite <- Singleton_from_Empty.
    now left.
Qed.


Inductive lpresproof (hyps : Ensemble (Ensemble form)) : list (Ensemble form) -> Prop :=
  | lpresproof_assumption : forall cl, IN cl hyps -> lpresproof hyps (cl::nil)
  | lpresproof_resolve : forall f cl cl' l, lpresproof hyps (cl::l) ->
                        (IN cl' hyps \/ List.In cl' l) -> IN f cl -> IN (FNot f) cl' ->
                        lpresproof hyps ((resolve f cl cl')::cl::l).

Lemma lpresproof_def : lpresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : list (form -> Prop) => forall lpresproof' : (list (form -> Prop)) -> Prop, (forall a' : list (form -> Prop), ((exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (@IN (form -> Prop) cl hyps')) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists lis : list (form -> Prop), exists p : form, (a' = (@cons (form -> Prop) (resolve p c1 c2) (@cons (form -> Prop) c1 lis))) /\ ((lpresproof' (@cons (form -> Prop) c1 lis)) /\ (((@IN (form -> Prop) c2 hyps') \/ (@List.In (form -> Prop) c2 lis)) /\ ((@IN form p c1) /\ (@IN form (FNot p) c2)))))) -> lpresproof' a') -> lpresproof' a).
Proof.
  ext hyps. ind_align'.
Qed.

Fixpoint suffix {A : Type} (l : list A) l' :=
  match l' with
  | nil => l = nil
  | _::l'0  => l = l' \/ suffix l l'0 end.

Lemma suffix_def {_224872 : Type'} : (@suffix _224872) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list _224872) -> (list _224872) -> Prop) (fun suffix' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list _224872) -> (list _224872) -> Prop => forall _374747 : prod N (prod N (prod N (prod N (prod N N)))), (forall lis : list _224872, (suffix' _374747 lis (@nil _224872)) = (lis = (@nil _224872))) /\ (forall s : _224872, forall lis : list _224872, forall cs : list _224872, (suffix' _374747 lis (@cons _224872 s cs)) = ((lis = (@cons _224872 s cs)) \/ (suffix' _374747 lis cs)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))))))))).
Proof. total_align2. Qed.

Inductive lresproof (hyps : Ensemble (Ensemble form)) : list (Ensemble form) -> Prop :=
  | lresproof_assumption : forall cl, IN cl hyps -> lresproof hyps (cl::nil)
  | lresproof_resolve : forall cl0 cl cl' l, lresproof hyps (cl::l) ->
                        (IN cl' hyps \/ List.In cl' l) -> isaresolvent cl0 (cl,cl') ->
                        lresproof hyps (cl0::cl::l).

Lemma lresproof_def : lresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : list (form -> Prop) => forall lresproof' : (list (form -> Prop)) -> Prop, (forall a' : list (form -> Prop), ((exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (@IN (form -> Prop) cl hyps')) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists lis : list (form -> Prop), exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@cons (form -> Prop) c1 lis))) /\ ((lresproof' (@cons (form -> Prop) c1 lis)) /\ (((@IN (form -> Prop) c2 hyps') \/ (@List.In (form -> Prop) c2 lis)) /\ (isaresolvent cl (@pair (form -> Prop) (form -> Prop) c1 c2)))))) -> lresproof' a') -> lresproof' a).
Proof.
  ext hyps. ind_align' ; apply (lresproof_resolve _ _ _ c2) ; auto.
Qed.

(*****************************************************************************)
(* Logic/support.ml *)
(*****************************************************************************)

Inductive npresproof (hyps : Ensemble (Ensemble form)) : Ensemble form -> N -> Prop :=
  | npresproof_assumption : forall cl, IN cl hyps -> npresproof hyps cl 1
  | npresproof_resolve : forall f cl cl' n n', npresproof hyps cl n ->
                        npresproof hyps cl' n' -> IN f cl -> IN (FNot f) cl' ->
                        npresproof hyps (resolve f cl cl') (n+n'+1).

Lemma npresproof_def : npresproof = (fun hyps' : (form -> Prop) -> Prop => fun a0 : form -> Prop => fun a1 : N => forall npresproof' : (form -> Prop) -> N -> Prop, (forall a0' : form -> Prop, forall a1' : N, (((a1' = (NUMERAL (BIT1 N0))) /\ (@IN (form -> Prop) a0' hyps')) \/ (exists p : form, exists n1 : N, exists n2 : N, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a0' = (resolve p cl1 cl2)) /\ ((a1' = (N.add n1 (N.add n2 (NUMERAL (BIT1 N0))))) /\ ((npresproof' cl1 n1) /\ ((npresproof' cl2 n2) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> npresproof' a0' a1') -> npresproof' a0 a1).
Proof.
  ext hyps. ind_align'.
  - right. exists f. exists n. exists n'. exists cl. exists cl'.
    repeat split;auto. now rewrite N.add_assoc.
  - rewrite N.add_assoc. now right.
Qed.

Inductive psresproof (hyps sos : Ensemble (Ensemble form)) : Prop -> Ensemble form -> Prop :=
  | psresproof_assumption : forall cl, IN cl hyps -> ~ tautologous cl ->
                            psresproof hyps sos (IN cl sos) cl
  | psresproof_resolve : forall f cl cl' P P', psresproof hyps sos P cl ->
                        psresproof hyps sos P' cl' -> IN f cl -> IN (FNot f) cl' ->
                        P \/ P' -> ~ tautologous (resolve f cl cl') ->
                        psresproof hyps sos True (resolve f cl cl').

Lemma psresproof_def : psresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a0 : Prop => fun a1 : form -> Prop => forall psresproof' : Prop -> (form -> Prop) -> Prop, (forall a0' : Prop, forall a1' : form -> Prop, (((a0' = (@IN (form -> Prop) a1' sos)) /\ ((@IN (form -> Prop) a1' hyps') /\ (~ (tautologous a1')))) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists s1 : Prop, exists s2 : Prop, exists p : form, (a0' = True) /\ ((a1' = (resolve p c1 c2)) /\ ((psresproof' s1 c1) /\ ((psresproof' s2 c2) /\ ((@IN form p c1) /\ ((@IN form (FNot p) c2) /\ ((s1 \/ s2) /\ (~ (tautologous (resolve p c1 c2))))))))))) -> psresproof' a0' a1') -> psresproof' a0 a1).
Proof.
  ext hyps sos. ind_align' ;
  apply (psresproof_resolve _ _ _ _ _ s1 s2) ; auto.
Qed.

Inductive spresproof (hyps sos : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | spresproof_assumption : forall cl, IN cl hyps -> IN cl sos ->
                            ~ tautologous cl -> spresproof hyps sos cl
  | spresproof_resolve1 : forall f cl cl', spresproof hyps sos cl ->
                        spresproof hyps sos cl' -> IN f cl ->
                        IN (FNot f) cl' -> ~ tautologous (resolve f cl cl') ->
                        spresproof hyps sos (resolve f cl cl')
  | spresproof_resolve2 : forall f cl cl', spresproof hyps sos cl ->
                        IN cl' hyps -> IN f cl ->
                        IN (FNot f) cl' -> ~ tautologous (resolve f cl cl') ->
                        spresproof hyps sos (resolve f cl cl').

Lemma spresproof_def : spresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a : form -> Prop => forall spresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, (((@IN (form -> Prop) a' hyps') /\ ((@IN (form -> Prop) a' sos) /\ (~ (tautologous a')))) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists p : form, (a' = (resolve p c1 c2)) /\ ((spresproof' c1) /\ (((spresproof' c2) \/ (@IN (form -> Prop) c2 hyps')) /\ ((@IN form p c1) /\ ((@IN form (FNot p) c2) /\ (~ (tautologous (resolve p c1 c2))))))))) -> spresproof' a') -> spresproof' a).
Proof.
  ext hyps sos. ind_align'.
Qed.

Inductive sresproof (hyps sos : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | sresproof_assumption : forall cl, IN cl hyps -> IN cl sos ->
    ~ tautologous cl -> sresproof hyps sos cl
  | sresproof_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst, sresproof hyps sos cl1 -> sresproof hyps sos cl2 ->
      IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2' -> Included ps1 cl1 ->
      Included ps2 cl2' -> ps1 <> Empty_set -> ps2 <> Empty_set ->
      (exists subst', Unifies subst' (Union ps1 (IMAGE FNot ps2))) ->
      mgu (Union ps1 (IMAGE FNot ps2)) = subst ->
      ~ tautologous (IMAGE (formsubst subst) (Union (Setminus cl1 ps1) (Setminus cl2' ps2))) ->
      sresproof hyps sos (IMAGE (formsubst subst) (Union (Setminus cl1 ps1) (Setminus cl2' ps2)))
  | sresproof_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst, sresproof hyps sos cl1 -> IN cl2 hyps ->
      IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2' -> Included ps1 cl1 ->
      Included ps2 cl2' -> ps1 <> Empty_set -> ps2 <> Empty_set ->
      (exists subst', Unifies subst' (Union ps1 (IMAGE FNot ps2))) ->
      mgu (Union ps1 (IMAGE FNot ps2)) = subst ->
      ~ tautologous (IMAGE (formsubst subst) (Union (Setminus cl1 ps1) (Setminus cl2' ps2))) ->
      sresproof hyps sos (IMAGE (formsubst subst) (Union (Setminus cl1 ps1) (Setminus cl2' ps2))).

Lemma sresproof_def : sresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a : form -> Prop => forall sresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, (((@IN (form -> Prop) a' hyps') /\ ((@IN (form -> Prop) a' sos) /\ (~ (tautologous a')))) \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((sresproof' cl1) /\ (((sresproof' cl2) \/ (@IN (form -> Prop) cl2 hyps')) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_589 : form => exists p : form, @SETSPEC form GEN_PVAR_589 (@IN form p ps2) (FNot p))))) /\ (((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_590 : form => exists p : form, @SETSPEC form GEN_PVAR_590 (@IN form p ps2) (FNot p))))) = i) /\ (~ (tautologous (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))))))))))))))) -> sresproof' a') -> sresproof' a).
Proof.
  ext hyps sos. fastind_align.
  2,3 : right ; exist cl1 cl2 cl2' ps1 ps2 ; exists subst ; repeat split ; auto.
  - now left.
  - apply (sresproof_rm_opposable1 hyps sos cl1 cl2) ; auto. now exists i'.
  - apply (sresproof_rm_opposable2 hyps sos cl1 cl2) ; auto. now exists i'.
Qed.

(*****************************************************************************)
(* Logic/positive.ml *)
(*****************************************************************************)

Definition allpositive cl := Included cl positive.

Lemma allpositive_def : allpositive = (fun _460164 : form -> Prop => forall p : form, (@IN form p _460164) -> positive p).
Proof. exact (eq_refl allpositive). Qed.

Inductive pposresproof (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | pposresproof_assumption : forall cl, IN cl hyps -> pposresproof hyps cl
  | pposresproof_resolve : forall f cl cl', pposresproof hyps cl ->
                        pposresproof hyps cl' -> allpositive cl \/ allpositive cl' ->
                        IN f cl -> IN (FNot f) cl' ->
                        pposresproof hyps (resolve f cl cl').

Lemma pposresproof_def : pposresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall pposresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((pposresproof' cl1) /\ ((pposresproof' cl2) /\ (((allpositive cl1) \/ (allpositive cl2)) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> pposresproof' a') -> pposresproof' a).
Proof.
  ext hyps. ind_align'.
Qed.

Inductive psemresproof (TrueVar : Ensemble form) (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | psemresproof_assumption : forall cl, IN cl hyps -> psemresproof TrueVar hyps cl
  | psemresproof_resolve : forall f cl cl', psemresproof TrueVar hyps cl ->
                        psemresproof TrueVar hyps cl' ->
                        ~pholds TrueVar (interp cl) \/ ~pholds TrueVar (interp cl') ->
                        IN f cl -> IN (FNot f) cl' ->
                        psemresproof TrueVar hyps (resolve f cl cl').

Lemma psemresproof_def : psemresproof = (fun v : form -> Prop => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall psemresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((psemresproof' cl1) /\ ((psemresproof' cl2) /\ (((~ (pholds v (interp cl1))) \/ (~ (pholds v (interp cl2)))) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> psemresproof' a') -> psemresproof' a).
Proof.
  ext v hyps. ind_align'.
Qed.

Definition propflip TrueVar f := COND (negative f = pholds TrueVar f) f (FNot f).

Lemma propflip_def : propflip = (fun _467005 : form -> Prop => fun _467006 : form => @COND form ((negative _467006) = (pholds _467005 _467006)) _467006 (FNot _467006)).
Proof. exact (eq_refl propflip). Qed.

Inductive posresproof (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | posresproof_assumption : forall cl, IN cl hyps -> posresproof hyps cl
  | posresproof_rm_opposable :
      forall cl1 cl2 cl2' ps1 ps2 subst, posresproof hyps cl1 -> posresproof hyps cl2 ->
      (allpositive cl1 \/ allpositive cl2) ->
      IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2' -> Included ps1 cl1 ->
      Included ps2 cl2' -> ps1 <> Empty_set -> ps2 <> Empty_set ->
      (exists subst', Unifies subst' (Union ps1 (IMAGE FNot ps2))) ->
      mgu (Union ps1 (IMAGE FNot ps2)) = subst ->
      posresproof hyps (IMAGE (formsubst subst) (Union (Setminus cl1 ps1) (Setminus cl2' ps2))).

Lemma posresproof_def : posresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall posresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((posresproof' cl1) /\ ((posresproof' cl2) /\ (((allpositive cl1) \/ (allpositive cl2)) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_622 : form => exists p : form, @SETSPEC form GEN_PVAR_622 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_623 : form => exists p : form, @SETSPEC form GEN_PVAR_623 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> posresproof' a') -> posresproof' a).
Proof.
  ext hyps. fastind_align.
  3,4 : apply (posresproof_rm_opposable _ _ cl2) ; auto ; now exists i'.
  - now left.
  - right. exist cl1 cl2 cl2' ps1 ps2. exists subst. repeat split;auto.
Qed.

Inductive semresproof {A : Type'} (M : Structure A) 
  (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | semresproof_assumption : forall cl, IN cl hyps -> semresproof M hyps cl
  | semresproof_rm_opposable :
      forall cl1 cl2 cl2' ps1 ps2 subst, semresproof M hyps cl1 -> semresproof M hyps cl2 ->
      (~(forall v, holds M v (interp cl1)) \/ ~forall v, holds M v (interp cl2)) ->
      IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2' -> Included ps1 cl1 ->
      Included ps2 cl2' -> ps1 <> Empty_set -> ps2 <> Empty_set ->
      (exists subst', Unifies subst' (Union ps1 (IMAGE FNot ps2))) ->
      mgu (Union ps1 (IMAGE FNot ps2)) = subst ->
      semresproof M hyps (IMAGE (formsubst subst) (Union (Setminus cl1 ps1) (Setminus cl2' ps2))).

Lemma semresproof_def {A : Type'} : (@semresproof A) = (fun M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((semresproof' cl1) /\ ((semresproof' cl2) /\ (((~ (forall v : N -> A, @holds A M v (interp cl1))) \/ (~ (forall v : N -> A, @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_629 : form => exists p : form, @SETSPEC form GEN_PVAR_629 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_630 : form => exists p : form, @SETSPEC form GEN_PVAR_630 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof' a') -> semresproof' a).
Proof.
  ext M hyps. ext E. fastind_align.
  3,4 : apply (semresproof_rm_opposable _ _ _ cl2) ; auto ; now exists i'.
  - now left.
  - right. exist cl1 cl2 cl2' ps1 ps2. exists subst. repeat split ; auto.
Qed.

Inductive semresproof2 {A : Type'} (M : Structure A) 
  (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | semresproof2_assumption : forall cl, IN cl hyps -> semresproof2 M hyps cl
  | semresproof2_rm_opposable :
      forall cl1 cl2 cl2' ps1 ps2 subst, semresproof2 M hyps cl1 -> semresproof2 M hyps cl2 ->
      (~(forall v, valuation M v -> holds M v (interp cl1)) \/
      ~forall v, valuation M v -> holds M v (interp cl2)) ->
      IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2' -> Included ps1 cl1 ->
      Included ps2 cl2' -> ps1 <> Empty_set -> ps2 <> Empty_set ->
      (exists subst', Unifies subst' (Union ps1 (IMAGE FNot ps2))) ->
      mgu (Union ps1 (IMAGE FNot ps2)) = subst ->
      semresproof2 M hyps (IMAGE (formsubst subst) (Union (Setminus cl1 ps1) (Setminus cl2' ps2))).

Lemma semresproof2_def {A : Type'} : (@semresproof2 A) = (fun M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof2' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((semresproof2' cl1) /\ ((semresproof2' cl2) /\ (((~ (forall v : N -> A, (@valuation A M v) -> @holds A M v (interp cl1))) \/ (~ (forall v : N -> A, (@valuation A M v) -> @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_636 : form => exists p : form, @SETSPEC form GEN_PVAR_636 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_637 : form => exists p : form, @SETSPEC form GEN_PVAR_637 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof2' a') -> semresproof2' a).
Proof.
  ext M hyps. ext E. fastind_align.
  3,4 : apply (semresproof2_rm_opposable _ _ _ cl2) ; auto ; now exists i'.
  - now left.
  - right. exist cl1 cl2 cl2' ps1 ps2. exists subst. repeat split ; auto.
Qed.

(*****************************************************************************)
(* Logic/givensem.ml *)
(*****************************************************************************)

Definition isaresolvent_sem (M : Structure N) cl c := isaresolvent cl c /\
  (~(forall v, holds M v (interp (fst c))) \/ ~forall v, holds M v (interp (snd c))).

Lemma isaresolvent_sem_def : isaresolvent_sem = (fun _533128 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533129 : form -> Prop => fun _533130 : prod (form -> Prop) (form -> Prop) => (isaresolvent _533129 (@pair (form -> Prop) (form -> Prop) (@fst (form -> Prop) (form -> Prop) _533130) (@snd (form -> Prop) (form -> Prop) _533130))) /\ ((~ (forall v : N -> N, @holds N _533128 v (interp (@fst (form -> Prop) (form -> Prop) _533130)))) \/ (~ (forall v : N -> N, @holds N _533128 v (interp (@snd (form -> Prop) (form -> Prop) _533130)))))).
Proof.
  ext M c (cl1,cl2). reflexivity.
Qed.

Definition allresolvents_sem M E E' :=
  fun cl => (exists c1 c2 : form -> Prop, IN c1 E /\ IN c2 E' /\ isaresolvent_sem M cl (c1, c2)).

Lemma allresolvents_sem_def : allresolvents_sem = (fun _533155 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533156 : (form -> Prop) -> Prop => fun _533157 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_648 : form -> Prop => exists c : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_648 (exists c1 : form -> Prop, exists c2 : form -> Prop, (@IN (form -> Prop) c1 _533156) /\ ((@IN (form -> Prop) c2 _533157) /\ (isaresolvent_sem _533155 c (@pair (form -> Prop) (form -> Prop) c1 c2)))) c)).
Proof.
  ext M E E'. symmetry. exact (SPEC_elim).
Qed.

Definition allntresolvents_sem M E E' cl := IN cl (allresolvents_sem M E E') /\ ~ tautologous cl.

Lemma allntresolvents_sem_def : allntresolvents_sem = (fun _533176 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533177 : (form -> Prop) -> Prop => fun _533178 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_649 : form -> Prop => exists r : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_649 ((@IN (form -> Prop) r (allresolvents_sem _533176 _533177 _533178)) /\ (~ (tautologous r))) r)).
Proof.
  ext M E E'. symmetry. exact (SPEC_elim).
Qed.

Definition resolvents_sem M cl l := list_of_set (allresolvents_sem M (Singleton cl) (set_of_list l)).

Lemma resolvents_sem_def : resolvents_sem = (fun _533232 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533233 : form -> Prop => fun _533234 : list (form -> Prop) => @list_of_set (form -> Prop) (allresolvents_sem _533232 (@INSERT (form -> Prop) _533233 (@Ensembles.Empty_set (form -> Prop))) (@set_of_list (form -> Prop) _533234))).
Proof.
  ext M cl l. unfold resolvents_sem. now rewrite Singleton_from_Empty.
Qed.

Definition step_sem M c :=
  match snd c with
  | nil => c
  | a::l' => (insert a (fst c), fold_right (incorporate a) l' (resolvents_sem M a (a :: (fst c)))) end.

Lemma step_sem_def : step_sem = (fun _533275 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533276 : prod (list (form -> Prop)) (list (form -> Prop)) => @COND (prod (list (form -> Prop)) (list (form -> Prop))) ((@snd (list (form -> Prop)) (list (form -> Prop)) _533276) = (@nil (form -> Prop))) (@pair (list (form -> Prop)) (list (form -> Prop)) (@fst (list (form -> Prop)) (list (form -> Prop)) _533276) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276)) (@Basics.apply (list (form -> Prop)) (prod (list (form -> Prop)) (list (form -> Prop))) (fun new : list (form -> Prop) => @Datatypes.id (prod (list (form -> Prop)) (list (form -> Prop))) (@pair (list (form -> Prop)) (list (form -> Prop)) (@insert (form -> Prop) (@HOLLight_Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276)) (@fst (list (form -> Prop)) (list (form -> Prop)) _533276)) (@fold_right_with_perm_args (form -> Prop) (list (form -> Prop)) (incorporate (@HOLLight_Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276))) new (@HOLLight_Real_With_N.mappings.tl (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276))))) (resolvents_sem _533275 (@HOLLight_Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276)) (@cons (form -> Prop) (@HOLLight_Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276)) (@fst (list (form -> Prop)) (list (form -> Prop)) _533276))))).
Proof.
  ext M (l,l'). rewrite COND_list. now destruct l'.
Qed.

Fixpoint given_sem M n p :=
  match n with
  | O => p
  | S n => step_sem M (given_sem M n p) end.

Definition giveN_sem M n := given_sem M (N.to_nat n).

Lemma given_sem_def : giveN_sem = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> N -> (prod (list (form -> Prop)) (list (form -> Prop))) -> prod (list (form -> Prop)) (list (form -> Prop))) (fun given_sem' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> N -> (prod (list (form -> Prop)) (list (form -> Prop))) -> prod (list (form -> Prop)) (list (form -> Prop)) => forall _533299 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall p : prod (list (form -> Prop)) (list (form -> Prop)), (given_sem' _533299 M (NUMERAL N0) p) = p) /\ (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall n : N, forall p : prod (list (form -> Prop)) (list (form -> Prop)), (given_sem' _533299 M (N.succ n) p) = (step_sem M (given_sem' _533299 M n p)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))).
Proof.
  N_rec_align. intros. unfold giveN_sem. now rewrite (Nnat.N2Nat.inj_succ).
Qed.

Definition Used_SEM M init n := set_of_list (fst (giveN_sem M n init)).
Definition Unused_SEM M init n := set_of_list (snd (giveN_sem M n init)).

Lemma Used_SEM_def : Used_SEM = (fun _533300 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533301 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _533302 : N => @set_of_list (form -> Prop) (@fst (list (form -> Prop)) (list (form -> Prop)) (giveN_sem _533300 _533302 _533301))).
Proof. exact (eq_refl Used_SEM). Qed.
Lemma Unused_SEM_def : Unused_SEM = (fun _533321 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533322 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _533323 : N => @set_of_list (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem _533321 _533323 _533322))).
Proof. exact (eq_refl Unused_SEM). Qed.

Fixpoint Subnat_SEM M init n := 
  match n with
  | O => Empty_set
  | S n => match snd (given_sem M n init) with
    | nil => Subnat_SEM M init n
    | a::l => INSERT a (Subnat_SEM M init n) end end.

Definition Sub_SEM M init n : (form -> Prop) -> Prop := Subnat_SEM M init (N.to_nat n).

Lemma Sub_SEM_def : Sub_SEM = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> (form -> Prop) -> Prop) (fun Sub_SEM' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> (form -> Prop) -> Prop => forall _533349 : prod N (prod N (prod N (prod N (prod N (prod N N))))), (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall init : prod (list (form -> Prop)) (list (form -> Prop)), (Sub_SEM' _533349 M init (NUMERAL N0)) = (@Ensembles.Empty_set (form -> Prop))) /\ (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall init : prod (list (form -> Prop)) (list (form -> Prop)), forall n : N, (Sub_SEM' _533349 M init (N.succ n)) = (@COND ((form -> Prop) -> Prop) ((@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem M n init)) = (@nil (form -> Prop))) (Sub_SEM' _533349 M init n) (@INSERT (form -> Prop) (@HOLLight_Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem M n init))) (Sub_SEM' _533349 M init n))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))))))).
Proof.
  N_rec_align.
  intros M init n. rewrite COND_list. unfold Sub_SEM.
  rewrite Nnat.N2Nat.inj_succ. unfold giveN_sem. simpl.
  apply (Sub_def0 (snd (given_sem M (N.to_nat n) init))).
Qed.

Fixpoint breaknat_sem M init n :=
  match n with
  | O => lengthN (snd init)
  | S n => let k := breaknat_sem M init n in
           k + lengthN (snd (giveN_sem M k init)) end.

Definition break_sem M init n := breaknat_sem M init (N.to_nat n).

Lemma break_sem_def : break_sem = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> N) (fun break_sem' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> N => forall _544384 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall init : prod (list (form -> Prop)) (list (form -> Prop)), (break_sem' _544384 M init (NUMERAL N0)) = (@lengthN (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem M (NUMERAL N0) init)))) /\ (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall n : N, forall init : prod (list (form -> Prop)) (list (form -> Prop)), (break_sem' _544384 M init (N.succ n)) = (N.add (break_sem' _544384 M init n) (@lengthN (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem M (break_sem' _544384 M init n) init)))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))).
Proof.
  N_rec_align.
  intros. unfold break_sem. now rewrite Nnat.N2Nat.inj_succ.
Qed.

Definition level_sem M init n := Sub_SEM M init (break_sem M init n).

Lemma level_sem_def : level_sem = (fun _544385 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _544386 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _544387 : N => Sub_SEM _544385 _544386 (break_sem _544385 _544386 _544387)).
Proof. exact (eq_refl level_sem). Qed.

(*****************************************************************************)
(* Logic/prolog.ml *)
(*****************************************************************************)

Definition definite cl := clause cl /\ CARD (Intersection cl positive) = 1.

Lemma definite_def : definite = (fun _545149 : form -> Prop => (clause _545149) /\ ((@CARD form (@GSPEC form (fun GEN_PVAR_652 : form => exists p : form, @SETSPEC form GEN_PVAR_652 ((@IN form p _545149) /\ (positive p)) p))) = (NUMERAL (BIT1 N0)))).
Proof.
  ext cl. unfold definite. now rewrite INTER_def.
Qed.

Definition horn cl := clause cl /\ CARD (Intersection cl positive) <= 1.

Lemma horn_def : horn = (fun _545154 : form -> Prop => (clause _545154) /\ (N.le (@CARD form (@GSPEC form (fun GEN_PVAR_653 : form => exists p : form, @SETSPEC form GEN_PVAR_653 ((@IN form p _545154) /\ (positive p)) p))) (NUMERAL (BIT1 N0)))).
Proof.
  ext cl. unfold horn. now rewrite INTER_def.
Qed.

Definition falsify f cl := COND (definite cl) cl (Ensembles.Add cl f).

Lemma falsify_def : falsify = (fun _545159 : form => fun _545160 : form -> Prop => @COND (form -> Prop) (definite _545160) _545160 (@INSERT form _545159 _545160)).
Proof. exact (eq_refl falsify). Qed.

Definition minmodel E := (herbase (functions E),
  (Fn,
  fun n l => forall M, Dom M = herbase (functions E) /\ 
    Fun M = Fn /\ satisfies M E -> Pred M n l)).

Lemma minmodel_def : minmodel = (fun _546187 : form -> Prop => @pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (herbase (functions _546187)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun zs : list term => forall H : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (((@Dom term H) = (herbase (functions _546187))) /\ (((@Fun term H) = Fn) /\ (@satisfies term H _546187))) -> @Pred term H p zs))).
Proof. exact (eq_refl minmodel). Qed.

Definition breakhorn cl := COND (definite cl)
  (let p := ε (fun p : form => IN p cl /\ positive p) in
    (map FNot (list_of_set (Subtract cl p)), p))
  (map FNot (list_of_set cl), FFalse).

Lemma breakhorn_def : breakhorn = (fun _546245 : form -> Prop => @COND (prod (list form) form) (definite _546245) (@Basics.apply form (prod (list form) form) (fun p : form => @Datatypes.id (prod (list form) form) (@pair (list form) form (@List.map form form FNot (@list_of_set form (@Ensembles.Subtract form _546245 p))) p)) (@ε form (fun p : form => (@IN form p _546245) /\ (positive p)))) (@pair (list form) form (@List.map form form FNot (@list_of_set form _546245)) FFalse)).
Proof. exact (eq_refl breakhorn). Qed.

Definition hypotheses cl := fst (breakhorn cl).
Definition conclusion cl := snd (breakhorn cl).

Lemma hypotheses_def : hypotheses = (fun _546250 : form -> Prop => @fst (list form) form (breakhorn _546250)).
Proof. exact (eq_refl hypotheses). Qed.
Lemma conclusion_def : conclusion = (fun _546255 : form -> Prop => @snd (list form) form (breakhorn _546255)).
Proof. exact (eq_refl conclusion). Qed.

Inductive gbackchain E : N -> form -> Prop :=
| gbackchain0 : forall cl v l, IN cl E ->
  (forall n, IN (v n) (herbase (functions (IMAGE interp E)))) ->
  Forall2 (gbackchain E) l (map (formsubst v) (hypotheses cl)) ->
  gbackchain E (fold_right N.add 1 l) (formsubst v (conclusion cl)).

Fixpoint gbackchain_ind' (E : Ensemble (Ensemble form))
  (P : N -> form -> Prop)
  (H : forall cl v l, IN cl E ->
    (forall n : N, IN (v n) (herbase (functions (IMAGE interp E)))) ->
    Forall2 P l (map (formsubst v) (hypotheses cl)) ->
    P (fold_right N.add 1 l) (formsubst v (conclusion cl)))
  (n : N) (f : form) (H0 : gbackchain E n f) : P n f :=
  match H0 in gbackchain _ n1 f1 return P n1 f1
  with gbackchain0 cl v l H1 H2 H3 => H cl v l H1 H2
    (Forall2_ind (Forall2 P)
      (Forall2_nil _) (fun n0 f0 l0 l0' H4 H5 H6 =>
        Forall2_cons _ _ (gbackchain_ind' E P H n0 f0 H4) H6) H3) end.

Lemma gbackchain_def : gbackchain = (fun s : (form -> Prop) -> Prop => fun a0 : N => fun a1 : form => forall gbackchain' : N -> form -> Prop, (forall a0' : N, forall a1' : form, (exists cl : form -> Prop, exists i : N -> term, exists ns : list N, (a0' = (@fold_right_with_perm_args N N N.add ns (NUMERAL (BIT1 N0)))) /\ ((a1' = (formsubst i (conclusion cl))) /\ ((@IN (form -> Prop) cl s) /\ ((forall x : N, @IN term (i x) (herbase (functions (@IMAGE (form -> Prop) form interp s)))) /\ (@List.Forall2 N form gbackchain' ns (@List.map form form (formsubst i) (hypotheses cl))))))) -> gbackchain' a0' a1') -> gbackchain' a0 a1).
Proof.
  ext E n f. apply prop_ext;intro H.
  - intros P H'. apply (gbackchain_ind' E);auto.
    intros cl v l H1 H2 IHgbc. apply H'.
    exists cl. exists v. now exists l.
  - apply H. clear n f H. intros n f (cl, (v, (l, H))). full_destruct.
    rewrite H, H0. now apply (gbackchain0 E cl v l). 
Qed.

Definition iminmodel E :=
  (terms (functions E),
   (Fn,
     fun n l => forall M, Dom M = terms (functions E) /\ Fun M = Fn /\ 
     (forall v f, IN f E /\ valuation M v -> holds M v f) ->
     Pred M n l)).

Lemma iminmodel_def : iminmodel = (fun _549309 : form -> Prop => @pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (terms (functions _549309)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun zs : list term => forall C : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (((@Dom term C) = (terms (functions _549309))) /\ (((@Fun term C) = Fn) /\ (forall v : N -> term, forall p' : form, ((@IN form p' _549309) /\ (@valuation term C v)) -> @holds term C v p'))) -> @Pred term C p zs))).
Proof. exact (eq_refl iminmodel). Qed.

(* replacing herbase with terms*)
Inductive ibackchain E : N -> form -> Prop :=
| ibackchain0 : forall cl v l, IN cl E ->
  (forall n, IN (v n) (terms (functions (IMAGE interp E)))) ->
  Forall2 (ibackchain E) l (map (formsubst v) (hypotheses cl)) ->
  ibackchain E (fold_right N.add 1 l) (formsubst v (conclusion cl)).

Fixpoint ibackchain_ind' (E : Ensemble (Ensemble form))
  (P : N -> form -> Prop)
  (H : forall cl v l, IN cl E ->
    (forall n : N, IN (v n) (terms (functions (IMAGE interp E)))) ->
    Forall2 P l (map (formsubst v) (hypotheses cl)) ->
    P (fold_right N.add 1 l) (formsubst v (conclusion cl)))
  (n : N) (f : form) (H0 : ibackchain E n f) : P n f :=
  match H0 in ibackchain _ n1 f1 return P n1 f1
  with ibackchain0 cl v l H1 H2 H3 => H cl v l H1 H2
    (Forall2_ind (Forall2 P)
      (Forall2_nil _) (fun n0 f0 l0 l0' H4 H5 H6 =>
        Forall2_cons _ _ (ibackchain_ind' E P H n0 f0 H4) H6) H3) end.

Lemma ibackchain_def : ibackchain = (fun s : (form -> Prop) -> Prop => fun a0 : N => fun a1 : form => forall ibackchain' : N -> form -> Prop, (forall a0' : N, forall a1' : form, (exists cl : form -> Prop, exists i : N -> term, exists ns : list N, (a0' = (@fold_right_with_perm_args N N N.add ns (NUMERAL (BIT1 N0)))) /\ ((a1' = (formsubst i (conclusion cl))) /\ ((@IN (form -> Prop) cl s) /\ ((forall x : N, @IN term (i x) (terms (functions (@IMAGE (form -> Prop) form interp s)))) /\ (@List.Forall2 N form ibackchain' ns (@List.map form form (formsubst i) (hypotheses cl))))))) -> ibackchain' a0' a1') -> ibackchain' a0 a1).
Proof.
  ext E n f. apply prop_ext;intro H.
  - intros P H'. apply (ibackchain_ind' E);auto.
    intros cl v l H1 H2 IHibc. apply H'.
    exists cl. exists v. now exists l.
  - apply H. clear n f H. intros n f (cl, (v, (l, H))). full_destruct.
    rewrite H, H0. now apply (ibackchain0 E cl v l).
Qed.

(*****************************************************************************)
(* Logic/Birkhoff.ml *)
(*****************************************************************************)

Inductive provable E : form -> Prop :=
| pr_assume : forall t t', IN (FEq t t') E -> provable E (FEq t t')
| pr_FEq_refl : forall t, provable E (FEq t t)
| pr_FEq_sym : forall t t', provable E (FEq t t') -> provable E (FEq t' t)
| pr_FEq_trans : forall t t' t'', provable E (FEq t t') -> provable E (FEq t' t'') ->
                 provable E (FEq t t'')
| pr_FEq_fun_compat : forall n l l', Forall2 (fun t t' => provable E (FEq t t')) l l' ->
               provable E (FEq (Fn n l) (Fn n l'))
| pr_formsubst : forall t t' v, provable E (FEq t t') -> provable E (formsubst v (FEq t t')).

Fixpoint provable_ind' (E : Ensemble form) (P : form -> Prop) 
  H0 H1 H2 H3
  (H4 : forall n l l', Forall2 (fun t t' => P (FEq t t')) l l' ->
               P (FEq (Fn n l) (Fn n l')))
  H5 (f : form) (H6 : provable E f) : P f :=
  provable_ind E P H0 H1 H2 H3 
    (fun n l l' H' => H4 n l l' (Forall2_ind (Forall2 (fun t t' => P (FEq t t')))
      (Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => Forall2_cons _ _
        (provable_ind' E P H0 H1 H2 H3 H4 H5 _ H00) H20) H')) H5 f H6.

Lemma vdash_def : provable = (fun E : form -> Prop => fun a : form => forall vdash' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, (a' = (FEq s t)) /\ (@IN form (FEq s t) E)) \/ ((exists t : term, a' = (FEq t t)) \/ ((exists s : term, exists t : term, (a' = (FEq t s)) /\ (vdash' (FEq s t))) \/ ((exists s : term, exists t : term, exists u : term, (a' = (FEq s u)) /\ ((vdash' (FEq s t)) /\ (vdash' (FEq t u)))) \/ ((exists f : N, exists a'' : list term, exists b : list term, (a' = (FEq (Fn f a'') (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash' (FEq l r)) a'' b)) \/ (exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq s t))) /\ (vdash' (FEq s t)))))))) -> vdash' a') -> vdash' a).
Proof.
  ext E f. apply prop_ext;intro H.
  - intros P H'. apply (provable_ind' E);auto ; clear H ;
    intros ; apply H' ; breakgoal'.
  - apply H. clear f H. intros f H. full_destruct ;
    (repeat match goal with H : _ |- _ => rewrite H end) ; try now constructor.
    now apply (pr_FEq_trans _ _ t).
Qed.

Inductive wcprovable E : form -> Prop :=
| wcpr_assume : forall t t' v, IN (FEq t t') E -> wcprovable E (formsubst v (FEq t t'))
| wcpr_FEq_refl : forall t, wcprovable E (FEq t t)
| wcpr_FEq_sym : forall t t' v, IN (FEq t t') E -> wcprovable E (formsubst v (FEq t' t))
| wcpr_FEq_trans : forall t t' t'', wcprovable E (FEq t t') -> wcprovable E (FEq t' t'') ->
                 wcprovable E (FEq t t'')
| wcpr_FEq_fun_compat : forall n l l', Forall2 (fun t t' => wcprovable E (FEq t t')) l l' ->
               wcprovable E (FEq (Fn n l) (Fn n l')).

Fixpoint wcprovable_ind' (E : Ensemble form) (P : form -> Prop) 
  H0 H1 H2 H3
  (H4 : forall n l l', Forall2 (fun t t' => P (FEq t t')) l l' ->
               P (FEq (Fn n l) (Fn n l')))
  (f : form) (H5 : wcprovable E f) : P f :=
  wcprovable_ind E P H0 H1 H2 H3
    (fun n l l' H' => H4 n l l' (Forall2_ind (Forall2 (fun t t' => P (FEq t t')))
      (Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => Forall2_cons _ _
        (wcprovable_ind' E P H0 H1 H2 H3 H4 _ H00) H20) H')) f H5.

Lemma vdash2_def : wcprovable = (fun E : form -> Prop => fun a : form => forall vdash2' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq s t))) /\ (@IN form (FEq s t) E)) \/ ((exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq t s))) /\ (@IN form (FEq s t) E)) \/ ((exists t : term, a' = (FEq t t)) \/ ((exists s : term, exists t : term, exists u : term, (a' = (FEq s u)) /\ ((vdash2' (FEq s t)) /\ (vdash2' (FEq t u)))) \/ (exists f : N, exists a'' : list term, exists b : list term, (a' = (FEq (Fn f a'') (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash2' (FEq l r)) a'' b)))))) -> vdash2' a') -> vdash2' a).
Proof.
  ext E f. apply prop_ext;intro H.
  - intros P H'. apply (wcprovable_ind' E);auto ; clear H ;
    intros ; apply H' ; breakgoal'.
  - apply H. clear f H. intros f H. full_destruct ;
    (repeat match goal with H : _ |- _ => rewrite H end) ; try now constructor.
    now apply (wcpr_FEq_trans _ _ t).
Qed.

Inductive aprovable E : form -> Prop :=
| apr_assume : forall t t' v, IN (FEq t t') E -> aprovable E (formsubst v (FEq t t'))
| apr_FEq_sym : forall t t' v, IN (FEq t t') E -> aprovable E (formsubst v (FEq t' t)).

Lemma vdash2_axiom_def : aprovable = (fun E : form -> Prop => fun a : form => forall vdash2_axiom' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq s t))) /\ (@IN form (FEq s t) E)) \/ (exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq t s))) /\ (@IN form (FEq s t) E))) -> vdash2_axiom' a') -> vdash2_axiom' a).
Proof. ext e. ind_align'. Qed.

Unset Elimination Schemes.
Inductive cprovable E : form -> Prop :=
| cpr_FEq_refl : forall t, cprovable E (FEq t t)
| cpr_prac : forall t t', provable_achain E (FEq t t') -> cprovable E (FEq t t')
| cpr_prcc : forall t t', provable_cchain E (FEq t t') -> cprovable E (FEq t t')
with provable_achain E : form -> Prop :=
| prac_apr : forall t t', aprovable E (FEq t t') -> provable_achain E (FEq t t')
| prac_trans : forall t t' t'', aprovable E (FEq t t') -> cprovable E (FEq t' t'') ->
               provable_achain E (FEq t t'')
with provable_cchain E : form -> Prop :=
| prcc_prc : forall t t', provable_cong E (FEq t t') -> provable_cchain E (FEq t t')
| prcc_trans : forall t t' t'', provable_cong E (FEq t t') -> provable_achain E (FEq t' t'') ->
               provable_cchain E (FEq t t'')
with provable_cong E : form -> Prop :=
| prc_fun_compat : forall n l l', Forall2 (fun t t' => cprovable E (FEq t t')) l l' ->
                   provable_cong E (FEq (Fn n l) (Fn n l')).
Set Elimination Schemes.

Section cprovable_ind.

Variables 
  (E : Ensemble form)
  (P P0 P1 P2 : form -> Prop)
  (H0 : forall t, P (FEq t t))
  (H1 : forall t t', provable_achain E (FEq t t') -> P0 (FEq t t') -> P (FEq t t'))
  (H2 : forall t t', provable_cchain E (FEq t t') -> P1 (FEq t t') -> P (FEq t t'))
  (H3 : forall t t', aprovable E (FEq t t') -> P0 (FEq t t'))
  (H4 : forall t t' t'', aprovable E (FEq t t') -> cprovable E (FEq t' t'') ->
    P (FEq t' t'') -> P0 (FEq t t''))
  (H5 : forall t t', provable_cong E (FEq t t') -> P2 (FEq t t') -> P1 (FEq t t'))
  (H6 : forall t t' t'', provable_cong E (FEq t t') -> P2 (FEq t t') ->
    provable_achain E (FEq t' t'') -> P0 (FEq t' t'') -> P1 (FEq t t''))
  (H7 : forall n l l', Forall2 (fun t t' : term => P (FEq t t')) l l' -> P2 (FEq (Fn n l) (Fn n l'))).

Fixpoint cprovable_ind f (H' : cprovable E f) : P f :=
  match H' in cprovable _ f return P f with
  | cpr_FEq_refl t => H0 t
  | cpr_prac t t' Hac => H1 t t' Hac (provable_achain_ind (FEq t t') Hac)
  | cpr_prcc t t' Hcc => H2 t t' Hcc (provable_cchain_ind (FEq t t') Hcc) end
with provable_achain_ind f (Hac : provable_achain E f ): P0 f :=
  match Hac in provable_achain _ f return P0 f with
  | prac_apr t t' Ha => H3 t t' Ha
  | prac_trans t t' t'' Ha H' => H4 t t' t'' Ha H' (cprovable_ind (FEq t' t'') H') end
with provable_cchain_ind f (Hcc : provable_cchain E f) : P1 f :=
  match Hcc in provable_cchain _ f return P1 f with
  | prcc_prc t t' Hc => H5 t t' Hc (provable_cong_ind (FEq t t') Hc)
  | prcc_trans t t' t'' Hc Hac => H6 t t' t'' Hc (provable_cong_ind (FEq t t') Hc)
    Hac (provable_achain_ind (FEq t' t'') Hac) end
with provable_cong_ind f (Hc : provable_cong _ f) : P2 f :=
  match Hc in provable_cong _ f return P2 f with
  | prc_fun_compat n l l' HF2' => H7 n l l'
    (Forall2_ind (Forall2 (fun t t' => P (FEq t t')))
      (Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => Forall2_cons _ _
        (cprovable_ind _ H00) H20) HF2') end.

End cprovable_ind.

Ltac provable_align induction_principle :=
  let E := fresh in
  let f := fresh in
  let H := fresh in
  let Pac := fresh in
  let Pcc := fresh in
  let Pc := fresh in
  let P := fresh in
  let H' := fresh in
  ext E f ; apply prop_ext ; intro H ;
  [ intros Pac Pcc Pc P H' ; apply (induction_principle E P Pac Pcc Pc) ; auto ;
    clear H ; intros ; apply H' ; breakgoal'
  | apply (H (provable_achain E) (provable_cchain E) (provable_cong E) (cprovable E)) ;
    clear f H ; (repeat split) ; intros f H ; full_destruct ;
    (repeat match goal with H : _ |- _ => rewrite H end) ; (try now constructor) ;
    match goal with t:term , t':term |- _ => (try now apply (prac_trans E t t')) ;
    now apply (prcc_trans E t t') end
  ].

Lemma vdash3_def : cprovable = (fun E : form -> Prop => fun a3 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3' : form, (exists s : term, exists t : term, (a3' = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3')))) -> vdash3' a3).
Proof. provable_align cprovable_ind. Qed.

Lemma vdash2_achain_def : provable_achain = (fun E : form -> Prop => fun a0 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0' : form, ((exists s : term, exists t : term, (a0' = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0' = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0') /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_achain' a0).
Proof. provable_align provable_achain_ind. Qed.

Lemma vdash2_cchain_def : provable_cchain = (fun E : form -> Prop => fun a1 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1' : form, ((exists s : term, exists t : term, (a1' = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1' = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1') /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_cchain' a1).
Proof. provable_align provable_cchain_ind. Qed.

Lemma vdash2_cong_def : provable_cong = (fun E : form -> Prop => fun a2 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2' : form, (exists f : N, exists a : list term, exists b : list term, (a2' = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2') /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_cong' a2).
Proof. provable_align provable_cong_ind. Qed.

Fixpoint subterms t : term -> Prop :=
  match t with
  | V n => Singleton (V n)
  | Fn n l => Ensembles.Add (list_Union (map subterms l)) (Fn n l) end.

Lemma subterms_def : subterms = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> term -> Prop) (fun subterms' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> term -> Prop => forall _553739 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall x : N, (subterms' _553739 (V x)) = (@INSERT term (V x) (@Ensembles.Empty_set term))) /\ (forall f : N, forall args : list term, (subterms' _553739 (Fn f args)) = (@INSERT term (Fn f args) (@list_Union term (@List.map term (term -> Prop) (subterms' _553739) args))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))).
Proof.
  term_align. simpl. now rewrite Singleton_from_Empty.
Qed.

Inductive atomcase : form -> Prop := atom0 : forall n l, atomcase (Atom n l).

Inductive notatomcase : form -> Prop :=
| notatom_FFalse : notatomcase FFalse
| notatom_FImp : forall f f', notatomcase (FImp f f')
| notatom_FAll : forall n f, notatomcase (FAll n f).

Lemma atom_notatom_cover : forall f, atomcase f \/ notatomcase f.
Proof.
  induction f ; left + right ; now constructor.
Qed.

Definition on_atom := {| case := atomcase ; negcase := notatomcase ; cover_proof := atom_notatom_cover |}.

Definition SUBTERMSA : form -> term -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> form -> term -> Prop) (fun subtermsa' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> form -> term -> Prop => forall _553741 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall P : N, forall args : list term, (subtermsa' _553741 (Atom P args)) = (@list_Union term (@List.map term (term -> Prop) subterms args))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))))))).

Definition subtermsa f : term -> Prop :=
  match f with Atom _ l => list_Union (map subterms l) | _ => SUBTERMSA f end.

Lemma subtermsa_def : subtermsa = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> form -> term -> Prop) (fun subtermsa' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> form -> term -> Prop => forall _553741 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall P : N, forall args : list term, (subtermsa' _553741 (Atom P args)) = (@list_Union term (@List.map term (term -> Prop) subterms args))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))))))))).
Proof. partial_align on_atom. Qed.

Definition subtermss E := UNIONS (IMAGE subtermsa E).

Lemma subtermss_def : subtermss = (fun _553742 : form -> Prop => @UNIONS term (@GSPEC (term -> Prop) (fun GEN_PVAR_664 : term -> Prop => exists p : form, @SETSPEC (term -> Prop) GEN_PVAR_664 (@IN form p _553742) (subtermsa p)))).
Proof. exact (eq_refl subtermss). Qed.

Definition esubterms E t t' := subtermss (INSERT (FEq t t') (fun f =>
exists v, IN f (IMAGE (formsubst v) E))).

Lemma esubterms_def : esubterms = (fun _553747 : form -> Prop => fun _553748 : term => fun _553749 : term => subtermss (@INSERT form (FEq _553748 _553749) (@GSPEC form (fun GEN_PVAR_665 : form => exists i : N -> term, exists p : form, @SETSPEC form GEN_PVAR_665 (@IN form p _553747) (formsubst i p))))).
Proof. exact (eq_refl esubterms). Qed.

Unset Elimination Schemes.
Inductive scprovable E : form -> Prop :=
| scpr_FEq_refl : forall t, scprovable E (FEq t t)
| scpr_prsac : forall t t', provable_sachain E (FEq t t') -> scprovable E (FEq t t')
| scpr_prscc : forall t t', provable_scchain E (FEq t t') -> scprovable E (FEq t t')
with provable_sachain E : form -> Prop :=
| prsac_apr : forall t t', aprovable E (FEq t t') -> provable_sachain E (FEq t t')
| prsac_trans : forall t t' t'', aprovable E (FEq t t') -> scprovable E (FEq t' t'') ->
                IN t' (esubterms E t t'') -> provable_sachain E (FEq t t'')
with provable_scchain E : form -> Prop :=
| prscc_prsc : forall t t', provable_scong E (FEq t t') -> provable_scchain E (FEq t t')
| prscc_trans : forall t t' t'', provable_scong E (FEq t t') -> provable_sachain E (FEq t' t'') ->
                IN t' (esubterms E t t'') -> provable_scchain E (FEq t t'')
with provable_scong E : form -> Prop :=
| prsc_fun_compat : forall n l l', Forall2 (fun t t' => scprovable E (FEq t t')) l l' ->
                   provable_scong E (FEq (Fn n l) (Fn n l')).
Set Elimination Schemes.

Section scprovable_ind.

Variables 
  (E : Ensemble form)
  (P P0 P1 P2 : form -> Prop)
  (H0 : forall t, P (FEq t t))
  (H1 : forall t t', provable_sachain E (FEq t t') -> P0 (FEq t t') -> P (FEq t t'))
  (H2 : forall t t', provable_scchain E (FEq t t') -> P1 (FEq t t') -> P (FEq t t'))
  (H3 : forall t t', aprovable E (FEq t t') -> P0 (FEq t t'))
  (H4 : forall t t' t'', aprovable E (FEq t t') -> scprovable E (FEq t' t'') ->
    P (FEq t' t'') -> (IN t' (esubterms E t t'')) -> P0 (FEq t t''))
  (H5 : forall t t', provable_scong E (FEq t t') -> P2 (FEq t t') -> P1 (FEq t t'))
  (H6 : forall t t' t'', provable_scong E (FEq t t') -> P2 (FEq t t') ->
    provable_sachain E (FEq t' t'') -> P0 (FEq t' t'') -> (IN t' (esubterms E t t'')) ->
    P1 (FEq t t''))
  (H7 : forall n l l', Forall2 (fun t t' : term => P (FEq t t')) l l' -> P2 (FEq (Fn n l) (Fn n l'))).

Fixpoint scprovable_ind f (H' : scprovable E f) : P f :=
  match H' in scprovable _ f return P f with
  | scpr_FEq_refl t => H0 t
  | scpr_prsac t t' Hac => H1 t t' Hac (provable_sachain_ind (FEq t t') Hac)
  | scpr_prscc t t' Hcc => H2 t t' Hcc (provable_scchain_ind (FEq t t') Hcc) end
with provable_sachain_ind f (Hac : provable_sachain E f ): P0 f :=
  match Hac in provable_sachain _ f return P0 f with
  | prsac_apr t t' Ha => H3 t t' Ha
  | prsac_trans t t' t'' Ha H' Hsubs => H4 t t' t'' Ha H' (scprovable_ind (FEq t' t'') H') Hsubs end
with provable_scchain_ind f (Hcc : provable_scchain E f) : P1 f :=
  match Hcc in provable_scchain _ f return P1 f with
  | prscc_prsc t t' Hc => H5 t t' Hc (provable_scong_ind (FEq t t') Hc)
  | prscc_trans t t' t'' Hc Hac Hsubs => H6 t t' t'' Hc (provable_scong_ind (FEq t t') Hc)
    Hac (provable_sachain_ind (FEq t' t'') Hac) Hsubs end
with provable_scong_ind f (Hc : provable_scong _ f) : P2 f :=
  match Hc in provable_scong _ f return P2 f with
  | prsc_fun_compat n l l' HF2' => H7 n l l'
    (Forall2_ind (Forall2 (fun t t' => P (FEq t t')))
      (Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => Forall2_cons _ _
        (scprovable_ind _ H00) H20) HF2') end.

End scprovable_ind.

Ltac sprovable_align induction_principle :=
  let E := fresh in
  let f := fresh in
  let H := fresh in
  let Pac := fresh in
  let Pcc := fresh in
  let Pc := fresh in
  let P := fresh in
  let H' := fresh in
  ext E f ; apply prop_ext ; intro H ;
  [ intros Pac Pcc Pc P H' ; apply (induction_principle E P Pac Pcc Pc) ; auto ;
    clear H ; intros ; apply H' ; breakgoal'
  | apply (H (provable_sachain E) (provable_scchain E) (provable_scong E) (scprovable E)) ;
    clear f H ; (repeat split) ; intros f H ; full_destruct ;
    (repeat match goal with H : _ |- _ => rewrite H end) ; (try now constructor) ;
    match goal with t:term , t':term |- _ => (try now apply (prsac_trans E t t')) ;
    now apply (prscc_trans E t t') end
  ].

Lemma vdash4_def : scprovable = (fun E : form -> Prop => fun a3 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3' : form, (exists s : term, exists t : term, (a3' = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3')))) -> vdash4' a3).
Proof. sprovable_align scprovable_ind. Qed.

Lemma vdash2_sachain_def : provable_sachain = (fun E : form -> Prop => fun a0 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0' : form, ((exists s : term, exists t : term, (a0' = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0' = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0') /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_sachain' a0).
Proof. sprovable_align provable_sachain_ind. Qed.

Lemma vdash2_scchain_def : provable_scchain = (fun E : form -> Prop => fun a1 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1' : form, ((exists s : term, exists t : term, (a1' = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1' = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1') /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_scchain' a1).
Proof. sprovable_align provable_scchain_ind. Qed.

Lemma vdash2_scong_def : provable_scong = (fun E : form -> Prop => fun a2 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2' : form, (exists f : N, exists a : list term, exists b : list term, (a2' = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2') /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_scong' a2).
Proof. sprovable_align provable_scong_ind. Qed.

Definition Eqclause_Func c := set_of_list
  (FEq (Fn (fst c) (map fst (Varpairs (snd c)))) (Fn (fst c) (map snd (Varpairs (snd c))))
   :: map (fun c' => Not (FEq (fst c') (snd c')))
        (Varpairs (snd c))).

Lemma Eqclause_Func_def : Eqclause_Func = (fun _554544 : prod N N => @set_of_list form (@cons form (FEq (Fn (@fst N N _554544) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd N N _554544)))) (Fn (@fst N N _554544) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd N N _554544))))) (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (Not (FEq s t)))) (Varpairs (@snd N N _554544))))).
Proof.
  ext c. unfold Eqclause_Func. repeat f_equal.
  align_ε';auto. intros func' H H'. ext (t,t'). now rewrite H,H'.
Qed.

Definition Eqclause_Pred c := set_of_list
  (Atom (fst c) (map snd (Varpairs (snd c)))
   :: Not (Atom (fst c) (map fst (Varpairs (snd c))))
      :: map (fun c' => Not (FEq (fst c') (snd c')))
           (Varpairs (snd c))).

Lemma Eqclause_Pred_def : Eqclause_Pred = (fun _554553 : prod N N => @set_of_list form (@cons form (Atom (@fst N N _554553) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd N N _554553)))) (@cons form (Not (Atom (@fst N N _554553) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd N N _554553))))) (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (Not (FEq s t)))) (Varpairs (@snd N N _554553)))))).
Proof.
  ext c. unfold Eqclause_Pred. repeat f_equal.
  align_ε';auto. intros func' H H'. ext (t,t'). now rewrite H,H'.
Qed.

Definition Eqclauses L := INSERT (Singleton (FEq (V 0) (V 0))) 
  ( INSERT (set_of_list ((Not (FEq (V 0) (V 1)))::(Not (FEq (V 2) (V 1)))::(FEq (V 0) (V 2))::nil))
    (Union (IMAGE Eqclause_Func (fst L)) (IMAGE Eqclause_Pred (snd L)))).

Lemma Eqclauses_def : Eqclauses = (fun _554562 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => @INSERT (form -> Prop) (@INSERT form (FEq (V (NUMERAL N0)) (V (NUMERAL N0))) (@Ensembles.Empty_set form)) (@INSERT (form -> Prop) (@INSERT form (Not (FEq (V (NUMERAL N0)) (V (NUMERAL (BIT1 N0))))) (@INSERT form (Not (FEq (V (NUMERAL (BIT0 (BIT1 N0)))) (V (NUMERAL (BIT1 N0))))) (@INSERT form (FEq (V (NUMERAL N0)) (V (NUMERAL (BIT0 (BIT1 N0))))) (@Ensembles.Empty_set form)))) (@Ensembles.Union (form -> Prop) (@GSPEC (form -> Prop) (fun GEN_PVAR_666 : form -> Prop => exists fa : prod N N, @SETSPEC (form -> Prop) GEN_PVAR_666 (@IN (prod N N) fa (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _554562)) (Eqclause_Func fa))) (@GSPEC (form -> Prop) (fun GEN_PVAR_667 : form -> Prop => exists pa : prod N N, @SETSPEC (form -> Prop) GEN_PVAR_667 (@IN (prod N N) pa (@snd ((prod N N) -> Prop) ((prod N N) -> Prop) _554562)) (Eqclause_Pred pa)))))).
Proof.
  unfold INSERT at 2. now rewrite <- Singleton_from_Empty.
Qed.

Definition Eqaxiom_Pred_imp c := uclose
  (FImp (fold_right FAnd FTrue (map (fun c => FEq (fst c) (snd c)) (Varpairs (snd c))))
     (FImp (Atom (fst c) (map fst (Varpairs (snd c)))) (Atom (fst c) (map snd (Varpairs (snd c)))))).

Lemma Eqaxiom_Pred_imp_def : Eqaxiom_Pred_imp = (fun _554616 : prod N N => uclose (FImp (@fold_right_with_perm_args form form FAnd (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (FEq s t))) (Varpairs (@snd N N _554616))) FTrue) (FImp (Atom (@fst N N _554616) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd N N _554616)))) (Atom (@fst N N _554616) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd N N _554616))))))).
Proof.
  ext c. unfold Eqaxiom_Pred_imp , fold_right_with_perm_args. repeat f_equal. apply f_equal.
  f_equal. align_ε';auto. intros func' H H'. ext (t,t'). now rewrite H,H'.
Qed.

(*****************************************************************************)
(* Logic/trs.ml *)
(*****************************************************************************)

(* term rewritings *)
Inductive TRS (rw_rules : prod term term -> Prop) : term -> term -> Prop :=
| TRS_subst : forall v t t', IN (t,t') rw_rules ->
  TRS rw_rules (termsubst v t) (termsubst v t')
| TRS_rec : forall t t' n l l', TRS rw_rules t t' ->
  TRS rw_rules (Fn n (l++t::l')) (Fn n (l++t'::l')).

Lemma TRS_def : TRS = (fun rws : (prod term term) -> Prop => fun a0 : term => fun a1 : term => forall TRS' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((exists i : N -> term, exists l : term, exists r : term, (a0' = (termsubst i l)) /\ ((a1' = (termsubst i r)) /\ (@IN (prod term term) (@pair term term l r) rws))) \/ (exists s : term, exists t : term, exists f : N, exists largs : list term, exists rargs : list term, (a0' = (Fn f (@app term largs (@cons term s rargs)))) /\ ((a1' = (Fn f (@app term largs (@cons term t rargs)))) /\ (TRS' s t)))) -> TRS' a0' a1') -> TRS' a0 a1).
Proof.
  ext rw_rules. ind_align'.
Qed.

(*****************************************************************************)
(* Logic/lpo.ml *)
(*****************************************************************************)

Definition NONWF {A : Type} (R : A -> A -> Prop) (x : A) :=
  exists s, s 0 = x /\ forall n, R (s (N.succ n)) (s n).

Lemma NONWF_def {A : Type'} : (@NONWF A) = (fun _563585 : A -> A -> Prop => fun _563586 : A => exists s : N -> A, ((s (NUMERAL N0)) = _563586) /\ (forall n : N, _563585 (s (N.succ n)) (s n))).
Proof. exact (eq_refl NONWF). Qed.

Fixpoint termsize t :=
  match t with
  | V _ => 1
  | Fn _ l => fold_right N.add 1 (map termsize l) end.

Lemma termsize_def : termsize = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> N) (fun termsize' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> N => forall _564457 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall x : N, (termsize' _564457 (V x)) = (NUMERAL (BIT1 N0))) /\ (forall f : N, forall args : list term, (termsize' _564457 (Fn f args)) = (@fold_right_with_perm_args N N N.add (@List.map term N (termsize' _564457) args) (NUMERAL (BIT1 N0))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))))))).
Proof. term_align. Qed.

Inductive LEX {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| LEX_R : forall x l x' l', R x x' -> length l = length l' -> LEX R (x::l) (x'::l')
| LEX_rec : forall x l l', LEX R l l' -> LEX R (x::l) (x::l').

Lemma LEX_length {A : Type} (R : A -> A -> Prop) l l' :
  LEX R l l' -> length l = length l'.
Proof.
  induction 1 ; simpl ; now f_equal.
Qed.

Lemma LEX_def {_250280 : Type'} : (@LEX _250280) = (@ε ((prod N (prod N N)) -> (_250280 -> _250280 -> Prop) -> (list _250280) -> (list _250280) -> Prop) (fun LEX' : (prod N (prod N N)) -> (_250280 -> _250280 -> Prop) -> (list _250280) -> (list _250280) -> Prop => forall _564465 : prod N (prod N N), (forall lt2' : _250280 -> _250280 -> Prop, forall l : list _250280, (LEX' _564465 lt2' (@nil _250280) l) = False) /\ (forall h : _250280, forall lt2' : _250280 -> _250280 -> Prop, forall t : list _250280, forall l : list _250280, (LEX' _564465 lt2' (@cons _250280 h t) l) = (@COND Prop (l = (@nil _250280)) False (@COND Prop (lt2' h (@HOLLight_Real_With_N.mappings.hd _250280 l)) ((@lengthN _250280 t) = (@lengthN _250280 (@HOLLight_Real_With_N.mappings.tl _250280 l))) ((h = (@HOLLight_Real_With_N.mappings.hd _250280 l)) /\ (LEX' _564465 lt2' t (@HOLLight_Real_With_N.mappings.tl _250280 l))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 N0))))))))))).
Proof.
  total_align. rewrite is_False. inversion 1.
  rewrite COND_list. destruct l. rewrite is_False. inversion 1.
  simpl. apply COND_intro ; intro H.
  - rewrite <- length_lengthN_equality_eq. apply prop_ext ; intro H'.
    + apply LEX_length in H'. now inversion H'.
    + now left.
  - apply prop_ext.
    + inversion 1 ; easy.
    + intros (H' , H''). rewrite H'. now right.
Qed.

Inductive subterm : term -> term -> Prop :=
| subterm_refl : forall t, subterm t t
| subterm_rec : forall t t' n l, subterm t t' -> List.In t' l -> subterm t (Fn n l).

Lemma subterm_def : subterm = (fun a0 : term => fun a1 : term => forall subterm' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((a1' = a0') \/ (exists a : term, exists f : N, exists args : list term, (a1' = (Fn f args)) /\ ((subterm' a0' a) /\ (@List.In term a args)))) -> subterm' a0' a1') -> subterm' a0 a1).
Proof.
  ind_align'. now apply (subterm_rec x a).
Qed.

Definition psubterm t t' := (subterm t t' /\ t <> t').

Lemma psubterm_def : psubterm = (fun _567009 : term => fun _567010 : term => (subterm _567009 _567010) /\ (~ (_567009 = _567010))).
Proof. exact (eq_refl psubterm). Qed.

Inductive lpo : term -> term -> Prop :=
| lpo_free : forall n t, IN n (free_variables_term t) -> t <> V n -> lpo (V n) t
| lpo_psubterm1 : forall n l n' l' t, List.In t l' -> lpo (Fn n l) t ->
                lpo (Fn n l) (Fn n' l')
| lpo_psubterm2 : forall n l n' l' t, List.In t l' -> t = Fn n l ->
                lpo (Fn n l) (Fn n' l')
| lpo_Fn_smaller : forall n l n' l', n' > n \/ (n' = n /\ (length l' > length l)%nat) ->
         Forall (fun t => lpo t (Fn n' l')) l -> lpo (Fn n l) (Fn n' l')
| lpo_LEX : forall n l l', Forall (fun t => lpo t (Fn n l')) l -> LEX lpo l l' ->
            lpo (Fn n l) (Fn n l').

Fixpoint lpo_ind' P H0 H1 H2 
  (H3 : forall n l n' l', n' > n \/ (n' = n /\ (length l' > length l)%nat) ->
    Forall (fun t : term => P t (Fn n' l')) l -> P (Fn n l) (Fn n' l'))
  (H4 : forall n l l', Forall (fun t : term => P t (Fn n l')) l -> LEX lpo l l' ->
    LEX P l l' -> P (Fn n l) (Fn n l'))
  t t' (H5 : lpo t t') : P t t' :=
  lpo_ind P H0 H1 H2
    (fun n l n' l' H0' H1' => H3 n l n' l' H0' (Forall_ind (Forall (fun t => P t (Fn n' l')))
      (Forall_nil _) 
      (fun t0 l0 H00 _ H10 => Forall_cons _ (lpo_ind' P H0 H1 H2 H3 H4 _ _ H00) H10) H1'))
    (fun n l l' H0' H1' => H4 n l l' (Forall_ind (Forall (fun t => P t (Fn n l')))
      (Forall_nil _) 
      (fun t0 l0 H00 _ H10 => Forall_cons _ (lpo_ind' P H0 H1 H2 H3 H4 _ _ H00) H10) H0')
      H1'
      (LEX_ind _ _ (LEX P)
        (fun t0 l0 t0' l0' H00 H10 => LEX_R P t0 l0 t0' l0' 
          (lpo_ind' P H0 H1 H2 H3 H4 _ _ H00) H10)
        (fun t0 l0 l0' _ H00 => LEX_rec P t0 l0 l0' H00) l l' H1')) t t' H5.

Lemma lt2_def : lpo = (fun a0 : term => fun a1 : term => forall lt2' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((exists x : N, (a0' = (V x)) /\ ((@IN N x (free_variables_term a1')) /\ (~ (a1' = (V x))))) \/ ((exists fs : N, exists sargs : list term, exists ft : N, exists targs : list term, exists si : term, (a0' = (Fn ft targs)) /\ ((a1' = (Fn fs sargs)) /\ ((@List.In term si sargs) /\ ((lt2' (Fn ft targs) si) \/ (si = (Fn ft targs)))))) \/ ((exists fs : N, exists ft : N, exists sargs : list term, exists targs : list term, (a0' = (Fn ft targs)) /\ ((a1' = (Fn fs sargs)) /\ (((N.gt fs ft) \/ ((fs = ft) /\ (N.gt (@lengthN term sargs) (@lengthN term targs)))) /\ (@List.Forall term (fun ti : term => lt2' ti (Fn fs sargs)) targs)))) \/ (exists f : N, exists sargs : list term, exists targs : list term, (a0' = (Fn f targs)) /\ ((a1' = (Fn f sargs)) /\ ((@List.Forall term (fun ti : term => lt2' ti (Fn f sargs)) targs) /\ (@LEX term lt2' targs sargs))))))) -> lt2' a0' a1') -> lt2' a0 a1).
Proof.
  ext t t' ; apply prop_ext ; intro H ;
  [ intros P H' ; apply lpo_ind' ; auto ;
    clear H ; intros ; apply H' ; try breakgoal'
  | apply H ;
    clear t t' H ; intros t t' H ; full_destruct ;
    repeat match goal with H : _ |- _ => rewrite H end ; try now constructor
  ].
  - do 2 right. left. exists n'. exists n. exists l'. exists l.
    repeat split;auto. now rewrite <- length_lengthN_gt_eq.
  - now apply (lpo_psubterm1 _ _ _ _ si).
  - now apply (lpo_psubterm2 _ _ _ _ si).
  - constructor;auto.
  - constructor. right. now rewrite length_lengthN_gt_eq. now rewrite <- H1.
Qed.



