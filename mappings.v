
(* Function unify0 env eqs {measure length eqs} :=
  match eqs with
  | nil => Some env
  | (t,t')::eqs => match t with
    | V n => COND (In n (map fst env))
      (unify0 env ((assoc n env, t') :: eqs))
      (match istriv env n t' with
      | None => None
      | Some true => unify0 env eqs
      | Some false => unify0 ((n,t') :: env) eqs end)
    | Fn n l => match t' with
      | V n' => unify0 env ((V n', Fn n l) :: eqs)
      | Fn n' l' => COND (n = n' /\ lengthN l = lengthN l')
              (unify0 env  (zip l l' ++ eqs)) None end end end.*)
(* Seems to be a very difficult recursion : measured on basically a combination of 
   overall structure of eqs (the sum of the number of symbols appearing in each
   term) and some form of disance inside env definable since it is loopfree. *)

Definition unify : (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term)) := @ε ((prod N (prod N (prod N (prod N N)))) -> (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term))) (fun unify' : (prod N (prod N (prod N (prod N N)))) -> (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term)) => forall _268410 : prod N (prod N (prod N (prod N N))), forall pr : prod (list (prod N term)) (list (prod term term)), (unify' _268410 pr) = (@COND (option (list (prod N term))) (~ (LOOPFREE (@fst (list (prod N term)) (list (prod term term)) pr))) (@None (list (prod N term))) (@COND (option (list (prod N term))) ((@snd (list (prod N term)) (list (prod term term)) pr) = (@nil (prod term term))) (@Some (list (prod N term)) (@fst (list (prod N term)) (list (prod term term)) pr)) (@tpcases (option (list (prod N term))) (fun f : N => fun fargs : list term => fun g : N => fun gargs : list term => @COND (option (list (prod N term))) ((f = g) /\ ((@lengthN term fargs) = (@lengthN term gargs))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@app (prod term term) (@zip term term fargs gargs) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@None (list (prod N term)))) (fun x : N => fun t : term => @COND (option (list (prod N term))) (@List.In N x (@List.map (prod N term) N (@fst N term) (@fst (list (prod N term)) (list (prod term term)) pr))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@cons (prod term term) (@pair term term (@assoc N term x (@fst (list (prod N term)) (list (prod term term)) pr)) t) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@COND (option (list (prod N term))) ((istriv (@fst (list (prod N term)) (list (prod term term)) pr) x t) = Exception) (@None (list (prod N term))) (@COND (option (list (prod N term))) ((istriv (@fst (list (prod N term)) (list (prod term term)) pr) x t) = TT) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr)))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@cons (prod N term) (@pair N term x t) (@fst (list (prod N term)) (list (prod term term)) pr)) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))))) (fun f : N => fun args : list term => fun x : N => unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@cons (prod term term) (@pair term term (V x) (Fn f args)) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@mappings.hd (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr)))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))))))).
Lemma unify_def : unify = (@ε ((prod N (prod N (prod N (prod N N)))) -> (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term))) (fun unify' : (prod N (prod N (prod N (prod N N)))) -> (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term)) => forall _268410 : prod N (prod N (prod N (prod N N))), forall pr : prod (list (prod N term)) (list (prod term term)), (unify' _268410 pr) = (@COND (option (list (prod N term))) (~ (LOOPFREE (@fst (list (prod N term)) (list (prod term term)) pr))) (@None (list (prod N term))) (@COND (option (list (prod N term))) ((@snd (list (prod N term)) (list (prod term term)) pr) = (@nil (prod term term))) (@Some (list (prod N term)) (@fst (list (prod N term)) (list (prod term term)) pr)) (@tpcases (option (list (prod N term))) (fun f : N => fun fargs : list term => fun g : N => fun gargs : list term => @COND (option (list (prod N term))) ((f = g) /\ ((@lengthN term fargs) = (@lengthN term gargs))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@app (prod term term) (@zip term term fargs gargs) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@None (list (prod N term)))) (fun x : N => fun t : term => @COND (option (list (prod N term))) (@List.In N x (@List.map (prod N term) N (@fst N term) (@fst (list (prod N term)) (list (prod term term)) pr))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@cons (prod term term) (@pair term term (@assoc N term x (@fst (list (prod N term)) (list (prod term term)) pr)) t) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@COND (option (list (prod N term))) ((istriv (@fst (list (prod N term)) (list (prod term term)) pr) x t) = Exception) (@None (list (prod N term))) (@COND (option (list (prod N term))) ((istriv (@fst (list (prod N term)) (list (prod term term)) pr) x t) = TT) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr)))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@cons (prod N term) (@pair N term x t) (@fst (list (prod N term)) (list (prod term term)) pr)) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))))) (fun f : N => fun args : list term => fun x : N => unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@cons (prod term term) (@pair term term (V x) (Fn f args)) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@mappings.hd (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr)))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0))))))))))))).
Proof. exact (eq_refl unify). Qed.

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
  ext hyps. ind_align'.
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

Definition insert {A : Type'} (a : A) l := COND (In a l) l (a :: l).

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
(* Logic/given.ml *)
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
  - rewrite H. now right.
Qed.


Inductive lpresproof (hyps : Ensemble (Ensemble form)) : list (Ensemble form) -> Prop :=
  | lpresproof_assumption : forall cl, IN cl hyps -> lpresproof hyps (cl::nil)
  | lpresproof_resolve : forall f cl cl' l, lpresproof hyps (cl::l) ->
                        (IN cl' hyps \/ In cl' l) -> IN f cl -> IN (FNot f) cl' ->
                        lpresproof hyps ((resolve f cl cl')::cl::l).

Lemma lpresproof_def : lpresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : list (form -> Prop) => forall lpresproof' : (list (form -> Prop)) -> Prop, (forall a' : list (form -> Prop), ((exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (@IN (form -> Prop) cl hyps')) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists lis : list (form -> Prop), exists p : form, (a' = (@cons (form -> Prop) (resolve p c1 c2) (@cons (form -> Prop) c1 lis))) /\ ((lpresproof' (@cons (form -> Prop) c1 lis)) /\ (((@IN (form -> Prop) c2 hyps') \/ (@List.In (form -> Prop) c2 lis)) /\ ((@IN form p c1) /\ (@IN form (FNot p) c2)))))) -> lpresproof' a') -> lpresproof' a).
Proof.
  ext hyps. ind_align' ; right ; auto. 
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
                        (IN cl' hyps \/ In cl' l) -> isaresolvent cl0 (cl,cl') ->
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
  - rewrite N.add_assoc , H. now right.
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
  ext hyps sos. ind_align' ; rewrite H ;
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
  ext hyps sos. ind_align'.
  apply (sresproof_rm_opposable1 hyps sos cl1 cl2) ; auto. now exists i'.
  apply (sresproof_rm_opposable2 hyps sos cl1 cl2) ; auto. now exists i'.
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
  ext hyps. ind_align' ; right ; auto.
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
  ext v hyps. ind_align' ; right ; auto.
Qed.

Definition propflip TrueVar f := COND (negative f = pholds TrueVar f) f (FNot f).

Lemma propflip_def : propflip = (fun _467005 : form -> Prop => fun _467006 : form => @COND form ((negative _467006) = (pholds _467005 _467006)) _467006 (FNot _467006)).
Proof. exact (eq_refl propflip). Qed.
(*
Inductive presproof (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | presproof_assumption : forall cl, IN cl hyps -> presproof hyps cl
  | presproof_resolve : forall f cl cl', presproof hyps cl ->
                        presproof hyps cl' -> IN f cl -> IN (FNot f) cl' ->
                        presproof hyps (resolve f cl cl'). 

Definition posresproof : ((form -> Prop) -> Prop) -> (form -> Prop) -> Prop := fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall posresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((posresproof' cl1) /\ ((posresproof' cl2) /\ (((allpositive cl1) \/ (allpositive cl2)) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_622 : form => exists p : form, @SETSPEC form GEN_PVAR_622 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_623 : form => exists p : form, @SETSPEC form GEN_PVAR_623 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> posresproof' a') -> posresproof' a.
Lemma posresproof_def : posresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall posresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((posresproof' cl1) /\ ((posresproof' cl2) /\ (((allpositive cl1) \/ (allpositive cl2)) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_622 : form => exists p : form, @SETSPEC form GEN_PVAR_622 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_623 : form => exists p : form, @SETSPEC form GEN_PVAR_623 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> posresproof' a') -> posresproof' a).
Proof. exact (eq_refl posresproof). Qed.

Inductive presproof (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | presproof_assumption : forall cl, IN cl hyps -> presproof hyps cl
  | presproof_resolve : forall f cl cl', presproof hyps cl ->
                        presproof hyps cl' -> IN f cl -> IN (FNot f) cl' ->
                        presproof hyps (resolve f cl cl'). 

Definition semresproof {A : Type'} : (prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) -> ((form -> Prop) -> Prop) -> (form -> Prop) -> Prop := fun M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((semresproof' cl1) /\ ((semresproof' cl2) /\ (((~ (forall v : N -> A, @holds A M v (interp cl1))) \/ (~ (forall v : N -> A, @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_629 : form => exists p : form, @SETSPEC form GEN_PVAR_629 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_630 : form => exists p : form, @SETSPEC form GEN_PVAR_630 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof' a') -> semresproof' a.
Lemma semresproof_def {A : Type'} : (@semresproof A) = (fun M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((semresproof' cl1) /\ ((semresproof' cl2) /\ (((~ (forall v : N -> A, @holds A M v (interp cl1))) \/ (~ (forall v : N -> A, @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_629 : form => exists p : form, @SETSPEC form GEN_PVAR_629 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_630 : form => exists p : form, @SETSPEC form GEN_PVAR_630 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof' a') -> semresproof' a).
Proof. exact (eq_refl (@semresproof A)). Qed.

Inductive presproof (hyps : Ensemble (Ensemble form)) : Ensemble form -> Prop :=
  | presproof_assumption : forall cl, IN cl hyps -> presproof hyps cl
  | presproof_resolve : forall f cl cl', presproof hyps cl ->
                        presproof hyps cl' -> IN f cl -> IN (FNot f) cl' ->
                        presproof hyps (resolve f cl cl'). 

Definition semresproof2 {A : Type'} : (prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop))) -> ((form -> Prop) -> Prop) -> (form -> Prop) -> Prop := fun M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof2' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((semresproof2' cl1) /\ ((semresproof2' cl2) /\ (((~ (forall v : N -> A, (@valuation A M v) -> @holds A M v (interp cl1))) \/ (~ (forall v : N -> A, (@valuation A M v) -> @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_636 : form => exists p : form, @SETSPEC form GEN_PVAR_636 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_637 : form => exists p : form, @SETSPEC form GEN_PVAR_637 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof2' a') -> semresproof2' a.
Lemma semresproof2_def {A : Type'} : (@semresproof2 A) = (fun M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof2' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@Ensembles.Union form (@Ensembles.Setminus form cl1 ps1) (@Ensembles.Setminus form cl2' ps2)))) /\ ((semresproof2' cl1) /\ ((semresproof2' cl2) /\ (((~ (forall v : N -> A, (@valuation A M v) -> @holds A M v (interp cl1))) \/ (~ (forall v : N -> A, (@valuation A M v) -> @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@Ensembles.Included form ps1 cl1) /\ ((@Ensembles.Included form ps2 cl2') /\ ((~ (ps1 = (@Ensembles.Empty_set form))) /\ ((~ (ps2 = (@Ensembles.Empty_set form))) /\ ((exists i' : N -> term, Unifies i' (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_636 : form => exists p : form, @SETSPEC form GEN_PVAR_636 (@IN form p ps2) (FNot p))))) /\ ((mgu (@Ensembles.Union form ps1 (@GSPEC form (fun GEN_PVAR_637 : form => exists p : form, @SETSPEC form GEN_PVAR_637 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof2' a') -> semresproof2' a).
Proof. exact (eq_refl (@semresproof2 A)). Qed. *)
