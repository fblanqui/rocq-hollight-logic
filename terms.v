Require Import Stdlib.NArith.BinNat Stdlib.Reals.Reals mathcomp.classical.classical_sets mathcomp.classical.cardinality mathcomp.ssreflect.choice mathcomp.ssreflect.ssrbool HOLLight_Real_With_N.mappings HOLLight_Logic1.mappings_coq_hol_light HOLLight_Logic_fole.mappings HOLLight_Logic.mappings.
Definition o {A B C : Type'} : (B -> C) -> (A -> B) -> A -> C := fun f : B -> C => fun g : A -> B => fun x : A => f (g x).
Lemma o_def {A B C : Type'} : (@o A B C) = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)).
Proof. exact (REFL (@o A B C)). Qed.
Definition I {A : Type'} : A -> A := fun x : A => x.
Lemma I_def {A : Type'} : (@I A) = (fun x : A => x).
Proof. exact (REFL (@I A)). Qed.
Definition _SEQPATTERN {A B : Type'} : (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop := fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x).
Lemma _SEQPATTERN_def {A B : Type'} : (@_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)).
Proof. exact (REFL (@_SEQPATTERN A B)). Qed.
Definition _GUARDED_PATTERN : Prop -> Prop -> Prop -> Prop := fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r).
Lemma _GUARDED_PATTERN_def : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Proof. exact (REFL _GUARDED_PATTERN). Qed.
Definition _MATCH {A B : Type'} : A -> (A -> B -> Prop) -> B := fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False)).
Lemma _MATCH_def {A B : Type'} : (@_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))).
Proof. exact (REFL (@_MATCH A B)). Qed.
Definition _FUNCTION {A B : Type'} : (A -> B -> Prop) -> A -> B := fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False)).
Lemma _FUNCTION_def {A B : Type'} : (@_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))).
Proof. exact (REFL (@_FUNCTION A B)). Qed.
Definition CURRY {A B C : Type'} : ((prod A B) -> C) -> A -> B -> C := fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285).
Lemma CURRY_def {A B C : Type'} : (@CURRY A B C) = (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285)).
Proof. exact (REFL (@CURRY A B C)). Qed.
Definition UNCURRY {A B C : Type'} : (A -> B -> C) -> (prod A B) -> C := fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305).
Lemma UNCURRY_def {A B C : Type'} : (@UNCURRY A B C) = (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305)).
Proof. exact (REFL (@UNCURRY A B C)). Qed.
Definition PASSOC {A B C D : Type'} : ((prod (prod A B) C) -> D) -> (prod A (prod B C)) -> D := fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322))).
Lemma PASSOC_def {A B C D : Type'} : (@PASSOC A B C D) = (fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322)))).
Proof. exact (REFL (@PASSOC A B C D)). Qed.
Definition minimal : (N -> Prop) -> N := fun _6536 : N -> Prop => @ε N (fun n : N => (_6536 n) /\ (forall m : N, (N.lt m n) -> ~ (_6536 m))).
Lemma minimal_def : minimal = (fun _6536 : N -> Prop => @ε N (fun n : N => (_6536 n) /\ (forall m : N, (N.lt m n) -> ~ (_6536 m)))).
Proof. exact (REFL minimal). Qed.
Definition FNIL {A : Type'} : N -> A := fun _17624 : N => @ε A (fun x : A => True).
Lemma FNIL_def {A : Type'} : (@FNIL A) = (fun _17624 : N => @ε A (fun x : A => True)).
Proof. exact (REFL (@FNIL A)). Qed.
Definition OUTL {A B : Type'} : (Datatypes.sum A B) -> A := @ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A => forall _17649 : prod N (prod N (prod N N)), forall x : A, (OUTL' _17649 (@inl A B x)) = x) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))).
Lemma OUTL_def {A B : Type'} : (@OUTL A B) = (@ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A => forall _17649 : prod N (prod N (prod N N)), forall x : A, (OUTL' _17649 (@inl A B x)) = x) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))).
Proof. exact (REFL (@OUTL A B)). Qed.
Definition OUTR {A B : Type'} : (Datatypes.sum A B) -> B := @ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B => forall _17651 : prod N (prod N (prod N N)), forall y : B, (OUTR' _17651 (@inr A B y)) = y) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).
Lemma OUTR_def {A B : Type'} : (@OUTR A B) = (@ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B => forall _17651 : prod N (prod N (prod N N)), forall y : B, (OUTR' _17651 (@inr A B y)) = y) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))).
Proof. exact (REFL (@OUTR A B)). Qed.
Definition _22857 : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii := fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7).
Lemma _22857_def : _22857 = (fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (REFL _22857). Qed.
Definition ASCII : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii := _22857.
Lemma ASCII_def : ASCII = _22857.
Proof. exact (REFL ASCII). Qed.
Definition sqrt : R -> R := fun _27149 : R => @ε R (fun y : R => ((Rsgn y) = (Rsgn _27149)) /\ ((Rpow y (NUMERAL (BIT0 (BIT1 N0)))) = (Rabs _27149))).
Lemma sqrt_def : sqrt = (fun _27149 : R => @ε R (fun y : R => ((Rsgn y) = (Rsgn _27149)) /\ ((Rpow y (NUMERAL (BIT0 (BIT1 N0)))) = (Rabs _27149)))).
Proof. exact (REFL sqrt). Qed.
Definition DECIMAL : N -> N -> R := fun _27828 : N => fun _27829 : N => Rdiv (R_of_N _27828) (R_of_N _27829).
Lemma DECIMAL_def : DECIMAL = (fun _27828 : N => fun _27829 : N => Rdiv (R_of_N _27828) (R_of_N _27829)).
Proof. exact (REFL DECIMAL). Qed.
Definition eq2 {A : Type'} : A -> A -> (A -> A -> Prop) -> Prop := fun _29602 : A => fun _29603 : A => fun _29604 : A -> A -> Prop => _29604 _29602 _29603.
Lemma eq2_def {A : Type'} : (@eq2 A) = (fun _29602 : A => fun _29603 : A => fun _29604 : A -> A -> Prop => _29604 _29602 _29603).
Proof. exact (REFL (@eq2 A)). Qed.
Definition int_mod : Z -> Z -> Z -> Prop := fun _29664 : Z => fun _29665 : Z => fun _29666 : Z => Z.divide _29664 (Z.sub _29665 _29666).
Lemma int_mod_def : int_mod = (fun _29664 : Z => fun _29665 : Z => fun _29666 : Z => Z.divide _29664 (Z.sub _29665 _29666)).
Proof. exact (REFL int_mod). Qed.
Definition num_of_int : Z -> N := fun _31234 : Z => @ε N (fun n : N => (Z_of_N n) = _31234).
Lemma num_of_int_def : num_of_int = (fun _31234 : Z => @ε N (fun n : N => (Z_of_N n) = _31234)).
Proof. exact (REFL num_of_int). Qed.
Definition num_divides : N -> N -> Prop := fun _31266 : N => fun _31267 : N => Z.divide (Z_of_N _31266) (Z_of_N _31267).
Lemma num_divides_def : num_divides = (fun _31266 : N => fun _31267 : N => Z.divide (Z_of_N _31266) (Z_of_N _31267)).
Proof. exact (REFL num_divides). Qed.
Definition num_mod : N -> N -> N -> Prop := fun _31278 : N => fun _31279 : N => fun _31280 : N => int_mod (Z_of_N _31278) (Z_of_N _31279) (Z_of_N _31280).
Lemma num_mod_def : num_mod = (fun _31278 : N => fun _31279 : N => fun _31280 : N => int_mod (Z_of_N _31278) (Z_of_N _31279) (Z_of_N _31280)).
Proof. exact (REFL num_mod). Qed.
Definition num_coprime : (prod N N) -> Prop := fun _31299 : prod N N => int_coprime (@pair Z Z (Z_of_N (@fst N N _31299)) (Z_of_N (@snd N N _31299))).
Lemma num_coprime_def : num_coprime = (fun _31299 : prod N N => int_coprime (@pair Z Z (Z_of_N (@fst N N _31299)) (Z_of_N (@snd N N _31299)))).
Proof. exact (REFL num_coprime). Qed.
Definition num_gcd : (prod N N) -> N := fun _31308 : prod N N => num_of_int (int_gcd (@pair Z Z (Z_of_N (@fst N N _31308)) (Z_of_N (@snd N N _31308)))).
Lemma num_gcd_def : num_gcd = (fun _31308 : prod N N => num_of_int (int_gcd (@pair Z Z (Z_of_N (@fst N N _31308)) (Z_of_N (@snd N N _31308))))).
Proof. exact (REFL num_gcd). Qed.
Definition num_lcm : (prod N N) -> N := fun _31317 : prod N N => num_of_int (int_lcm (@pair Z Z (Z_of_N (@fst N N _31317)) (Z_of_N (@snd N N _31317)))).
Lemma num_lcm_def : num_lcm = (fun _31317 : prod N N => num_of_int (int_lcm (@pair Z Z (Z_of_N (@fst N N _31317)) (Z_of_N (@snd N N _31317))))).
Proof. exact (REFL num_lcm). Qed.
Definition prime : N -> Prop := fun _32102 : N => (~ (_32102 = (NUMERAL (BIT1 N0)))) /\ (forall x : N, (num_divides x _32102) -> (x = (NUMERAL (BIT1 N0))) \/ (x = _32102)).
Lemma prime_def : prime = (fun _32102 : N => (~ (_32102 = (NUMERAL (BIT1 N0)))) /\ (forall x : N, (num_divides x _32102) -> (x = (NUMERAL (BIT1 N0))) \/ (x = _32102))).
Proof. exact (REFL prime). Qed.
Definition real_zpow : R -> Z -> R := fun _32260 : R => fun _32261 : Z => @COND R (Z.le (Z_of_N (NUMERAL N0)) _32261) (Rpow _32260 (num_of_int _32261)) (Rinv (Rpow _32260 (num_of_int (Z.opp _32261)))).
Lemma real_zpow_def : real_zpow = (fun _32260 : R => fun _32261 : Z => @COND R (Z.le (Z_of_N (NUMERAL N0)) _32261) (Rpow _32260 (num_of_int _32261)) (Rinv (Rpow _32260 (num_of_int (Z.opp _32261))))).
Proof. exact (REFL real_zpow). Qed.
Definition INFINITE {A : Type'} : (A -> Prop) -> Prop := fun _32488 : A -> Prop => ~ (@finite_set A _32488).
Lemma INFINITE_def {A : Type'} : (@INFINITE A) = (fun _32488 : A -> Prop => ~ (@finite_set A _32488)).
Proof. exact (REFL (@INFINITE A)). Qed.
Definition INJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32505 : A -> B => fun _32506 : A -> Prop => fun _32507 : B -> Prop => (forall x : A, (@IN A x _32506) -> @IN B (_32505 x) _32507) /\ (forall x : A, forall y : A, ((@IN A x _32506) /\ ((@IN A y _32506) /\ ((_32505 x) = (_32505 y)))) -> x = y).
Lemma INJ_def {A B : Type'} : (@INJ A B) = (fun _32505 : A -> B => fun _32506 : A -> Prop => fun _32507 : B -> Prop => (forall x : A, (@IN A x _32506) -> @IN B (_32505 x) _32507) /\ (forall x : A, forall y : A, ((@IN A x _32506) /\ ((@IN A y _32506) /\ ((_32505 x) = (_32505 y)))) -> x = y)).
Proof. exact (REFL (@INJ A B)). Qed.
Definition SURJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32526 : A -> B => fun _32527 : A -> Prop => fun _32528 : B -> Prop => (forall x : A, (@IN A x _32527) -> @IN B (_32526 x) _32528) /\ (forall x : B, (@IN B x _32528) -> exists y : A, (@IN A y _32527) /\ ((_32526 y) = x)).
Lemma SURJ_def {A B : Type'} : (@SURJ A B) = (fun _32526 : A -> B => fun _32527 : A -> Prop => fun _32528 : B -> Prop => (forall x : A, (@IN A x _32527) -> @IN B (_32526 x) _32528) /\ (forall x : B, (@IN B x _32528) -> exists y : A, (@IN A y _32527) /\ ((_32526 y) = x))).
Proof. exact (REFL (@SURJ A B)). Qed.
Definition BIJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32547 : A -> B => fun _32548 : A -> Prop => fun _32549 : B -> Prop => (@INJ A B _32547 _32548 _32549) /\ (@SURJ A B _32547 _32548 _32549).
Lemma BIJ_def {A B : Type'} : (@BIJ A B) = (fun _32547 : A -> B => fun _32548 : A -> Prop => fun _32549 : B -> Prop => (@INJ A B _32547 _32548 _32549) /\ (@SURJ A B _32547 _32548 _32549)).
Proof. exact (REFL (@BIJ A B)). Qed.
Definition CHOICE {A : Type'} : (A -> Prop) -> A := fun _32568 : A -> Prop => @ε A (fun x : A => @IN A x _32568).
Lemma CHOICE_def {A : Type'} : (@CHOICE A) = (fun _32568 : A -> Prop => @ε A (fun x : A => @IN A x _32568)).
Proof. exact (REFL (@CHOICE A)). Qed.
Definition REST {A : Type'} : (A -> Prop) -> A -> Prop := fun _32573 : A -> Prop => @DELETE A _32573 (@CHOICE A _32573).
Lemma REST_def {A : Type'} : (@REST A) = (fun _32573 : A -> Prop => @DELETE A _32573 (@CHOICE A _32573)).
Proof. exact (REFL (@REST A)). Qed.
Definition FINREC {A B : Type'} : (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop) (fun FINREC' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop => forall _42175 : prod N (prod N (prod N (prod N (prod N N)))), (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (FINREC' _42175 f b s a (NUMERAL N0)) = ((s = (@set0 A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : N, forall a : B, forall f : A -> B -> B, (FINREC' _42175 f b s a (N.succ n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((FINREC' _42175 f b (@DELETE A s x) c n) /\ (a = (f x c)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))).
Lemma FINREC_def {A B : Type'} : (@FINREC A B) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop) (fun FINREC' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop => forall _42175 : prod N (prod N (prod N (prod N (prod N N)))), (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (FINREC' _42175 f b s a (NUMERAL N0)) = ((s = (@set0 A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : N, forall a : B, forall f : A -> B -> B, (FINREC' _42175 f b s a (N.succ n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((FINREC' _42175 f b (@DELETE A s x) c n) /\ (a = (f x c)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof. exact (REFL (@FINREC A B)). Qed.
Definition HAS_SIZE {A : Type'} : (A -> Prop) -> N -> Prop := fun _43403 : A -> Prop => fun _43404 : N => (@finite_set A _43403) /\ ((@card A _43403) = _43404).
Lemma HAS_SIZE_def {A : Type'} : (@HAS_SIZE A) = (fun _43403 : A -> Prop => fun _43404 : N => (@finite_set A _43403) /\ ((@card A _43403) = _43404)).
Proof. exact (REFL (@HAS_SIZE A)). Qed.
Definition CROSS {A B : Type'} : (A -> Prop) -> (B -> Prop) -> (prod A B) -> Prop := fun _47322 : A -> Prop => fun _47323 : B -> Prop => @GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x _47322) /\ (@IN B y _47323)) (@pair A B x y)).
Lemma CROSS_def {A B : Type'} : (@CROSS A B) = (fun _47322 : A -> Prop => fun _47323 : B -> Prop => @GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x _47322) /\ (@IN B y _47323)) (@pair A B x y))).
Proof. exact (REFL (@CROSS A B)). Qed.
Definition ARB {A : Type'} : A := @ε A (fun x : A => False).
Lemma ARB_def {A : Type'} : (@ARB A) = (@ε A (fun x : A => False)).
Proof. exact (REFL (@ARB A)). Qed.
Definition EXTENSIONAL {A B : Type'} : (A -> Prop) -> (A -> B) -> Prop := fun _48096 : A -> Prop => @GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x _48096)) -> (f x) = (@ARB B)) f).
Lemma EXTENSIONAL_def {A B : Type'} : (@EXTENSIONAL A B) = (fun _48096 : A -> Prop => @GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x _48096)) -> (f x) = (@ARB B)) f)).
Proof. exact (REFL (@EXTENSIONAL A B)). Qed.
Definition RESTRICTION {A B : Type'} : (A -> Prop) -> (A -> B) -> A -> B := fun _48148 : A -> Prop => fun _48149 : A -> B => fun _48150 : A => @COND B (@IN A _48150 _48148) (_48149 _48150) (@ARB B).
Lemma RESTRICTION_def {A B : Type'} : (@RESTRICTION A B) = (fun _48148 : A -> Prop => fun _48149 : A -> B => fun _48150 : A => @COND B (@IN A _48150 _48148) (_48149 _48150) (@ARB B)).
Proof. exact (REFL (@RESTRICTION A B)). Qed.
Definition cartesian_product {A K : Type'} : (K -> Prop) -> (K -> A -> Prop) -> (K -> A) -> Prop := fun _48343 : K -> Prop => fun _48344 : K -> A -> Prop => @GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A _48343 f) /\ (forall i : K, (@IN K i _48343) -> @IN A (f i) (_48344 i))) f).
Lemma cartesian_product_def {A K : Type'} : (@cartesian_product A K) = (fun _48343 : K -> Prop => fun _48344 : K -> A -> Prop => @GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A _48343 f) /\ (forall i : K, (@IN K i _48343) -> @IN A (f i) (_48344 i))) f)).
Proof. exact (REFL (@cartesian_product A K)). Qed.
Definition product_map {A B K : Type'} : (K -> Prop) -> (K -> A -> B) -> (K -> A) -> K -> B := fun _49392 : K -> Prop => fun _49393 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _49392 (fun i : K => _49393 i (x i)).
Lemma product_map_def {A B K : Type'} : (@product_map A B K) = (fun _49392 : K -> Prop => fun _49393 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _49392 (fun i : K => _49393 i (x i))).
Proof. exact (REFL (@product_map A B K)). Qed.
Definition disjoint_union {A K : Type'} : (K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop := fun _49528 : K -> Prop => fun _49529 : K -> A -> Prop => @GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i _49528) /\ (@IN A x (_49529 i))) (@pair K A i x)).
Lemma disjoint_union_def {A K : Type'} : (@disjoint_union A K) = (fun _49528 : K -> Prop => fun _49529 : K -> A -> Prop => @GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i _49528) /\ (@IN A x (_49529 i))) (@pair K A i x))).
Proof. exact (REFL (@disjoint_union A K)). Qed.
Definition pairwise {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _56616 : A -> A -> Prop => fun _56617 : A -> Prop => forall x : A, forall y : A, ((@IN A x _56617) /\ ((@IN A y _56617) /\ (~ (x = y)))) -> _56616 x y.
Lemma pairwise_def {A : Type'} : (@pairwise A) = (fun _56616 : A -> A -> Prop => fun _56617 : A -> Prop => forall x : A, forall y : A, ((@IN A x _56617) /\ ((@IN A y _56617) /\ (~ (x = y)))) -> _56616 x y).
Proof. exact (REFL (@pairwise A)). Qed.
Definition UNION_OF {A : Type'} : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57329 : ((A -> Prop) -> Prop) -> Prop => fun _57330 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57329 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57330 c) /\ ((@UNIONS A u) = s)).
Lemma UNION_OF_def {A : Type'} : (@UNION_OF A) = (fun _57329 : ((A -> Prop) -> Prop) -> Prop => fun _57330 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57329 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57330 c) /\ ((@UNIONS A u) = s))).
Proof. exact (REFL (@UNION_OF A)). Qed.
Definition INTERSECTION_OF {A : Type'} : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57341 : ((A -> Prop) -> Prop) -> Prop => fun _57342 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57341 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57342 c) /\ ((@INTERS A u) = s)).
Lemma INTERSECTION_OF_def {A : Type'} : (@INTERSECTION_OF A) = (fun _57341 : ((A -> Prop) -> Prop) -> Prop => fun _57342 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57341 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57342 c) /\ ((@INTERS A u) = s))).
Proof. exact (REFL (@INTERSECTION_OF A)). Qed.
Definition ARBITRARY {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _57477 : (A -> Prop) -> Prop => True.
Lemma ARBITRARY_def {A : Type'} : (@ARBITRARY A) = (fun _57477 : (A -> Prop) -> Prop => True).
Proof. exact (REFL (@ARBITRARY A)). Qed.
Definition le_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64071 : A -> Prop => fun _64072 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64071) -> @IN B (f x) _64072) /\ (forall x : A, forall y : A, ((@IN A x _64071) /\ ((@IN A y _64071) /\ ((f x) = (f y)))) -> x = y).
Lemma le_c_def {A B : Type'} : (@le_c A B) = (fun _64071 : A -> Prop => fun _64072 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64071) -> @IN B (f x) _64072) /\ (forall x : A, forall y : A, ((@IN A x _64071) /\ ((@IN A y _64071) /\ ((f x) = (f y)))) -> x = y)).
Proof. exact (REFL (@le_c A B)). Qed.
Definition lt_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64083 : A -> Prop => fun _64084 : B -> Prop => (@le_c A B _64083 _64084) /\ (~ (@le_c B A _64084 _64083)).
Lemma lt_c_def {A B : Type'} : (@lt_c A B) = (fun _64083 : A -> Prop => fun _64084 : B -> Prop => (@le_c A B _64083 _64084) /\ (~ (@le_c B A _64084 _64083))).
Proof. exact (REFL (@lt_c A B)). Qed.
Definition eq_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64095 : A -> Prop => fun _64096 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64095) -> @IN B (f x) _64096) /\ (forall y : B, (@IN B y _64096) -> @ex1 A (fun x : A => (@IN A x _64095) /\ ((f x) = y))).
Lemma eq_c_def {A B : Type'} : (@eq_c A B) = (fun _64095 : A -> Prop => fun _64096 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64095) -> @IN B (f x) _64096) /\ (forall y : B, (@IN B y _64096) -> @ex1 A (fun x : A => (@IN A x _64095) /\ ((f x) = y)))).
Proof. exact (REFL (@eq_c A B)). Qed.
Definition ge_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64107 : A -> Prop => fun _64108 : B -> Prop => @le_c B A _64108 _64107.
Lemma ge_c_def {A B : Type'} : (@ge_c A B) = (fun _64107 : A -> Prop => fun _64108 : B -> Prop => @le_c B A _64108 _64107).
Proof. exact (REFL (@ge_c A B)). Qed.
Definition gt_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64119 : A -> Prop => fun _64120 : B -> Prop => @lt_c B A _64120 _64119.
Lemma gt_c_def {A B : Type'} : (@gt_c A B) = (fun _64119 : A -> Prop => fun _64120 : B -> Prop => @lt_c B A _64120 _64119).
Proof. exact (REFL (@gt_c A B)). Qed.
Definition COUNTABLE {A : Type'} : (A -> Prop) -> Prop := fun _64270 : A -> Prop => @ge_c N A (@setT N) _64270.
Lemma COUNTABLE_def {A : Type'} : (@COUNTABLE A) = (fun _64270 : A -> Prop => @ge_c N A (@setT N) _64270).
Proof. exact (REFL (@COUNTABLE A)). Qed.
Definition sup : (R -> Prop) -> R := fun _64275 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _64275) -> Rle x a) /\ (forall b : R, (forall x : R, (@IN R x _64275) -> Rle x b) -> Rle a b)).
Lemma sup_def : sup = (fun _64275 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _64275) -> Rle x a) /\ (forall b : R, (forall x : R, (@IN R x _64275) -> Rle x b) -> Rle a b))).
Proof. exact (REFL sup). Qed.
Definition inf : (R -> Prop) -> R := fun _65134 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _65134) -> Rle a x) /\ (forall b : R, (forall x : R, (@IN R x _65134) -> Rle b x) -> Rle b a)).
Lemma inf_def : inf = (fun _65134 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _65134) -> Rle a x) /\ (forall b : R, (forall x : R, (@IN R x _65134) -> Rle b x) -> Rle b a))).
Proof. exact (REFL inf). Qed.
Definition has_inf : (R -> Prop) -> R -> Prop := fun _66484 : R -> Prop => fun _66485 : R => forall c : R, (forall x : R, (@IN R x _66484) -> Rle c x) = (Rle c _66485).
Lemma has_inf_def : has_inf = (fun _66484 : R -> Prop => fun _66485 : R => forall c : R, (forall x : R, (@IN R x _66484) -> Rle c x) = (Rle c _66485)).
Proof. exact (REFL has_inf). Qed.
Definition has_sup : (R -> Prop) -> R -> Prop := fun _66496 : R -> Prop => fun _66497 : R => forall c : R, (forall x : R, (@IN R x _66496) -> Rle x c) = (Rle _66497 c).
Lemma has_sup_def : has_sup = (fun _66496 : R -> Prop => fun _66497 : R => forall c : R, (forall x : R, (@IN R x _66496) -> Rle x c) = (Rle _66497 c)).
Proof. exact (REFL has_sup). Qed.
Definition neutral {A : Type'} : (A -> A -> A) -> A := fun _68834 : A -> A -> A => @ε A (fun x : A => forall y : A, ((_68834 x y) = y) /\ ((_68834 y x) = y)).
Lemma neutral_def {A : Type'} : (@neutral A) = (fun _68834 : A -> A -> A => @ε A (fun x : A => forall y : A, ((_68834 x y) = y) /\ ((_68834 y x) = y))).
Proof. exact (REFL (@neutral A)). Qed.
Definition monoidal {A : Type'} : (A -> A -> A) -> Prop := fun _68839 : A -> A -> A => (forall x : A, forall y : A, (_68839 x y) = (_68839 y x)) /\ ((forall x : A, forall y : A, forall z : A, (_68839 x (_68839 y z)) = (_68839 (_68839 x y) z)) /\ (forall x : A, (_68839 (@neutral A _68839) x) = x)).
Lemma monoidal_def {A : Type'} : (@monoidal A) = (fun _68839 : A -> A -> A => (forall x : A, forall y : A, (_68839 x y) = (_68839 y x)) /\ ((forall x : A, forall y : A, forall z : A, (_68839 x (_68839 y z)) = (_68839 (_68839 x y) z)) /\ (forall x : A, (_68839 (@neutral A _68839) x) = x))).
Proof. exact (REFL (@monoidal A)). Qed.
Definition support {A B : Type'} : (B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop := fun _68924 : B -> B -> B => fun _68925 : A -> B => fun _68926 : A -> Prop => @GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x _68926) /\ (~ ((_68925 x) = (@neutral B _68924)))) x).
Lemma support_def {A B : Type'} : (@support A B) = (fun _68924 : B -> B -> B => fun _68925 : A -> B => fun _68926 : A -> Prop => @GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x _68926) /\ (~ ((_68925 x) = (@neutral B _68924)))) x)).
Proof. exact (REFL (@support A B)). Qed.
Definition iterate {A B : Type'} : (B -> B -> B) -> (A -> Prop) -> (A -> B) -> B := fun _68945 : B -> B -> B => fun _68946 : A -> Prop => fun _68947 : A -> B => @COND B (@finite_set A (@support A B _68945 _68947 _68946)) (@fold_set A B (fun x : A => fun a : B => _68945 (_68947 x) a) (@support A B _68945 _68947 _68946) (@neutral B _68945)) (@neutral B _68945).
Lemma iterate_def {A B : Type'} : (@iterate A B) = (fun _68945 : B -> B -> B => fun _68946 : A -> Prop => fun _68947 : A -> B => @COND B (@finite_set A (@support A B _68945 _68947 _68946)) (@fold_set A B (fun x : A => fun a : B => _68945 (_68947 x) a) (@support A B _68945 _68947 _68946) (@neutral B _68945)) (@neutral B _68945)).
Proof. exact (REFL (@iterate A B)). Qed.
Definition iterato {A K : Type'} : (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A := @ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) (fun itty : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => forall _76701 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (itty _76701 dom neut op ltle k f) = (@COND A ((@finite_set K (@GSPEC K (fun GEN_PVAR_265 : K => exists i : K, @SETSPEC K GEN_PVAR_265 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_266 : K => exists i : K, @SETSPEC K GEN_PVAR_266 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) (@LET K A (fun i : K => @LET_END A (op (f i) (itty _76701 dom neut op ltle (@GSPEC K (fun GEN_PVAR_267 : K => exists j : K, @SETSPEC K GEN_PVAR_267 ((@IN K j (@DELETE K k i)) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j)) f))) (@COND K (exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) (@ε K (fun i : K => (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i)))) (@ε K (fun i : K => (@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))))))) neut)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))).
Lemma iterato_def {A K : Type'} : (@iterato A K) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) (fun itty : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => forall _76701 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (itty _76701 dom neut op ltle k f) = (@COND A ((@finite_set K (@GSPEC K (fun GEN_PVAR_265 : K => exists i : K, @SETSPEC K GEN_PVAR_265 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_266 : K => exists i : K, @SETSPEC K GEN_PVAR_266 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) (@LET K A (fun i : K => @LET_END A (op (f i) (itty _76701 dom neut op ltle (@GSPEC K (fun GEN_PVAR_267 : K => exists j : K, @SETSPEC K GEN_PVAR_267 ((@IN K j (@DELETE K k i)) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j)) f))) (@COND K (exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) (@ε K (fun i : K => (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i)))) (@ε K (fun i : K => (@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))))))) neut)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))).
Proof. exact (REFL (@iterato A K)). Qed.
Definition nproduct {A : Type'} : (A -> Prop) -> (A -> N) -> N := @iterate A N N.mul.
Lemma nproduct_def {A : Type'} : (@nproduct A) = (@iterate A N N.mul).
Proof. exact (REFL (@nproduct A)). Qed.
Definition iproduct {A : Type'} : (A -> Prop) -> (A -> Z) -> Z := @iterate A Z Z.mul.
Lemma iproduct_def {A : Type'} : (@iproduct A) = (@iterate A Z Z.mul).
Proof. exact (REFL (@iproduct A)). Qed.
Definition product {A : Type'} : (A -> Prop) -> (A -> R) -> R := @iterate A R Rmult.
Lemma product_def {A : Type'} : (@product A) = (@iterate A R Rmult).
Proof. exact (REFL (@product A)). Qed.
Definition isum {A : Type'} : (A -> Prop) -> (A -> Z) -> Z := @iterate A Z Z.add.
Lemma isum_def {A : Type'} : (@isum A) = (@iterate A Z Z.add).
Proof. exact (REFL (@isum A)). Qed.
Definition nsum {A : Type'} : (A -> Prop) -> (A -> N) -> N := @iterate A N N.add.
Lemma nsum_def {A : Type'} : (@nsum A) = (@iterate A N N.add).
Proof. exact (REFL (@nsum A)). Qed.
Definition sum {A : Type'} : (A -> Prop) -> (A -> R) -> R := @iterate A R Rplus.
Lemma sum_def {A : Type'} : (@sum A) = (@iterate A R Rplus).
Proof. exact (REFL (@sum A)). Qed.
Definition polynomial_function : (R -> R) -> Prop := fun _94114 : R -> R => exists m : N, exists c : N -> R, forall x : R, (_94114 x) = (@sum N (Ninterval (NUMERAL N0) m) (fun i : N => Rmult (c i) (Rpow x i))).
Lemma polynomial_function_def : polynomial_function = (fun _94114 : R -> R => exists m : N, exists c : N -> R, forall x : R, (_94114 x) = (@sum N (Ninterval (NUMERAL N0) m) (fun i : N => Rmult (c i) (Rpow x i)))).
Proof. exact (REFL polynomial_function). Qed.
Definition dollar {A N' : Type'} : (cart A N') -> N -> A := fun _94566 : cart A N' => fun _94567 : N => @dest_cart A N' _94566 (@finite_index N' _94567).
Lemma dollar_def {A N' : Type'} : (@dollar A N') = (fun _94566 : cart A N' => fun _94567 : N => @dest_cart A N' _94566 (@finite_index N' _94567)).
Proof. exact (REFL (@dollar A N')). Qed.
Definition lambda {A B : Type'} : (N -> A) -> cart A B := fun _94602 : N -> A => @ε (cart A B) (fun f : cart A B => forall i : N, ((N.le (NUMERAL (BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94602 i)).
Lemma lambda_def {A B : Type'} : (@lambda A B) = (fun _94602 : N -> A => @ε (cart A B) (fun f : cart A B => forall i : N, ((N.le (NUMERAL (BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94602 i))).
Proof. exact (REFL (@lambda A B)). Qed.
Definition pastecart {A M N' : Type'} : (cart A M) -> (cart A N') -> cart A (finite_sum M N') := fun _94893 : cart A M => fun _94894 : cart A N' => @lambda A (finite_sum M N') (fun i : N => @COND A (N.le i (@dimindex M (@setT M))) (@dollar A M _94893 i) (@dollar A N' _94894 (N.sub i (@dimindex M (@setT M))))).
Lemma pastecart_def {A M N' : Type'} : (@pastecart A M N') = (fun _94893 : cart A M => fun _94894 : cart A N' => @lambda A (finite_sum M N') (fun i : N => @COND A (N.le i (@dimindex M (@setT M))) (@dollar A M _94893 i) (@dollar A N' _94894 (N.sub i (@dimindex M (@setT M)))))).
Proof. exact (REFL (@pastecart A M N')). Qed.
Definition fstcart {A M N' : Type'} : (cart A (finite_sum M N')) -> cart A M := fun _94905 : cart A (finite_sum M N') => @lambda A M (fun i : N => @dollar A (finite_sum M N') _94905 i).
Lemma fstcart_def {A M N' : Type'} : (@fstcart A M N') = (fun _94905 : cart A (finite_sum M N') => @lambda A M (fun i : N => @dollar A (finite_sum M N') _94905 i)).
Proof. exact (REFL (@fstcart A M N')). Qed.
Definition sndcart {A M N' : Type'} : (cart A (finite_sum M N')) -> cart A N' := fun _94910 : cart A (finite_sum M N') => @lambda A N' (fun i : N => @dollar A (finite_sum M N') _94910 (N.add i (@dimindex M (@setT M)))).
Lemma sndcart_def {A M N' : Type'} : (@sndcart A M N') = (fun _94910 : cart A (finite_sum M N') => @lambda A N' (fun i : N => @dollar A (finite_sum M N') _94910 (N.add i (@dimindex M (@setT M))))).
Proof. exact (REFL (@sndcart A M N')). Qed.
Definition _100320 {A : Type'} : (finite_sum A A) -> tybit0 A := fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL N0) a' (fun n : N => @BOTTOM (finite_sum A A))) a).
Lemma _100320_def {A : Type'} : (@_100320 A) = (fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL N0) a' (fun n : N => @BOTTOM (finite_sum A A))) a)).
Proof. exact (REFL (@_100320 A)). Qed.
Definition mktybit0 {A : Type'} : (finite_sum A A) -> tybit0 A := @_100320 A.
Lemma mktybit0_def {A : Type'} : (@mktybit0 A) = (@_100320 A).
Proof. exact (REFL (@mktybit0 A)). Qed.
Definition _100339 {A : Type'} : (finite_sum (finite_sum A A) unit) -> tybit1 A := fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL N0) a' (fun n : N => @BOTTOM (finite_sum (finite_sum A A) unit))) a).
Lemma _100339_def {A : Type'} : (@_100339 A) = (fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL N0) a' (fun n : N => @BOTTOM (finite_sum (finite_sum A A) unit))) a)).
Proof. exact (REFL (@_100339 A)). Qed.
Definition mktybit1 {A : Type'} : (finite_sum (finite_sum A A) unit) -> tybit1 A := @_100339 A.
Lemma mktybit1_def {A : Type'} : (@mktybit1 A) = (@_100339 A).
Proof. exact (REFL (@mktybit1 A)). Qed.
Definition vector {A N' : Type'} : (list A) -> cart A N' := fun _102033 : list A => @lambda A N' (fun i : N => @Nth A (N.sub i (NUMERAL (BIT1 N0))) _102033).
Lemma vector_def {A N' : Type'} : (@vector A N') = (fun _102033 : list A => @lambda A N' (fun i : N => @Nth A (N.sub i (NUMERAL (BIT1 N0))) _102033)).
Proof. exact (REFL (@vector A N')). Qed.
Definition PCROSS {A M N' : Type'} : ((cart A M) -> Prop) -> ((cart A N') -> Prop) -> (cart A (finite_sum M N')) -> Prop := fun _102060 : (cart A M) -> Prop => fun _102061 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x _102060) /\ (@IN (cart A N') y _102061)) (@pastecart A M N' x y)).
Lemma PCROSS_def {A M N' : Type'} : (@PCROSS A M N') = (fun _102060 : (cart A M) -> Prop => fun _102061 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x _102060) /\ (@IN (cart A N') y _102061)) (@pastecart A M N' x y))).
Proof. exact (REFL (@PCROSS A M N')). Qed.
Definition CASEWISE {_137714 _137750 _137754 _137755 : Type'} : (list (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714))) -> _137755 -> _137754 -> _137714 := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714))) -> _137755 -> _137754 -> _137714) (fun CASEWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714))) -> _137755 -> _137754 -> _137714 => forall _102665 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall f : _137755, forall x : _137754, (CASEWISE' _102665 (@nil (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714))) f x) = (@ε _137714 (fun y : _137714 => True))) /\ (forall h : prod (_137750 -> _137754) (_137755 -> _137750 -> _137714), forall t : list (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714)), forall f : _137755, forall x : _137754, (CASEWISE' _102665 (@cons (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714)) h t) f x) = (@COND _137714 (exists y : _137750, (@fst (_137750 -> _137754) (_137755 -> _137750 -> _137714) h y) = x) (@snd (_137750 -> _137754) (_137755 -> _137750 -> _137714) h f (@ε _137750 (fun y : _137750 => (@fst (_137750 -> _137754) (_137755 -> _137750 -> _137714) h y) = x))) (CASEWISE' _102665 t f x)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))))).
Lemma CASEWISE_def {_137714 _137750 _137754 _137755 : Type'} : (@CASEWISE _137714 _137750 _137754 _137755) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714))) -> _137755 -> _137754 -> _137714) (fun CASEWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714))) -> _137755 -> _137754 -> _137714 => forall _102665 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall f : _137755, forall x : _137754, (CASEWISE' _102665 (@nil (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714))) f x) = (@ε _137714 (fun y : _137714 => True))) /\ (forall h : prod (_137750 -> _137754) (_137755 -> _137750 -> _137714), forall t : list (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714)), forall f : _137755, forall x : _137754, (CASEWISE' _102665 (@cons (prod (_137750 -> _137754) (_137755 -> _137750 -> _137714)) h t) f x) = (@COND _137714 (exists y : _137750, (@fst (_137750 -> _137754) (_137755 -> _137750 -> _137714) h y) = x) (@snd (_137750 -> _137754) (_137755 -> _137750 -> _137714) h f (@ε _137750 (fun y : _137750 => (@fst (_137750 -> _137754) (_137755 -> _137750 -> _137714) h y) = x))) (CASEWISE' _102665 t f x)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))))).
Proof. exact (REFL (@CASEWISE _137714 _137750 _137754 _137755)). Qed.
Definition admissible {_138045 _138048 _138052 _138053 _138058 : Type'} : (_138052 -> _138045 -> Prop) -> ((_138052 -> _138048) -> _138058 -> Prop) -> (_138058 -> _138045) -> ((_138052 -> _138048) -> _138058 -> _138053) -> Prop := fun _103732 : _138052 -> _138045 -> Prop => fun _103733 : (_138052 -> _138048) -> _138058 -> Prop => fun _103734 : _138058 -> _138045 => fun _103735 : (_138052 -> _138048) -> _138058 -> _138053 => forall f : _138052 -> _138048, forall g : _138052 -> _138048, forall a : _138058, ((_103733 f a) /\ ((_103733 g a) /\ (forall z : _138052, (_103732 z (_103734 a)) -> (f z) = (g z)))) -> (_103735 f a) = (_103735 g a).
Lemma admissible_def {_138045 _138048 _138052 _138053 _138058 : Type'} : (@admissible _138045 _138048 _138052 _138053 _138058) = (fun _103732 : _138052 -> _138045 -> Prop => fun _103733 : (_138052 -> _138048) -> _138058 -> Prop => fun _103734 : _138058 -> _138045 => fun _103735 : (_138052 -> _138048) -> _138058 -> _138053 => forall f : _138052 -> _138048, forall g : _138052 -> _138048, forall a : _138058, ((_103733 f a) /\ ((_103733 g a) /\ (forall z : _138052, (_103732 z (_103734 a)) -> (f z) = (g z)))) -> (_103735 f a) = (_103735 g a)).
Proof. exact (REFL (@admissible _138045 _138048 _138052 _138053 _138058)). Qed.
Definition tailadmissible {A B P : Type'} : (A -> A -> Prop) -> ((A -> B) -> P -> Prop) -> (P -> A) -> ((A -> B) -> P -> B) -> Prop := fun _103764 : A -> A -> Prop => fun _103765 : (A -> B) -> P -> Prop => fun _103766 : P -> A => fun _103767 : (A -> B) -> P -> B => exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (_103764 y (G f a))) -> _103764 y (_103766 a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (_103764 z (_103766 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (_103765 f a) -> (_103767 f a) = (@COND B (P' f a) (f (G f a)) (H f a)))).
Lemma tailadmissible_def {A B P : Type'} : (@tailadmissible A B P) = (fun _103764 : A -> A -> Prop => fun _103765 : (A -> B) -> P -> Prop => fun _103766 : P -> A => fun _103767 : (A -> B) -> P -> B => exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (_103764 y (G f a))) -> _103764 y (_103766 a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (_103764 z (_103766 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (_103765 f a) -> (_103767 f a) = (@COND B (P' f a) (f (G f a)) (H f a))))).
Proof. exact (REFL (@tailadmissible A B P)). Qed.
Definition superadmissible {_138202 _138204 _138210 : Type'} : (_138202 -> _138202 -> Prop) -> ((_138202 -> _138204) -> _138210 -> Prop) -> (_138210 -> _138202) -> ((_138202 -> _138204) -> _138210 -> _138204) -> Prop := fun _103796 : _138202 -> _138202 -> Prop => fun _103797 : (_138202 -> _138204) -> _138210 -> Prop => fun _103798 : _138210 -> _138202 => fun _103799 : (_138202 -> _138204) -> _138210 -> _138204 => (@admissible _138202 _138204 _138202 Prop _138210 _103796 (fun f : _138202 -> _138204 => fun a : _138210 => True) _103798 _103797) -> @tailadmissible _138202 _138204 _138210 _103796 _103797 _103798 _103799.
Lemma superadmissible_def {_138202 _138204 _138210 : Type'} : (@superadmissible _138202 _138204 _138210) = (fun _103796 : _138202 -> _138202 -> Prop => fun _103797 : (_138202 -> _138204) -> _138210 -> Prop => fun _103798 : _138210 -> _138202 => fun _103799 : (_138202 -> _138204) -> _138210 -> _138204 => (@admissible _138202 _138204 _138202 Prop _138210 _103796 (fun f : _138202 -> _138204 => fun a : _138210 => True) _103798 _103797) -> @tailadmissible _138202 _138204 _138210 _103796 _103797 _103798 _103799).
Proof. exact (REFL (@superadmissible _138202 _138204 _138210)). Qed.
Definition psum : (prod N N) -> (N -> R) -> R := @ε ((prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R) (fun sum' : (prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R => forall _114458 : prod N (prod N (prod N N)), (forall f : N -> R, forall n : N, (sum' _114458 (@pair N N n (NUMERAL N0)) f) = (R_of_N (NUMERAL N0))) /\ (forall f : N -> R, forall m : N, forall n : N, (sum' _114458 (@pair N N n (N.succ m)) f) = (Rplus (sum' _114458 (@pair N N n m) f) (f (N.add n m))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))).
Lemma psum_def : psum = (@ε ((prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R) (fun sum' : (prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R => forall _114458 : prod N (prod N (prod N N)), (forall f : N -> R, forall n : N, (sum' _114458 (@pair N N n (NUMERAL N0)) f) = (R_of_N (NUMERAL N0))) /\ (forall f : N -> R, forall m : N, forall n : N, (sum' _114458 (@pair N N n (N.succ m)) f) = (Rplus (sum' _114458 (@pair N N n m) f) (f (N.add n m))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))).
Proof. exact (REFL psum). Qed.
Definition re_Union {A : Type'} : ((A -> Prop) -> Prop) -> A -> Prop := fun _114505 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114505 s) /\ (s x).
Lemma re_Union_def {A : Type'} : (@re_Union A) = (fun _114505 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114505 s) /\ (s x)).
Proof. exact (REFL (@re_Union A)). Qed.
Definition re_union {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114510 : A -> Prop => fun _114511 : A -> Prop => fun x : A => (_114510 x) \/ (_114511 x).
Lemma re_union_def {A : Type'} : (@re_union A) = (fun _114510 : A -> Prop => fun _114511 : A -> Prop => fun x : A => (_114510 x) \/ (_114511 x)).
Proof. exact (REFL (@re_union A)). Qed.
Definition re_intersect {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114522 : A -> Prop => fun _114523 : A -> Prop => fun x : A => (_114522 x) /\ (_114523 x).
Lemma re_intersect_def {A : Type'} : (@re_intersect A) = (fun _114522 : A -> Prop => fun _114523 : A -> Prop => fun x : A => (_114522 x) /\ (_114523 x)).
Proof. exact (REFL (@re_intersect A)). Qed.
Definition re_null {A : Type'} : A -> Prop := fun x : A => False.
Lemma re_null_def {A : Type'} : (@re_null A) = (fun x : A => False).
Proof. exact (REFL (@re_null A)). Qed.
Definition re_universe {A : Type'} : A -> Prop := fun x : A => True.
Lemma re_universe_def {A : Type'} : (@re_universe A) = (fun x : A => True).
Proof. exact (REFL (@re_universe A)). Qed.
Definition re_subset {A : Type'} : (A -> Prop) -> (A -> Prop) -> Prop := fun _114534 : A -> Prop => fun _114535 : A -> Prop => forall x : A, (_114534 x) -> _114535 x.
Lemma re_subset_def {A : Type'} : (@re_subset A) = (fun _114534 : A -> Prop => fun _114535 : A -> Prop => forall x : A, (_114534 x) -> _114535 x).
Proof. exact (REFL (@re_subset A)). Qed.
Definition re_compl {A : Type'} : (A -> Prop) -> A -> Prop := fun _114546 : A -> Prop => fun x : A => ~ (_114546 x).
Lemma re_compl_def {A : Type'} : (@re_compl A) = (fun _114546 : A -> Prop => fun x : A => ~ (_114546 x)).
Proof. exact (REFL (@re_compl A)). Qed.
Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _114555 : (A -> Prop) -> Prop => (_114555 (@re_null A)) /\ ((_114555 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114555 a) /\ (_114555 b)) -> _114555 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114555) -> _114555 (@re_Union A P)))).
Lemma istopology_def {A : Type'} : (@istopology A) = (fun _114555 : (A -> Prop) -> Prop => (_114555 (@re_null A)) /\ ((_114555 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114555 a) /\ (_114555 b)) -> _114555 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114555) -> _114555 (@re_Union A P))))).
Proof. exact (REFL (@istopology A)). Qed.
Definition neigh {A : Type'} : (Topology A) -> (prod (A -> Prop) A) -> Prop := fun _114568 : Topology A => fun _114569 : prod (A -> Prop) A => exists P : A -> Prop, (@open A _114568 P) /\ ((@re_subset A P (@fst (A -> Prop) A _114569)) /\ (P (@snd (A -> Prop) A _114569))).
Lemma neigh_def {A : Type'} : (@neigh A) = (fun _114568 : Topology A => fun _114569 : prod (A -> Prop) A => exists P : A -> Prop, (@open A _114568 P) /\ ((@re_subset A P (@fst (A -> Prop) A _114569)) /\ (P (@snd (A -> Prop) A _114569)))).
Proof. exact (REFL (@neigh A)). Qed.
Definition closed {A : Type'} : (Topology A) -> (A -> Prop) -> Prop := fun _114589 : Topology A => fun _114590 : A -> Prop => @open A _114589 (@re_compl A _114590).
Lemma closed_def {A : Type'} : (@closed A) = (fun _114589 : Topology A => fun _114590 : A -> Prop => @open A _114589 (@re_compl A _114590)).
Proof. exact (REFL (@closed A)). Qed.
Definition limpt {A : Type'} : (Topology A) -> A -> (A -> Prop) -> Prop := fun _114601 : Topology A => fun _114602 : A => fun _114603 : A -> Prop => forall N' : A -> Prop, (@neigh A _114601 (@pair (A -> Prop) A N' _114602)) -> exists y : A, (~ (_114602 = y)) /\ ((_114603 y) /\ (N' y)).
Lemma limpt_def {A : Type'} : (@limpt A) = (fun _114601 : Topology A => fun _114602 : A => fun _114603 : A -> Prop => forall N' : A -> Prop, (@neigh A _114601 (@pair (A -> Prop) A N' _114602)) -> exists y : A, (~ (_114602 = y)) /\ ((_114603 y) /\ (N' y))).
Proof. exact (REFL (@limpt A)). Qed.
Definition mtop {A : Type'} : (Metric A) -> Topology A := fun _114749 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N (NUMERAL N0)) e) /\ (forall y : A, (Rlt (@mdist A _114749 (@pair A A x y)) e) -> S' y)).
Lemma mtop_def {A : Type'} : (@mtop A) = (fun _114749 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N (NUMERAL N0)) e) /\ (forall y : A, (Rlt (@mdist A _114749 (@pair A A x y)) e) -> S' y))).
Proof. exact (REFL (@mtop A)). Qed.
Definition ball {A : Type'} : (Metric A) -> (prod A R) -> A -> Prop := fun _114760 : Metric A => fun _114761 : prod A R => fun y : A => Rlt (@mdist A _114760 (@pair A A (@fst A R _114761) y)) (@snd A R _114761).
Lemma ball_def {A : Type'} : (@ball A) = (fun _114760 : Metric A => fun _114761 : prod A R => fun y : A => Rlt (@mdist A _114760 (@pair A A (@fst A R _114761) y)) (@snd A R _114761)).
Proof. exact (REFL (@ball A)). Qed.
Definition mr1 : Metric R := @metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (Rabs (Rminus y x)))).
Lemma mr1_def : mr1 = (@metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (Rabs (Rminus y x))))).
Proof. exact (REFL mr1). Qed.
Definition dorder {A : Type'} : (A -> A -> Prop) -> Prop := fun _114842 : A -> A -> Prop => forall x : A, forall y : A, ((_114842 x x) /\ (_114842 y y)) -> exists z : A, (_114842 z z) /\ (forall w : A, (_114842 w z) -> (_114842 w x) /\ (_114842 w y)).
Lemma dorder_def {A : Type'} : (@dorder A) = (fun _114842 : A -> A -> Prop => forall x : A, forall y : A, ((_114842 x x) /\ (_114842 y y)) -> exists z : A, (_114842 z z) /\ (forall w : A, (_114842 w z) -> (_114842 w x) /\ (_114842 w y))).
Proof. exact (REFL (@dorder A)). Qed.
Definition tends {A B : Type'} : (B -> A) -> A -> (prod (Topology A) (B -> B -> Prop)) -> Prop := fun _114847 : B -> A => fun _114848 : A => fun _114849 : prod (Topology A) (B -> B -> Prop) => forall N' : A -> Prop, (@neigh A (@fst (Topology A) (B -> B -> Prop) _114849) (@pair (A -> Prop) A N' _114848)) -> exists n : B, (@snd (Topology A) (B -> B -> Prop) _114849 n n) /\ (forall m : B, (@snd (Topology A) (B -> B -> Prop) _114849 m n) -> N' (_114847 m)).
Lemma tends_def {A B : Type'} : (@tends A B) = (fun _114847 : B -> A => fun _114848 : A => fun _114849 : prod (Topology A) (B -> B -> Prop) => forall N' : A -> Prop, (@neigh A (@fst (Topology A) (B -> B -> Prop) _114849) (@pair (A -> Prop) A N' _114848)) -> exists n : B, (@snd (Topology A) (B -> B -> Prop) _114849 n n) /\ (forall m : B, (@snd (Topology A) (B -> B -> Prop) _114849 m n) -> N' (_114847 m))).
Proof. exact (REFL (@tends A B)). Qed.
Definition bounded {A B : Type'} : (prod (Metric A) (B -> B -> Prop)) -> (B -> A) -> Prop := fun _114874 : prod (Metric A) (B -> B -> Prop) => fun _114875 : B -> A => exists k : R, exists x : A, exists N' : B, (@snd (Metric A) (B -> B -> Prop) _114874 N' N') /\ (forall n : B, (@snd (Metric A) (B -> B -> Prop) _114874 n N') -> Rlt (@mdist A (@fst (Metric A) (B -> B -> Prop) _114874) (@pair A A (_114875 n) x)) k).
Lemma bounded_def {A B : Type'} : (@bounded A B) = (fun _114874 : prod (Metric A) (B -> B -> Prop) => fun _114875 : B -> A => exists k : R, exists x : A, exists N' : B, (@snd (Metric A) (B -> B -> Prop) _114874 N' N') /\ (forall n : B, (@snd (Metric A) (B -> B -> Prop) _114874 n N') -> Rlt (@mdist A (@fst (Metric A) (B -> B -> Prop) _114874) (@pair A A (_114875 n) x)) k)).
Proof. exact (REFL (@bounded A B)). Qed.
Definition tendsto {A : Type'} : (prod (Metric A) A) -> A -> A -> Prop := fun _114891 : prod (Metric A) A => fun _114892 : A => fun _114893 : A => (Rlt (R_of_N (NUMERAL N0)) (@mdist A (@fst (Metric A) A _114891) (@pair A A (@snd (Metric A) A _114891) _114892))) /\ (Rle (@mdist A (@fst (Metric A) A _114891) (@pair A A (@snd (Metric A) A _114891) _114892)) (@mdist A (@fst (Metric A) A _114891) (@pair A A (@snd (Metric A) A _114891) _114893))).
Lemma tendsto_def {A : Type'} : (@tendsto A) = (fun _114891 : prod (Metric A) A => fun _114892 : A => fun _114893 : A => (Rlt (R_of_N (NUMERAL N0)) (@mdist A (@fst (Metric A) A _114891) (@pair A A (@snd (Metric A) A _114891) _114892))) /\ (Rle (@mdist A (@fst (Metric A) A _114891) (@pair A A (@snd (Metric A) A _114891) _114892)) (@mdist A (@fst (Metric A) A _114891) (@pair A A (@snd (Metric A) A _114891) _114893)))).
Proof. exact (REFL (@tendsto A)). Qed.
Definition tends_num_real : (N -> R) -> R -> Prop := fun _114982 : N -> R => fun _114983 : R => @tends R N _114982 _114983 (@pair (Topology R) (N -> N -> Prop) (@mtop R mr1) N.ge).
Lemma tends_num_real_def : tends_num_real = (fun _114982 : N -> R => fun _114983 : R => @tends R N _114982 _114983 (@pair (Topology R) (N -> N -> Prop) (@mtop R mr1) N.ge)).
Proof. exact (REFL tends_num_real). Qed.
Definition convergent : (N -> R) -> Prop := fun _115038 : N -> R => exists l : R, tends_num_real _115038 l.
Lemma convergent_def : convergent = (fun _115038 : N -> R => exists l : R, tends_num_real _115038 l).
Proof. exact (REFL convergent). Qed.
Definition cauchy : (N -> R) -> Prop := fun _115043 : N -> R => forall e : R, (Rlt (R_of_N (NUMERAL N0)) e) -> exists N' : N, forall m : N, forall n : N, ((N.ge m N') /\ (N.ge n N')) -> Rlt (Rabs (Rminus (_115043 m) (_115043 n))) e.
Lemma cauchy_def : cauchy = (fun _115043 : N -> R => forall e : R, (Rlt (R_of_N (NUMERAL N0)) e) -> exists N' : N, forall m : N, forall n : N, ((N.ge m N') /\ (N.ge n N')) -> Rlt (Rabs (Rminus (_115043 m) (_115043 n))) e).
Proof. exact (REFL cauchy). Qed.
Definition lim : (N -> R) -> R := fun _115048 : N -> R => @ε R (fun l : R => tends_num_real _115048 l).
Lemma lim_def : lim = (fun _115048 : N -> R => @ε R (fun l : R => tends_num_real _115048 l)).
Proof. exact (REFL lim). Qed.
Definition subseq : (N -> N) -> Prop := fun _115053 : N -> N => forall m : N, forall n : N, (N.lt m n) -> N.lt (_115053 m) (_115053 n).
Lemma subseq_def : subseq = (fun _115053 : N -> N => forall m : N, forall n : N, (N.lt m n) -> N.lt (_115053 m) (_115053 n)).
Proof. exact (REFL subseq). Qed.
Definition mono : (N -> R) -> Prop := fun _115060 : N -> R => (forall m : N, forall n : N, (N.le m n) -> Rle (_115060 m) (_115060 n)) \/ (forall m : N, forall n : N, (N.le m n) -> Rge (_115060 m) (_115060 n)).
Lemma mono_def : mono = (fun _115060 : N -> R => (forall m : N, forall n : N, (N.le m n) -> Rle (_115060 m) (_115060 n)) \/ (forall m : N, forall n : N, (N.le m n) -> Rge (_115060 m) (_115060 n))).
Proof. exact (REFL mono). Qed.
Definition sums : (N -> R) -> R -> Prop := fun _115340 : N -> R => fun _115341 : R => tends_num_real (fun n : N => psum (@pair N N (NUMERAL N0) n) _115340) _115341.
Lemma sums_def : sums = (fun _115340 : N -> R => fun _115341 : R => tends_num_real (fun n : N => psum (@pair N N (NUMERAL N0) n) _115340) _115341).
Proof. exact (REFL sums). Qed.
Definition summable : (N -> R) -> Prop := fun _115352 : N -> R => exists s : R, sums _115352 s.
Lemma summable_def : summable = (fun _115352 : N -> R => exists s : R, sums _115352 s).
Proof. exact (REFL summable). Qed.
Definition suminf : (N -> R) -> R := fun _115357 : N -> R => @ε R (fun s : R => sums _115357 s).
Lemma suminf_def : suminf = (fun _115357 : N -> R => @ε R (fun s : R => sums _115357 s)).
Proof. exact (REFL suminf). Qed.
Definition tends_real_real : (R -> R) -> R -> R -> Prop := fun _115425 : R -> R => fun _115426 : R => fun _115427 : R => @tends R R _115425 _115426 (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 _115427))).
Lemma tends_real_real_def : tends_real_real = (fun _115425 : R -> R => fun _115426 : R => fun _115427 : R => @tends R R _115425 _115426 (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 _115427)))).
Proof. exact (REFL tends_real_real). Qed.
Definition diffl : (R -> R) -> R -> R -> Prop := fun _115455 : R -> R => fun _115456 : R => fun _115457 : R => tends_real_real (fun h : R => Rdiv (Rminus (_115455 (Rplus _115457 h)) (_115455 _115457)) h) _115456 (R_of_N (NUMERAL N0)).
Lemma diffl_def : diffl = (fun _115455 : R -> R => fun _115456 : R => fun _115457 : R => tends_real_real (fun h : R => Rdiv (Rminus (_115455 (Rplus _115457 h)) (_115455 _115457)) h) _115456 (R_of_N (NUMERAL N0))).
Proof. exact (REFL diffl). Qed.
Definition contl : (R -> R) -> R -> Prop := fun _115476 : R -> R => fun _115477 : R => tends_real_real (fun h : R => _115476 (Rplus _115477 h)) (_115476 _115477) (R_of_N (NUMERAL N0)).
Lemma contl_def : contl = (fun _115476 : R -> R => fun _115477 : R => tends_real_real (fun h : R => _115476 (Rplus _115477 h)) (_115476 _115477) (R_of_N (NUMERAL N0))).
Proof. exact (REFL contl). Qed.
Definition differentiable : (R -> R) -> R -> Prop := fun _115488 : R -> R => fun _115489 : R => exists l : R, diffl _115488 l _115489.
Lemma differentiable_def : differentiable = (fun _115488 : R -> R => fun _115489 : R => exists l : R, diffl _115488 l _115489).
Proof. exact (REFL differentiable). Qed.
Definition fld {A : Type'} : (A -> A -> Prop) -> A -> Prop := fun _117619 : A -> A -> Prop => @GSPEC A (fun GEN_PVAR_377 : A => exists x : A, @SETSPEC A GEN_PVAR_377 (exists y : A, (_117619 x y) \/ (_117619 y x)) x).
Lemma fld_def {A : Type'} : (@fld A) = (fun _117619 : A -> A -> Prop => @GSPEC A (fun GEN_PVAR_377 : A => exists x : A, @SETSPEC A GEN_PVAR_377 (exists y : A, (_117619 x y) \/ (_117619 y x)) x)).
Proof. exact (REFL (@fld A)). Qed.
Definition qoset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117674 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117674)) -> _117674 x x) /\ (forall x : A, forall y : A, forall z : A, ((_117674 x y) /\ (_117674 y z)) -> _117674 x z).
Lemma qoset_def {A : Type'} : (@qoset A) = (fun _117674 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117674)) -> _117674 x x) /\ (forall x : A, forall y : A, forall z : A, ((_117674 x y) /\ (_117674 y z)) -> _117674 x z)).
Proof. exact (REFL (@qoset A)). Qed.
Definition poset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117679 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117679)) -> _117679 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117679 x y) /\ (_117679 y z)) -> _117679 x z) /\ (forall x : A, forall y : A, ((_117679 x y) /\ (_117679 y x)) -> x = y)).
Lemma poset_def {A : Type'} : (@poset A) = (fun _117679 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117679)) -> _117679 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117679 x y) /\ (_117679 y z)) -> _117679 x z) /\ (forall x : A, forall y : A, ((_117679 x y) /\ (_117679 y x)) -> x = y))).
Proof. exact (REFL (@poset A)). Qed.
Definition toset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117684 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117684)) -> _117684 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117684 x y) /\ (_117684 y z)) -> _117684 x z) /\ ((forall x : A, forall y : A, ((_117684 x y) /\ (_117684 y x)) -> x = y) /\ (forall x : A, forall y : A, ((@IN A x (@fld A _117684)) /\ (@IN A y (@fld A _117684))) -> (_117684 x y) \/ (_117684 y x)))).
Lemma toset_def {A : Type'} : (@toset A) = (fun _117684 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117684)) -> _117684 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117684 x y) /\ (_117684 y z)) -> _117684 x z) /\ ((forall x : A, forall y : A, ((_117684 x y) /\ (_117684 y x)) -> x = y) /\ (forall x : A, forall y : A, ((@IN A x (@fld A _117684)) /\ (@IN A y (@fld A _117684))) -> (_117684 x y) \/ (_117684 y x))))).
Proof. exact (REFL (@toset A)). Qed.
Definition woset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117689 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117689)) -> _117689 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117689 x y) /\ (_117689 y z)) -> _117689 x z) /\ ((forall x : A, forall y : A, ((_117689 x y) /\ (_117689 y x)) -> x = y) /\ ((forall x : A, forall y : A, ((@IN A x (@fld A _117689)) /\ (@IN A y (@fld A _117689))) -> (_117689 x y) \/ (_117689 y x)) /\ (forall s : A -> Prop, ((@subset A s (@fld A _117689)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> _117689 x y))))).
Lemma woset_def {A : Type'} : (@woset A) = (fun _117689 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117689)) -> _117689 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117689 x y) /\ (_117689 y z)) -> _117689 x z) /\ ((forall x : A, forall y : A, ((_117689 x y) /\ (_117689 y x)) -> x = y) /\ ((forall x : A, forall y : A, ((@IN A x (@fld A _117689)) /\ (@IN A y (@fld A _117689))) -> (_117689 x y) \/ (_117689 y x)) /\ (forall s : A -> Prop, ((@subset A s (@fld A _117689)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> _117689 x y)))))).
Proof. exact (REFL (@woset A)). Qed.
Definition wqoset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117694 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117694)) -> _117694 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117694 x y) /\ (_117694 y z)) -> _117694 x z) /\ (forall s : A -> Prop, (@subset A s (@fld A _117694)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (_117694 x y))))).
Lemma wqoset_def {A : Type'} : (@wqoset A) = (fun _117694 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117694)) -> _117694 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117694 x y) /\ (_117694 y z)) -> _117694 x z) /\ (forall s : A -> Prop, (@subset A s (@fld A _117694)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (_117694 x y)))))).
Proof. exact (REFL (@wqoset A)). Qed.
Definition chain {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _117699 : A -> A -> Prop => fun _117700 : A -> Prop => forall x : A, forall y : A, ((@IN A x _117700) /\ (@IN A y _117700)) -> (_117699 x y) \/ (_117699 y x).
Lemma chain_def {A : Type'} : (@chain A) = (fun _117699 : A -> A -> Prop => fun _117700 : A -> Prop => forall x : A, forall y : A, ((@IN A x _117700) /\ (@IN A y _117700)) -> (_117699 x y) \/ (_117699 y x)).
Proof. exact (REFL (@chain A)). Qed.
Definition antichain {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _117711 : A -> A -> Prop => fun _117712 : A -> Prop => (@subset A _117712 (@fld A _117711)) /\ (@pairwise A (fun x : A => fun y : A => ~ (_117711 x y)) _117712).
Lemma antichain_def {A : Type'} : (@antichain A) = (fun _117711 : A -> A -> Prop => fun _117712 : A -> Prop => (@subset A _117712 (@fld A _117711)) /\ (@pairwise A (fun x : A => fun y : A => ~ (_117711 x y)) _117712)).
Proof. exact (REFL (@antichain A)). Qed.
Definition strictly {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _118364 : A -> A -> Prop => fun x : A => fun y : A => (_118364 x y) /\ (~ (_118364 y x)).
Lemma strictly_def {A : Type'} : (@strictly A) = (fun _118364 : A -> A -> Prop => fun x : A => fun y : A => (_118364 x y) /\ (~ (_118364 y x))).
Proof. exact (REFL (@strictly A)). Qed.
Definition properly {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _118369 : A -> A -> Prop => fun x : A => fun y : A => (_118369 x y) /\ (~ (x = y)).
Lemma properly_def {A : Type'} : (@properly A) = (fun _118369 : A -> A -> Prop => fun x : A => fun y : A => (_118369 x y) /\ (~ (x = y))).
Proof. exact (REFL (@properly A)). Qed.
Definition inseg {A : Type'} : (A -> A -> Prop) -> (A -> A -> Prop) -> Prop := fun _122630 : A -> A -> Prop => fun _122631 : A -> A -> Prop => forall x : A, forall y : A, (_122630 x y) = ((_122631 x y) /\ (@fld A _122630 y)).
Lemma inseg_def {A : Type'} : (@inseg A) = (fun _122630 : A -> A -> Prop => fun _122631 : A -> A -> Prop => forall x : A, forall y : A, (_122630 x y) = ((_122631 x y) /\ (@fld A _122630 y))).
Proof. exact (REFL (@inseg A)). Qed.
Definition linseg {A : Type'} : (A -> A -> Prop) -> A -> A -> A -> Prop := fun _122702 : A -> A -> Prop => fun _122703 : A => fun x : A => fun y : A => (_122702 x y) /\ (@properly A _122702 y _122703).
Lemma linseg_def {A : Type'} : (@linseg A) = (fun _122702 : A -> A -> Prop => fun _122703 : A => fun x : A => fun y : A => (_122702 x y) /\ (@properly A _122702 y _122703)).
Proof. exact (REFL (@linseg A)). Qed.
Definition ordinal {A : Type'} : (A -> A -> Prop) -> Prop := fun _122714 : A -> A -> Prop => (@woset A _122714) /\ (forall x : A, (@fld A _122714 x) -> x = (@ε A (fun y : A => ~ (@properly A _122714 y x)))).
Lemma ordinal_def {A : Type'} : (@ordinal A) = (fun _122714 : A -> A -> Prop => (@woset A _122714) /\ (forall x : A, (@fld A _122714 x) -> x = (@ε A (fun y : A => ~ (@properly A _122714 y x))))).
Proof. exact (REFL (@ordinal A)). Qed.
Definition RC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall RC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (a1' = a0')) -> RC' a0' a1') -> RC' a0 a1.
Lemma RC_def {A : Type'} : (@RC A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall RC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (a1' = a0')) -> RC' a0' a1') -> RC' a0 a1).
Proof. exact (REFL (@RC A)). Qed.
Definition SC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall SC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (SC' a1' a0')) -> SC' a0' a1') -> SC' a0 a1.
Lemma SC_def {A : Type'} : (@SC A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall SC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (SC' a1' a0')) -> SC' a0' a1') -> SC' a0 a1).
Proof. exact (REFL (@SC A)). Qed.
Definition RSC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _198680 : A -> A -> Prop => @RC A (@SC A _198680).
Lemma RSC_def {A : Type'} : (@RSC A) = (fun _198680 : A -> A -> Prop => @RC A (@SC A _198680)).
Proof. exact (REFL (@RSC A)). Qed.
Definition RTC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _198804 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A _198804).
Lemma RTC_def {A : Type'} : (@RTC A) = (fun _198804 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A _198804)).
Proof. exact (REFL (@RTC A)). Qed.
Definition STC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _200315 : A -> A -> Prop => @Relation_Operators.clos_trans A (@SC A _200315).
Lemma STC_def {A : Type'} : (@STC A) = (fun _200315 : A -> A -> Prop => @Relation_Operators.clos_trans A (@SC A _200315)).
Proof. exact (REFL (@STC A)). Qed.
Definition RSTC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _200607 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A (@SC A _200607)).
Lemma RSTC_def {A : Type'} : (@RSTC A) = (fun _200607 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A (@SC A _200607))).
Proof. exact (REFL (@RSTC A)). Qed.
Definition INV {A B : Type'} : (B -> A -> Prop) -> A -> B -> Prop := fun _201552 : B -> A -> Prop => fun _201553 : A => fun _201554 : B => _201552 _201554 _201553.
Lemma INV_def {A B : Type'} : (@INV A B) = (fun _201552 : B -> A -> Prop => fun _201553 : A => fun _201554 : B => _201552 _201554 _201553).
Proof. exact (REFL (@INV A B)). Qed.
Definition RELPOW {A : Type'} : N -> (A -> A -> Prop) -> A -> A -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop) (fun RELPOW' : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop => forall _201628 : prod N (prod N (prod N (prod N (prod N N)))), (forall R' : A -> A -> Prop, forall x : A, forall y : A, (RELPOW' _201628 (NUMERAL N0) R' x y) = (x = y)) /\ (forall n : N, forall x : A, forall R' : A -> A -> Prop, forall y : A, (RELPOW' _201628 (N.succ n) R' x y) = (exists z : A, (RELPOW' _201628 n R' x z) /\ (R' z y)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))))).
Lemma RELPOW_def {A : Type'} : (@RELPOW A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop) (fun RELPOW' : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop => forall _201628 : prod N (prod N (prod N (prod N (prod N N)))), (forall R' : A -> A -> Prop, forall x : A, forall y : A, (RELPOW' _201628 (NUMERAL N0) R' x y) = (x = y)) /\ (forall n : N, forall x : A, forall R' : A -> A -> Prop, forall y : A, (RELPOW' _201628 (N.succ n) R' x y) = (exists z : A, (RELPOW' _201628 n R' x z) /\ (R' z y)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))).
Proof. exact (REFL (@RELPOW A)). Qed.
Definition NORMAL {A : Type'} : (A -> A -> Prop) -> A -> Prop := fun _202286 : A -> A -> Prop => fun _202287 : A => ~ (exists y : A, _202286 _202287 y).
Lemma NORMAL_def {A : Type'} : (@NORMAL A) = (fun _202286 : A -> A -> Prop => fun _202287 : A => ~ (exists y : A, _202286 _202287 y)).
Proof. exact (REFL (@NORMAL A)). Qed.
Definition CR {A : Type'} : (A -> A -> Prop) -> Prop := fun _202298 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202298 x y1) /\ (_202298 x y2)) -> exists z : A, (_202298 y1 z) /\ (_202298 y2 z).
Lemma CR_def {A : Type'} : (@CR A) = (fun _202298 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202298 x y1) /\ (_202298 x y2)) -> exists z : A, (_202298 y1 z) /\ (_202298 y2 z)).
Proof. exact (REFL (@CR A)). Qed.
Definition WCR {A : Type'} : (A -> A -> Prop) -> Prop := fun _202303 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202303 x y1) /\ (_202303 x y2)) -> exists z : A, (@RTC A _202303 y1 z) /\ (@RTC A _202303 y2 z).
Lemma WCR_def {A : Type'} : (@WCR A) = (fun _202303 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202303 x y1) /\ (_202303 x y2)) -> exists z : A, (@RTC A _202303 y1 z) /\ (@RTC A _202303 y2 z)).
Proof. exact (REFL (@WCR A)). Qed.
Definition WN {A : Type'} : (A -> A -> Prop) -> Prop := fun _202308 : A -> A -> Prop => forall x : A, exists y : A, (@RTC A _202308 x y) /\ (@NORMAL A _202308 y).
Lemma WN_def {A : Type'} : (@WN A) = (fun _202308 : A -> A -> Prop => forall x : A, exists y : A, (@RTC A _202308 x y) /\ (@NORMAL A _202308 y)).
Proof. exact (REFL (@WN A)). Qed.
Definition SN {A : Type'} : (A -> A -> Prop) -> Prop := fun _202313 : A -> A -> Prop => ~ (exists seq : N -> A, forall n : N, _202313 (seq n) (seq (N.succ n))).
Lemma SN_def {A : Type'} : (@SN A) = (fun _202313 : A -> A -> Prop => ~ (exists seq : N -> A, forall n : N, _202313 (seq n) (seq (N.succ n)))).
Proof. exact (REFL (@SN A)). Qed.
Definition TREE {A : Type'} : (A -> A -> Prop) -> Prop := fun _202318 : A -> A -> Prop => (forall y : A, ~ (@Relation_Operators.clos_trans A _202318 y y)) /\ (exists a : A, (@IN A a (@fld A _202318)) /\ (forall y : A, (@IN A y (@fld A _202318)) -> (y = a) \/ ((@Relation_Operators.clos_trans A _202318 a y) /\ (@ex1 A (fun x : A => _202318 x y))))).
Lemma TREE_def {A : Type'} : (@TREE A) = (fun _202318 : A -> A -> Prop => (forall y : A, ~ (@Relation_Operators.clos_trans A _202318 y y)) /\ (exists a : A, (@IN A a (@fld A _202318)) /\ (forall y : A, (@IN A y (@fld A _202318)) -> (y = a) \/ ((@Relation_Operators.clos_trans A _202318 a y) /\ (@ex1 A (fun x : A => _202318 x y)))))).
Proof. exact (REFL (@TREE A)). Qed.
Definition LF {A : Type'} : (A -> A -> Prop) -> Prop := fun _202323 : A -> A -> Prop => forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_407 : A => exists y : A, @SETSPEC A GEN_PVAR_407 (_202323 x y) y)).
Lemma LF_def {A : Type'} : (@LF A) = (fun _202323 : A -> A -> Prop => forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_407 : A => exists y : A, @SETSPEC A GEN_PVAR_407 (_202323 x y) y))).
Proof. exact (REFL (@LF A)). Qed.
Definition JOINABLE {_183261 : Type'} : (_183261 -> _183261 -> Prop) -> _183261 -> _183261 -> Prop := fun _203860 : _183261 -> _183261 -> Prop => fun _203861 : _183261 => fun _203862 : _183261 => exists u : _183261, (@RTC _183261 _203860 _203861 u) /\ (@RTC _183261 _203860 _203862 u).
Lemma JOINABLE_def {_183261 : Type'} : (@JOINABLE _183261) = (fun _203860 : _183261 -> _183261 -> Prop => fun _203861 : _183261 => fun _203862 : _183261 => exists u : _183261, (@RTC _183261 _203860 _203861 u) /\ (@RTC _183261 _203860 _203862 u)).
Proof. exact (REFL (@JOINABLE _183261)). Qed.
Definition DOWNFROM : N -> list N := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N) (fun DOWNFROM' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N => forall _232647 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), ((DOWNFROM' _232647 (NUMERAL N0)) = (@nil N)) /\ (forall n : N, (DOWNFROM' _232647 (N.succ n)) = (@cons N n (DOWNFROM' _232647 n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))))))).
Lemma DOWNFROM_def : DOWNFROM = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N) (fun DOWNFROM' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N => forall _232647 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), ((DOWNFROM' _232647 (NUMERAL N0)) = (@nil N)) /\ (forall n : N, (DOWNFROM' _232647 (N.succ n)) = (@cons N n (DOWNFROM' _232647 n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))))).
Proof. exact (REFL DOWNFROM). Qed.
Definition loopcheck : (list (prod N term)) -> N -> term -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (list (prod N term)) -> N -> term -> Prop) (fun loopcheck' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (list (prod N term)) -> N -> term -> Prop => forall _260232 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall env : list (prod N term), forall x : N, (LOOPFREE env) -> forall t : term, (loopcheck' _260232 env x t) = (exists y : N, (@IN N y (free_variables_term t)) /\ ((y = x) \/ (exists s : term, (@List.In (prod N term) (@pair N term y s) env) /\ (loopcheck' _260232 env x s))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))).
Lemma loopcheck_def : loopcheck = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (list (prod N term)) -> N -> term -> Prop) (fun loopcheck' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (list (prod N term)) -> N -> term -> Prop => forall _260232 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall env : list (prod N term), forall x : N, (LOOPFREE env) -> forall t : term, (loopcheck' _260232 env x t) = (exists y : N, (@IN N y (free_variables_term t)) /\ ((y = x) \/ (exists s : term, (@List.In (prod N term) (@pair N term y s) env) /\ (loopcheck' _260232 env x s))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))).
Proof. exact (REFL loopcheck). Qed.
