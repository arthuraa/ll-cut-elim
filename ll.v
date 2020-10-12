Require Import Coq.Unicode.Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import fintype bigop ssrAC.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

Declare Scope mset_scope.
Delimit Scope mset_scope with mset.
Local Open Scope mset_scope.

Section MSet.

Variable T : ordType.

Definition mset_of of phant T := ffun (fun x : T => 0).
Notation "{ 'mset' T }" :=
  (mset_of (Phant T))
  (at level 0, format "{ 'mset'  T }") : form_scope.

Implicit Types (m : {mset T}) (x : T).

Definition msetU m1 m2 : {mset T} :=
  mkffun (fun x => m1 x + m2 x) (supp m1 :|: supp m2)%fset.
Notation "m1 ∪ m2" := (msetU m1 m2)
  (at level 25, left associativity) : mset_scope.

Lemma msetUE m1 m2 x : msetU m1 m2 x = m1 x + m2 x.
Proof.
rewrite !mkffunE in_fsetU !mem_supp.
by case: eqP=> // ->; case: eqP=> //= ->.
Qed.

Lemma supp_msetU m1 m2 : supp (msetU m1 m2) = supp m1 :|: supp m2.
Proof.
apply/eq_fset=> x.
by rewrite in_fsetU !mem_supp msetUE addn_eq0 negb_and.
Qed.

Lemma msetUC : commutative msetU.
Proof.
move=> m1 m2; apply/eq_ffun=> x.
by rewrite !msetUE addnC.
Qed.

Lemma msetUA : associative msetU.
Proof.
move=> m1 m2 m3; apply/eq_ffun=> x.
by rewrite !msetUE addnA.
Qed.

Lemma msetUI : right_injective msetU.
Proof.
move=> m1 m2 m3 /eq_ffun e; apply/eq_ffun=> x.
by move/(_ x): e; rewrite !msetUE=> /addnI.
Qed.

Lemma msetIU : left_injective msetU.
Proof.
move=> m1 m2 m3 /eq_ffun e; apply/eq_ffun=> x.
by move/(_ x): e; rewrite !msetUE=> /addIn.
Qed.

Definition msetD m1 m2 : {mset T} :=
  mkffun (fun x => m1 x - m2 x) (supp m1 :|: supp m2).
Notation "m1 ∖ m2" := (msetD m1 m2)
  (at level 25, left associativity) : mset_scope.

Lemma msetDE m1 m2 x : msetD m1 m2 x = m1 x - m2 x.
Proof.
rewrite mkffunE in_fsetU !mem_supp.
by case: eqP=> //= ->; case: eqP=> //= ->.
Qed.

Lemma msetUK m : cancel (msetU m) (msetD^~ m).
Proof.
move=> m'; apply/eq_ffun=> x; rewrite msetDE msetUE.
by rewrite addKn.
Qed.

Lemma msetKU m : cancel (msetU^~ m) (msetD^~ m).
Proof. by move=> m'; rewrite msetUC msetUK. Qed.

Definition mset1 x : {mset T} :=
  mkffun ([eta pred1 x] : T -> nat) (fset1 x).

Lemma mset1E x y : mset1 x y = (x == y).
Proof.
rewrite /mset1 mkffunE in_fset1 /= eq_sym.
by case: eq_op.
Qed.

Lemma supp_mset1 x : supp (mset1 x) = fset1 x.
Proof.
apply/eq_fset=> y; rewrite mem_supp mset1E in_fset1 [y == x]eq_sym.
by case: (x == y).
Qed.

Lemma mset1_inj : injective mset1.
Proof.
move=> x y /eq_ffun/(_ y).
rewrite !mset1E eqxx=> e /=; apply/eqP.
by case: (x == y) e.
Qed.

Definition mset0 : {mset T} :=
  mkffun (fun => 0) fset0.
Notation "∅" := mset0 (at level 0) : mset_scope.

Lemma mset0E x : mset0 x = 0.
Proof. by rewrite mkffunE. Qed.

Lemma supp_mset0 : supp mset0 = fset0.
Proof.
by apply/eq_fset=> x; rewrite mem_supp mset0E eqxx.
Qed.

Lemma mset0U : left_id mset0 msetU.
Proof.
by move=> m; apply/eq_ffun=> x; rewrite msetUE mset0E.
Qed.

Lemma msetU0 : right_id mset0 msetU.
Proof. by move=> m; rewrite msetUC mset0U. Qed.

Lemma mset1_eq0 x : (mset1 x == ∅) = false.
Proof. by apply/negbTE/eqP=> /eq_ffun/(_ x); rewrite mset1E eqxx. Qed.

Lemma msetU_eq0 m1 m2 : (m1 ∪ m2 == ∅) = (m1 == ∅) && (m2 == ∅).
Proof.
apply/(sameP eqP)/(iffP andP).
  by move=> [/eqP -> /eqP ->]; rewrite mset0U.
move=> /eq_ffun e; split; apply/eqP/eq_ffun=> x; apply/eqP.
- by move/(_ x)/eqP: e; rewrite msetUE mset0E addn_eq0; case/andP.
- by move/(_ x)/eqP: e; rewrite msetUE mset0E addn_eq0; case/andP.
Qed.

Lemma eq_msetU1 m1 m2 x y :
  m1 ∪ mset1 x = m2 ∪ mset1 y →
  x != y →
  {m | m1 = m ∪ mset1 y ∧ m2 = m ∪ mset1 x}.
Proof.
move=> /eq_ffun e ne; exists (m1 ∖ mset1 y).
split; apply/eq_ffun=> z; move/(_ z): e; rewrite ?(msetUE, msetDE, mset1E).
- case: (altP (y =P z))=> [<-|ne']; rewrite ?(addn0, subn0) //.
  by rewrite (negbTE ne) addn0=> ->; rewrite addnK.
- case: (altP (y =P z))=> [<-|ne']; rewrite ?(addn0, subn0) //.
  by rewrite (negbTE ne) !addn0 addn1 subn1 => ->.
Qed.

Definition msetM n m : {mset T} :=
  mkffun (λ x, n * m x) (supp m).

Lemma msetME n m x : msetM n m x = n * m x.
Proof.
rewrite mkffunE.
by case: ifPn=> // /suppPn ->; rewrite muln0.
Qed.

Lemma msetM0 m : msetM 0 m = ∅.
Proof. by apply/eq_ffun=> x; rewrite msetME. Qed.

Lemma msetMn0 n : msetM n ∅ = ∅.
Proof. by apply/eq_ffun=> x; rewrite msetME muln0. Qed.

Lemma msetM1 m : msetM 1 m = m.
Proof. by apply/eq_ffun=> x; rewrite msetME mul1n. Qed.

Lemma msetMDl n1 n2 m : msetM (n1 + n2) m = msetM n1 m ∪ msetM n2 m.
Proof.
by apply/eq_ffun=> x; rewrite !(msetME, msetUE) mulnDl.
Qed.

Lemma msetMS n m : msetM n.+1 m = m ∪ msetM n m.
Proof. by rewrite -addn1 msetMDl msetM1 msetUC. Qed.

Lemma msetMDr n m1 m2 : msetM n (m1 ∪ m2) = msetM n m1 ∪ msetM n m2.
Proof.
by apply/eq_ffun=> x; rewrite !(msetME, msetUE) mulnDr.
Qed.

Lemma supp_msetM n m : supp (msetM n m) = if n == 0 then fset0 else supp m.
Proof.
elim: n=> [|n IH] //=; rewrite ?msetM0 ?supp0 //.
rewrite msetMS supp_msetU {}IH.
by case: (n)=> //=; rewrite ?fsetU0 ?fsetUid.
Qed.

Lemma msetM_eq0 n m : (msetM n m == ∅) = (n == 0) || (m == ∅).
Proof.
elim: n=> [|n IH]; first by rewrite msetM0 eqxx.
rewrite msetMS msetU_eq0 {}IH.
by case: n (m == ∅)=> [|?] [].
Qed.

Definition msetn n x : {mset T} :=
  mkffun (λ _, n) (fset1 x).

Lemma msetnE n x y : msetn n x y = if x == y then n else 0.
Proof. by rewrite mkffunE in_fset1 eq_sym. Qed.

Lemma msetn0 x : msetn 0 x = ∅.
Proof. by apply/eq_ffun=> y; rewrite msetnE; case: eqP. Qed.

Lemma msetnS n x : msetn n.+1 x = msetn n x ∪ mset1 x.
Proof.
apply/eq_ffun=> y; rewrite msetUE !(mset1E, msetnE).
by case: eq_op; rewrite ?addn1.
Qed.

Lemma msetn1 x : msetn 1 x = mset1 x.
Proof. by rewrite msetnS msetn0 mset0U. Qed.

Definition mcard m := \sum_(x <- supp m) m x.

Lemma mcard0 : mcard mset0 = 0.
Proof. by rewrite /mcard supp_mset0 big_nil. Qed.

Canonical msetU_law := Monoid.Law msetUA mset0U msetU0.
Canonical msetU_comm_law := Monoid.ComLaw msetUC.

Lemma mcard1 x : mcard (mset1 x) = 1.
Proof.
by rewrite /mcard supp_mset1 /= big_seq1 mset1E eqxx.
Qed.

Lemma mcard_eq0 m : (mcard m == 0) = (m == mset0).
Proof.
apply/(sameP idP)/(iffP idP).
  by move=> /eqP ->; rewrite mcard0.
move=> ecard.
have [emp|/fset0Pn [x e]] := altP (supp m =P fset0).
  apply/eqP/eq_ffun=> x; rewrite mset0E.
  by have /suppPn m_x : x \notin supp m by rewrite emp.
move: ecard; rewrite /mcard.
have -> : supp m = x |: (supp m :\ x).
  apply/eq_fset=> y; rewrite in_fsetU1 in_fsetD1.
  by case: (y =P x) e=> [->|].
rewrite big_fsetU1 /= ?in_fsetD1 ?eqxx //.
by move: e; rewrite mem_supp; case: (m x).
Qed.

Lemma mcardU m1 m2 : mcard (m1 ∪ m2) = mcard m1 + mcard m2.
Proof.
rewrite /mcard supp_msetU.
under eq_big=> [x|x xP]; first over.
  rewrite msetUE; over.
rewrite big_split /=.
have {1}-> : supp m1 :|: supp m2 = supp m1 :|: supp m2 :\: supp m1.
  apply/eq_fset=> x; rewrite !in_fsetU !in_fsetD.
  by case: (x \in supp m1).
rewrite big_fsetU /=; last first.
  by rewrite fdisjointC; apply/fdisjointP=> ? /fsetDP [].
have {1}-> : supp m1 :|: supp m2 = supp m1 :\: supp m2 :|: supp m2.
  apply/eq_fset=> x; rewrite !in_fsetU !in_fsetD.
  case: (x \in supp m2)=> //=; by rewrite orbT.
rewrite big_fsetU /=; last first.
  by apply/fdisjointP=> ? /fsetDP [].
rewrite !addnA (ACl ((1*4)*(2*3))) /= -[RHS]addn0; congr addn.
apply/eqP; rewrite addn_eq0; apply/andP; split.
- by rewrite big_seq; apply/eqP/big1=> x /fsetDP [_ /suppPn].
- by rewrite big_seq; apply/eqP/big1=> x /fsetDP [_ /suppPn].
Qed.

Lemma mset_rect (P : {mset T} → Type) :
  P ∅ →
  (∀ x m, P m → P (m ∪ mset1 x)) →
  ∀ m, P m.
Proof.
move=> H0 H1 m.
move esupp: (supp m)=> X.
elim/fset_rect: X m esupp=> [|x X x_X IH] m esupp.
  suff ->: m = ∅ by [].
  apply/eq_ffun=> x.
  by have /suppPn -> : x \notin supp m by rewrite esupp.
pose m1 := msetn (m x) x.
pose m2 := m ∖ m1.
have em :  m = m1 ∪ m2.
  apply/eq_ffun=> y; rewrite !(msetUE, msetDE, msetnE).
  by have [<-|ne] := altP (x =P y); rewrite ?subnn ?addn0 ?subn0.
have esupp2: supp m2 = X.
  apply/eq_fset=> y; rewrite mem_supp msetDE msetnE.
  have [<-|ne] := altP (x =P y); rewrite ?subnn ?(negbTE x_X) //.
  by rewrite subn0 -mem_supp esupp in_fsetU1 eq_sym (negbTE ne).
move: x_X IH; rewrite -{}esupp2 => x_m2 /(_ _ erefl) IH.
move: m (m x) @m1 m2 IH em {x_m2 esupp} => _ n m1 m2 IH ->.
elim: n @m1 IH=> [|n IH]; rewrite /= ?mset0U ?msetn0 ?mset0U //.
by rewrite msetnS (ACl (1*3*2)) /= => ?; apply: H1; apply: IH.
Qed.

Lemma msetU1_eq1 m x y : m ∪ mset1 x = mset1 y → (m, x) = (∅, y).
Proof.
move=> e; move/eq_ffun/(_ x): (e).
rewrite msetUE !mset1E eqxx addn1.
case: (y =P _) e=> // -> e _.
by move: e; rewrite -[X in _ = X]mset0U=> /msetIU ->.
Qed.

Lemma msetU1_eq0 m x : m ∪ mset1 x ≠ ∅.
Proof.
move/eq_ffun/(_ x).
by rewrite msetUE mset1E eqxx addn1 mset0E.
Qed.

Inductive mset_dec Δ1 Δ2 : {mset T} → {mset T} → Type :=
| MSetDec Γ : mset_dec Δ1 Δ2 (Γ ∪ Δ2) (Γ ∪ Δ1).

Lemma mset_decP m11 m12 m21 m22 :
  fdisjoint (supp m12) (supp m22) →
  m11 ∪ m12 = m21 ∪ m22 →
  mset_dec m12 m22 m11 m21.
Proof.
move=> ne e.
pose m := m11 ∖ m22.
have em : m11 = m ∪ m22.
  apply/eq_ffun=> x; move/eq_ffun/(_ x): (e).
  rewrite !msetUE msetDE.
  have [xin|/suppPn ->] := boolP (x \in supp m12).
    move/(fdisjointP _ _ ne)/suppPn: xin=> ->.
    by rewrite subn0 !addn0.
  by rewrite addn0=> ->; rewrite addnK.
move: m em e => {}m11 ->.
by rewrite (ACl (1*3*2)) /= => /msetIU <-.
Qed.

Lemma mset_decPnn n1 n2 x1 x2 m1 m2 :
  x1 != x2 →
  m1 ∪ msetM n1 (mset1 x1) = m2 ∪ msetM n2 (mset1 x2) →
  mset_dec (msetM n1 (mset1 x1)) (msetM n2 (mset1 x2)) m1 m2.
Proof.
move=> ne; apply: mset_decP.
apply/fdisjointP=> y.
rewrite !mem_supp !msetME !mset1E.
case: (x1 =P y)=> [<-|] // _.
- by rewrite [x2 == x1]eq_sym (negbTE ne) muln0.
- by rewrite muln0.
Qed.

Lemma mset_decPn1 n1 x1 x2 m1 m2 :
  x1 != x2 →
  m1 ∪ msetM n1 (mset1 x1) = m2 ∪ mset1 x2 →
  mset_dec (msetM n1 (mset1 x1)) (mset1 x2) m1 m2.
Proof.
rewrite -[mset1 x2]msetM1; apply: mset_decPnn.
Qed.

Lemma mset_decP11 x1 x2 m1 m2 :
  x1 != x2 →
  m1 ∪ mset1 x1 = m2 ∪ mset1 x2 →
  mset_dec (mset1 x1) (mset1 x2) m1 m2.
Proof.
rewrite -[mset1 x1]msetM1 -[mset1 x2]msetM1; apply: mset_decPnn.
Qed.

End MSet.

Bind Scope mset_scope with mset_of.

Arguments msetU {_} _ _.
Arguments msetD {_} _ _.
Arguments mset0 {_}.
Arguments mcard {_} _.

Notation "∅" := mset0 (at level 0) : mset_scope.
Notation "m1 ∪ m2" := (msetU m1 m2)
  (at level 25, left associativity) : mset_scope.
Notation "m1 ∖ m2" := (msetD m1 m2)
  (at level 25, left associativity) : mset_scope.
Notation "{ 'mset' T }" :=
  (mset_of (Phant T))
  (at level 0, format "{ 'mset'  T }") : form_scope.

Declare Scope ll_scope.
Delimit Scope ll_scope with ll.

Inductive ll :=
| L1
| LConst of nat
| LWith of ll & ll
| LTens of ll & ll
| LLoli of ll & ll
| LPlus of ll & ll
| LBang of ll.

Definition ll_indMixin :=
  [indMixin for ll_rect].
Canonical ll_indType :=
  IndType _ ll ll_indMixin.
Definition ll_eqMixin :=
  [derive eqMixin for ll].
Canonical ll_eqType :=
  EqType ll ll_eqMixin.
Definition ll_choiceMixin :=
  [derive choiceMixin for ll].
Canonical ll_choiceType :=
  Eval hnf in ChoiceType ll ll_choiceMixin.
Definition ll_ordMixin :=
  [derive ordMixin for ll].
Canonical ll_ordType :=
  Eval hnf in OrdType ll ll_ordMixin.

Bind Scope ll_scope with ll.

Notation "1" := L1 (at level 0) : ll_scope.
Notation "A ⊗ B" := (LTens A B)
  (at level 20, left associativity) : ll_scope.
Notation "A × B" := (LWith A B)
  (at level 20, left associativity) : ll_scope.
Notation "A ⊸ B" := (LLoli A B)
  (at level 30, right associativity) : ll_scope.
Notation "A ⊕ B" := (LPlus A B)
  (at level 25, left associativity) : ll_scope.
Notation "! A" := (LBang A)
  (at level 9, format "! A") : ll_scope.

Definition banged A :=
  match A with
  | !B => true
  | _  => false
  end%ll.

Definition ll_sub (P : ll → Type) A : Type :=
  match A with
  | L1 => unit
  | LConst _ => unit
  | A1 × A2 => (P A1 * P A2)%type
  | A1 ⊗ A2 => (P A1 * P A2)%type
  | A1 ⊸ A2 => (P A1 * P A2)%type
  | A1 ⊕ A2 => (P A1 * P A2)%type
  | !A => P A
  end%ll.

Lemma ll_rect' P : (∀ A, ll_sub P A → P A) → ∀ A, P A.
Proof. move=> IH; elim=> *; by apply: IH=> //=. Qed.

Module Multiset.

Section Derivations.

Implicit Types (Γ Δ : {mset ll}) (A B C : ll).

Reserved Notation "Γ ⊢ A" (at level 90, no associativity).
Reserved Notation "Γ ⊢cf A" (at level 90, no associativity).

Open Scope mset_scope.
Open Scope ll_scope.

Definition banged_ctx Γ := all banged (supp Γ).

Lemma banged_ctxU Γ Δ : banged_ctx (Γ ∪ Δ) = banged_ctx Γ && banged_ctx Δ.
Proof. by rewrite /banged_ctx supp_msetU all_fsetU. Qed.

Lemma banged_ctx1 A : banged_ctx (mset1 A) = banged A.
Proof. by rewrite /banged_ctx supp_mset1 /= andbT. Qed.

Lemma banged_ctxM n Γ : banged_ctx (msetM n Γ) = (n == 0) || banged_ctx Γ.
Proof. by rewrite /banged_ctx supp_msetM; case: ifP. Qed.

Inductive derivation Γ : ll → Type :=
| LAxiom A
  of Γ = mset1 A
: Γ ⊢ A

| LCut Δ1 Δ2 A B
  of Γ = Δ1 ∪ Δ2
  &  Δ1 ⊢ A
  &  Δ2 ∪ mset1 A ⊢ B
: Γ ⊢ B

| L1L Δ A
  of Γ = Δ ∪ mset1 L1
  &  Δ ⊢ A
: Γ ⊢ A

| L1R
  of Γ = ∅
: Γ ⊢ 1

| LWithL1 Δ A B C
  of Γ = Δ ∪ mset1 (A × B)
  &  Δ ∪ mset1 A ⊢ C
: Γ ⊢ C

| LWithL2 Δ A B C
  of Γ = Δ ∪ mset1 (A × B)
  &  Δ ∪ mset1 B ⊢ C
: Γ ⊢ C

| LWithR A B
  of Γ ⊢ A
  &  Γ ⊢ B
: Γ ⊢ A × B

| LTensL Δ A B C
  of Γ = Δ ∪ mset1 (A ⊗ B)
  &  Δ ∪ mset1 A ∪ mset1 B ⊢ C
: Γ ⊢ C

| LTensR Δ1 Δ2 A B
  of Γ = Δ1 ∪ Δ2
  &  Δ1 ⊢ A
  &  Δ2 ⊢ B
: Γ ⊢ A ⊗ B

| LLoliL Δ1 Δ2 A B C
  of Γ = Δ1 ∪ Δ2 ∪ mset1 (A ⊸ B)
  &  Δ1 ⊢ A
  &  Δ2 ∪ mset1 B ⊢ C
: Γ ⊢ C

| LLoliR A B
  of Γ ∪ mset1 A ⊢ B
: Γ ⊢ A ⊸ B

| LPlusL Δ A1 A2 B
  of Γ = Δ ∪ mset1 (A1 ⊕ A2)
  &  Δ ∪ mset1 A1 ⊢ B
  &  Δ ∪ mset1 A2 ⊢ B
: Γ ⊢ B

| LPlusR1 A1 A2
  of Γ ⊢ A1
: Γ ⊢ A1 ⊕ A2

| LPlusR2 A1 A2
  of Γ ⊢ A2
: Γ ⊢ A1 ⊕ A2

| LWeak Δ A B
  of Γ = Δ ∪ mset1 !A
  &  Δ ⊢ B
: Γ ⊢ B

| LContr Δ A B
  of Γ = Δ ∪ mset1 !A ∪ mset1 !A
  & Δ ∪ mset1 !A ⊢ B
: Γ ⊢ B

| LDerel Δ A B
  of Γ = Δ ∪ mset1 !A
  & Δ ∪ mset1 A ⊢ B
: Γ ⊢ B

| LProm A
  of banged_ctx Γ
  & Γ ⊢ A
: Γ ⊢ !A

where "Γ ⊢ A" := (derivation Γ A).

Fixpoint cut_free Γ A (d : Γ ⊢ A) : bool :=
  match d with
  | LAxiom _ _ => true
  | LCut _ _ _ _ _ _ _ => false
  | L1L _ _ _ d => cut_free d
  | L1R _ => true
  | LWithL1 _ _ _ _ _ d => cut_free d
  | LWithL2 _ _ _ _ _ d => cut_free d
  | LWithR _ _ d1 d2 => cut_free d1 && cut_free d2
  | LTensL _ _ _ _ _ d => cut_free d
  | LTensR _ _ _ _ _ d1 d2 => cut_free d1 && cut_free d2
  | LLoliL _ _ _ _ _ _ d1 d2 => cut_free d1 && cut_free d2
  | LLoliR _ _ d => cut_free d
  | LPlusL _ _ _ _ _ d1 d2 => cut_free d1 && cut_free d2
  | LPlusR1 _ _ d => cut_free d
  | LPlusR2 _ _ d => cut_free d
  | LWeak _ _ _ _ d => cut_free d
  | LContr _ _ _ _ d => cut_free d
  | LDerel _ _ _ _ d => cut_free d
  | LProm _ _ d => cut_free d
  end.

Inductive derivation_cf Γ : ll → Type :=
| LAxiom' A
  of Γ = mset1 A
: Γ ⊢cf A

| L1L' Δ A
  of Γ = Δ ∪ mset1 L1
  &  Δ ⊢cf A
: Γ ⊢cf A

| L1R'
  of Γ = ∅
: Γ ⊢cf 1

| LWithL1' Δ A B C
  of Γ = Δ ∪ mset1 (A × B)
  &  Δ ∪ mset1 A ⊢cf C
: Γ ⊢cf C

| LWithL2' Δ A B C
  of Γ = Δ ∪ mset1 (A × B)
  &  Δ ∪ mset1 B ⊢cf C
: Γ ⊢cf C

| LWithR' A B
  of Γ ⊢cf A
  &  Γ ⊢cf B
: Γ ⊢cf A × B

| LTensL' Δ A B C
  of Γ = Δ ∪ mset1 (A ⊗ B)
  &  Δ ∪ mset1 A ∪ mset1 B ⊢cf C
: Γ ⊢cf C

| LTensR' Δ1 Δ2 A B
  of Γ = Δ1 ∪ Δ2
  &  Δ1 ⊢cf A
  &  Δ2 ⊢cf B
: Γ ⊢cf A ⊗ B

| LLoliL' Δ1 Δ2 A B C
  of Γ = Δ1 ∪ Δ2 ∪ mset1 (A ⊸ B)
  &  Δ1 ⊢cf A
  &  Δ2 ∪ mset1 B ⊢cf C
: Γ ⊢cf C

| LLoliR' A B
  of Γ ∪ mset1 A ⊢cf B
: Γ ⊢cf A ⊸ B

| LPlusL' Δ A1 A2 B
  of Γ = Δ ∪ mset1 (A1 ⊕ A2)
  &  Δ ∪ mset1 A1 ⊢cf B
  &  Δ ∪ mset1 A2 ⊢cf B
: Γ ⊢cf B

| LPlusR1' A1 A2
  of Γ ⊢cf A1
: Γ ⊢cf A1 ⊕ A2

| LPlusR2' A1 A2
  of Γ ⊢cf A2
: Γ ⊢cf A1 ⊕ A2

| LWeak' Δ A B
  of Γ = Δ ∪ mset1 !A
  &  Δ ⊢cf B
: Γ ⊢cf B

| LContr' Δ A B
  of Γ = Δ ∪ mset1 !A
  & Δ ∪ mset1 !A ∪ mset1 !A ⊢cf B
: Γ ⊢cf B

| LDerel' Δ A B
  of Γ = Δ ∪ mset1 !A
  & Δ ∪ mset1 A ⊢cf B
: Γ ⊢cf B

| LProm' A
  of banged_ctx Γ
  & Γ ⊢cf A
: Γ ⊢cf !A

where " Γ ⊢cf A" := (derivation_cf Γ A).

Inductive context_match2 A : {mset ll} → {mset ll} → {mset ll} → Type :=
| ContextMatch2L Γ Δ : context_match2 A (Γ ∪ Δ) (Γ ∪ mset1 A) Δ
| ContextMatch2R Γ Δ : context_match2 A (Γ ∪ Δ) Γ (Δ ∪ mset1 A).

Lemma context_match2P Γ A Δ1 Δ2 :
  Γ ∪ mset1 A = Δ1 ∪ Δ2 →
  context_match2 A Γ Δ1 Δ2.
Proof.
move=> e.
have [in1|/suppPn e1] := boolP (A \in supp Δ1).
  have eΔ1 : Δ1 = Δ1 ∖ mset1 A ∪ mset1 A.
    apply/eq_ffun=> C; rewrite msetUE msetDE mset1E.
    case: (A =P C)=> [<-|ne]; rewrite ?subn0 ?addn0 //.
    by rewrite subn1 addn1 prednK // lt0n -mem_supp.
  move: (Δ1 ∖ mset1 A) eΔ1=> Δ1' ?; subst Δ1.
  move: e; rewrite (ACl (1*3*2)) /= => /msetIU ?; subst Γ.
  constructor.
have [in2|/suppPn e2] := boolP (A \in supp Δ2).
  have eΔ2 : Δ2 = Δ2 ∖ mset1 A ∪ mset1 A.
    apply/eq_ffun=> C; rewrite msetUE msetDE mset1E.
    case: (A =P C)=> [<-|ne]; rewrite ?subn0 ?addn0 //.
    by rewrite subn1 addn1 prednK // lt0n -mem_supp.
  move: (Δ2 ∖ mset1 A) eΔ2=> Δ2' ?; subst Δ2.
  move: e; rewrite msetUA /= => /msetIU ?; subst Γ.
  constructor.
by move/eq_ffun/(_ A): e; rewrite !msetUE mset1E eqxx e1 e2 addn1.
Qed.

Inductive context_match2n A : nat → {mset ll} → {mset ll} → {mset ll} → Type :=
| ContextMatch2n m n Γ Δ :
  context_match2n A (m + n) (Γ ∪ Δ) (Γ ∪ msetM m (mset1 A)) (Δ ∪ msetM n (mset1 A)).

Lemma context_match2Pn Γ n A Δ1 Δ2 :
  Γ ∪ msetM n (mset1 A) = Δ1 ∪ Δ2 →
  context_match2n A n Γ Δ1 Δ2.
Proof.
move=> e.
pose m1  := minn (Δ1 A) n.
pose m2  := n - m1.
pose Δ1' := Δ1 ∖ msetM m1 (mset1 A).
pose Δ2' := Δ2 ∖ msetM m2 (mset1 A).
have en : n = m1 + m2.
  by rewrite /m2 addnC subnK // geq_minr.
have eΔ1 : Δ1 = Δ1' ∪ msetM m1 (mset1 A).
  apply/eq_ffun=> B; rewrite msetUE msetDE msetME mset1E.
  case: (A =P B) => [<-|_]; last by rewrite muln0 subn0 addn0.
  by rewrite subnK // muln1 geq_minl.
have e12 : Γ A + n = Δ1 A + Δ2 A.
  by move/eq_ffun/(_ A): (e); rewrite !msetUE msetME mset1E eqxx muln1.
have l2 : n <= Δ1 A + Δ2 A by rewrite -e12 leq_addl.
have {}l2 : m2 <= Δ2 A.
  rewrite leq_subLR /m1; case: (ltngtP (Δ1 A) n)=> //.
  by rewrite leq_addr.
have eΔ2 : Δ2 = Δ2' ∪ msetM m2 (mset1 A).
  apply/eq_ffun=> B; rewrite msetUE msetDE msetME mset1E.
  case: (A =P B) => [<-|_]; last by rewrite muln0 subn0 addn0.
  by rewrite subnK // muln1.
have eΓ : Γ = Δ1' ∪ Δ2'.
  move: e; rewrite eΔ1 eΔ2 msetUA (ACl (1*3*(2*4))) /= -msetMDl -en.
  by apply: msetIU.
by rewrite en eΓ eΔ1 eΔ2; constructor.
Qed.

Inductive context_match21 A B : {mset ll} → {mset ll} → {mset ll} → Type :=
| ContextMatch21Eq Δ1 Δ2 of A = B
: context_match21 A B (Δ1 ∪ Δ2) Δ1 Δ2
| ContextMatch21NeqL Δ1 Δ2 of A != B
: context_match21 A B (Δ1 ∪ Δ2 ∪ mset1 B) (Δ1 ∪ mset1 A) Δ2
| ContextMatch21NeqR Δ1 Δ2 of A != B
: context_match21 A B (Δ1 ∪ Δ2 ∪ mset1 B) Δ1 (Δ2 ∪ mset1 A).

Lemma context_match21P Γ A Δ1 Δ2 B :
  Γ ∪ mset1 A = Δ1 ∪ Δ2 ∪ mset1 B →
  context_match21 A B Γ Δ1 Δ2.
Proof.
have [{B} <-|ne] := altP (A =P B).
  move=> /msetIU ->; exact: ContextMatch21Eq.
move e: (Δ1 ∪ Δ2)=> Δ e'.
case/mset_decP11: Γ Δ / e' e=> // Γ /esym e.
by case/context_match2P: Γ Δ1 Δ2 / e=> Δ1 Δ2; eauto using context_match21.
Qed.

Hint Constructors derivation_cf : core.

Definition cut_right Γ A Δ B : Type :=
  ∀ Δ', Δ' ∪ mset1 A = Δ → Γ ∪ Δ' ⊢cf B.

Lemma cut_elim_comm_axiom Γ A B :
  Γ ⊢cf A →
  cut_right Γ A (mset1 B) B.
Proof.
by move=> dA Δ /msetU1_eq1 [-> <-]; rewrite msetU0.
Qed.

Lemma cut_elim_comm_L1L Γ Δ A C :
  A != 1 →
  cut_right Γ A Δ C →
  cut_right Γ A (Δ ∪ mset1 1) C.
Proof.
move=> ne IH Δ' e.
case/mset_decP11: Δ' Δ / e IH=> //.
move=> Δ IH; rewrite msetUA.
by move/(_ _ erefl) in IH; eauto.
Qed.

Lemma cut_elim_comm_L1R Γ A : cut_right Γ A ∅ 1.
Proof. by move=> Δ' /msetU1_eq0. Qed.

Lemma cut_elim_comm_LWithL1 Γ Δ A B1 B2 C :
  A != B1 × B2 →
  cut_right Γ A (Δ ∪ mset1 B1) C →
  cut_right Γ A (Δ ∪ mset1 (B1 × B2)) C.
Proof.
move=> ne IH Δ' e.
case/mset_decP11: Δ' Δ / e IH=> //.
move=> Δ IH; rewrite msetUA.
rewrite (ACl (1*3*2)) /= in IH; move/(_ _ erefl) in IH.
by rewrite msetUA in IH; eauto.
Qed.

Lemma cut_elim_comm_LWithL2 Γ Δ A B1 B2 C :
  A != B1 × B2 →
  cut_right Γ A (Δ ∪ mset1 B2) C →
  cut_right Γ A (Δ ∪ mset1 (B1 × B2)) C.
Proof.
move=> ne IH Δ' e.
case/mset_decP11: Δ' Δ / e IH=> //.
move=> Δ IH; rewrite msetUA.
rewrite (ACl (1*3*2)) /= in IH; move/(_ _ erefl) in IH.
by rewrite msetUA in IH; eauto.
Qed.

Lemma cut_elim_comm_LWithR Γ Δ A B1 B2 :
  cut_right Γ A Δ B1 →
  cut_right Γ A Δ B2 →
  cut_right Γ A Δ (B1 × B2).
Proof. rewrite /cut_right; by eauto. Qed.

Lemma cut_elim_comm_LTensL Γ Δ A B1 B2 C :
  A != B1 ⊗ B2 →
  cut_right Γ A (Δ ∪ mset1 B1 ∪ mset1 B2) C →
  cut_right Γ A (Δ ∪ mset1 (B1 ⊗ B2)) C.
Proof.
move=> ne IH Δ' e.
case/mset_decP11: Δ' Δ / e IH=> //.
move=> Δ IH; rewrite msetUA.
rewrite (ACl (1*3*4*2)) /= in IH; move/(_ _ erefl) in IH.
by rewrite !msetUA in IH; eauto.
Qed.

Lemma cut_elim_comm_LTensR Γ A Δ1 B1 Δ2 B2 :
  Δ1 ⊢cf B1 →
  cut_right Γ A Δ1 B1 →
  Δ2 ⊢cf B2 →
  cut_right Γ A Δ2 B2 →
  cut_right Γ A (Δ1 ∪ Δ2) (B1 ⊗ B2).
Proof.
rewrite /cut_right; move=> d1 IH1 d2 IH2 Δ' e.
case/context_match2P: Δ' Δ1 Δ2 / e d1 IH1 d2 IH2 => Δ1 Δ2 d1 IH1 d2 IH2.
- by rewrite msetUA; eauto.
- by rewrite msetUA (ACl (2*(1*3))) /=; eauto.
Qed.

Lemma cut_elim_comm_LLoliL Γ A Δ1 B1 Δ2 B2 C :
  A != (B1 ⊸ B2) →
  Δ1 ⊢cf B1 →
  cut_right Γ A Δ1 B1 →
  Δ2 ∪ mset1 B2 ⊢cf C →
  cut_right Γ A (Δ2 ∪ mset1 B2) C →
  cut_right Γ A (Δ1 ∪ Δ2 ∪ mset1 (B1 ⊸ B2)) C.
Proof.
move=> ne d1 IH1 d2 IH2 Δ' e.
case/context_match21P: Δ' Δ1 Δ2 / e ne d1 IH1 d2 IH2=> Δ1 Δ2.
- by move=> ->; rewrite eqxx.
- by move=> _ _ _ /(_ _ erefl) d1 d2 _; rewrite !msetUA; eauto.
- move=> _ _ d1 _ _ /(_ (Δ2 ∪ mset1 B2)).
  rewrite (ACl (1*3*2)) /= => /(_ erefl); rewrite msetUA => d2.
  by rewrite !msetUA (ACl (2*(1*3)*4)) /=; eauto.
Qed.

Lemma cut_elim_comm_LLoliR Γ A Δ B1 B2 :
  cut_right Γ A (Δ ∪ mset1 B1) B2 →
  cut_right Γ A Δ (B1 ⊸ B2).
Proof.
rewrite /cut_right => IH Δ' e.
rewrite -e (ACl (1*3*2)) /= in IH.
by move/(_ _ erefl) in IH; rewrite msetUA in IH; eauto.
Qed.

Lemma cut_elim_comm_LPlusL Γ A Δ B1 B2 C :
  A != B1 ⊕ B2 →
  cut_right Γ A (Δ ∪ mset1 B1) C →
  cut_right Γ A (Δ ∪ mset1 B2) C →
  cut_right Γ A (Δ ∪ mset1 (B1 ⊕ B2)) C.
Proof.
move=> ne IH1 IH2 Δ' e.
case/mset_decP11: Δ' Δ / e IH1 IH2=> // Δ.
move=> /(_ (Δ ∪ mset1 B1)).
rewrite (ACl (1*3*2)) /= !msetUA => /(_ erefl) IH1.
move=> /(_ (Δ ∪ mset1 B2)).
rewrite (ACl (1*3*2)) /= msetUA => /(_ erefl) IH2.
by eauto.
Qed.

Lemma cut_elim_comm_LPlusR1 Γ A Δ B1 B2 :
  cut_right Γ A Δ B1 →
  cut_right Γ A Δ (B1 ⊕ B2).
Proof. by rewrite /cut_right => ???; apply: LPlusR1'; eauto. Qed.

Lemma cut_elim_comm_LPlusR2 Γ A Δ B1 B2 :
  cut_right Γ A Δ B2 →
  cut_right Γ A Δ (B1 ⊕ B2).
Proof. by rewrite /cut_right; eauto. Qed.

Lemma cut_elim_comm_LWeak Γ A Δ B C :
  A != !B →
  cut_right Γ A Δ C →
  cut_right Γ A (Δ ∪ mset1 !B) C.
Proof.
move=> ne IH Δ' e.
case/mset_decP11: Δ' Δ / e IH=> // Δ.
by move=> /(_ Δ erefl); rewrite msetUA; eauto.
Qed.

Lemma cut_elim_comm_LContr Γ A Δ B C :
  A != !B →
  cut_right Γ A (Δ ∪ mset1 !B ∪ mset1 !B) C →
  cut_right Γ A (Δ ∪ mset1 !B) C.
Proof.
move=> ne IH Δ' e.
case/mset_decP11: Δ' Δ / e IH=> // Δ.
rewrite (ACl (1*3*4*2)) /=.
by move=> /(_ _ erefl); rewrite !msetUA; eauto.
Qed.

Lemma cut_elim_comm_LDerel Γ A Δ B C :
  A != !B →
  cut_right Γ A (Δ ∪ mset1 B) C →
  cut_right Γ A (Δ ∪ mset1 !B) C.
Proof.
move=> ne IH Δ' e.
case/mset_decP11: Δ' Δ / e IH=> // Δ.
rewrite (ACl (1*3*2)) /=.
by move=> /(_ _ erefl); rewrite !msetUA; eauto.
Qed.

Lemma cut_elim_comm_LProm Γ A Δ C :
  ~~ banged A →
  banged_ctx Δ →
  cut_right Γ A Δ !C.
Proof.
move=> contra bΔ Δ' e; subst Δ.
move: bΔ; rewrite banged_ctxU banged_ctx1; case/andP=> bΔ' bA.
by rewrite bA in contra.
Qed.

Definition cut_left Γ A := ∀ Δ B, Δ ⊢cf B → cut_right Γ A Δ B.

Lemma cut_left_1 : cut_left ∅ 1.
Proof.
move=> Δ B; elim: Δ B / => //=.
- by move=> ?? ->; apply: cut_elim_comm_axiom; eauto.
- by move=> _ Δ' B -> d IH Γ /msetIU ->; rewrite mset0U.
- by move=> _ -> Γ /msetU1_eq0 [].
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL1.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL2.
- by move=> ??? _ IH1 _ IH2; apply: cut_elim_comm_LWithR.
- by move=> _ ???? -> _; apply: cut_elim_comm_LTensL.
- by move=> _ ???? ->; apply: cut_elim_comm_LTensR.
- by move=> _ ????? ->; apply: cut_elim_comm_LLoliL.
- by move=> ??? _; apply: cut_elim_comm_LLoliR.
- move=> _ ???? -> _ IH1 _ IH2; by apply: cut_elim_comm_LPlusL.
- by move=> ??? _; apply: cut_elim_comm_LPlusR1.
- by move=> ??? _; apply: cut_elim_comm_LPlusR2.
- by move=> ???? -> _; apply: cut_elim_comm_LWeak.
- by move=> ???? -> _; apply: cut_elim_comm_LContr.
- by move=> ???? -> _; apply: cut_elim_comm_LDerel.
- by move=> ??????; apply: cut_elim_comm_LProm.
Qed.

Lemma cut_left_tens Γ1 A1 Γ2 A2 :
  Γ1 ⊢cf A1 →
  cut_left Γ1 A1 →
  Γ2 ⊢cf A2 →
  cut_left Γ2 A2 →
  cut_left (Γ1 ∪ Γ2) (A1 ⊗ A2).
Proof.
move=> dA1 IHdA1 dA2 IHdA2 Δ B.
elim: Δ B / => //=.
- by move=> ?? ->; apply: cut_elim_comm_axiom; eauto.
- by move=> _ ?? -> _; apply: cut_elim_comm_L1L.
- by move=> _ ->; apply: cut_elim_comm_L1R.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL1.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL2.
- by move=> ??? _ IH1 _ IH2; apply: cut_elim_comm_LWithR.
- move=> _ Δ C1 C2 B ->.
  have [[<- <-]|ne] := altP (A1 ⊗ A2 =P C1 ⊗ C2).
    move=> dB _ ? /msetIU ->.
    move/(_ _ _ dB _ erefl): IHdA2; rewrite msetUA => {}dB.
    by move/(_ _ _ dB _ erefl): IHdA1; rewrite msetUA.
  by move=> _; apply: cut_elim_comm_LTensL.
- by move=> _ ???? ->; apply: cut_elim_comm_LTensR.
- by move=> _ ????? ->; apply: cut_elim_comm_LLoliL.
- by move=> ??? _; apply: cut_elim_comm_LLoliR.
- move=> _ ???? -> _ IH1 _ IH2; by apply: cut_elim_comm_LPlusL.
- by move=> ??? _; apply: cut_elim_comm_LPlusR1.
- by move=> ??? _; apply: cut_elim_comm_LPlusR2.
- by move=> ???? -> _; apply: cut_elim_comm_LWeak.
- by move=> ???? -> _; apply: cut_elim_comm_LContr.
- by move=> ???? -> _; apply: cut_elim_comm_LDerel.
- by move=> ??????; apply: cut_elim_comm_LProm.
Qed.

Lemma cut_left_with Γ A1 A2 :
  Γ ⊢cf A1 →
  cut_left Γ A1 →
  Γ ⊢cf A2 →
  cut_left Γ A2 →
  cut_left Γ (A1 × A2).
Proof.
move=> dA1 IHdA1 dA2 IHdA2 Δ B.
elim: Δ B / => //=.
- by move=> ?? ->; apply: cut_elim_comm_axiom; eauto.
- by move=> _ ?? -> _; apply: cut_elim_comm_L1L.
- by move=> _ ->; apply: cut_elim_comm_L1R.
- move=> _ Δ C1 C2 B ->.
  have [[<- <-]|ne] := altP (A1 × A2 =P C1 × C2).
    move=> dB _ ? /msetIU ->.
    by move/(_ _ _ dB _ erefl): IHdA1.
  by move=> _; apply: cut_elim_comm_LWithL1.
- move=> _ Δ C1 C2 B ->.
  have [[<- <-]|ne] := altP (A1 × A2 =P C1 × C2).
    move=> dB _ ? /msetIU ->.
    by move/(_ _ _ dB _ erefl): IHdA2.
  by move=> _; apply: cut_elim_comm_LWithL2.
- by move=> ??? _ IH1 _ IH2; apply: cut_elim_comm_LWithR.
- by move=> _ ???? -> _; apply: cut_elim_comm_LTensL.
- by move=> _ ???? ->; apply: cut_elim_comm_LTensR.
- by move=> _ ????? ->; apply: cut_elim_comm_LLoliL.
- by move=> ??? _; apply: cut_elim_comm_LLoliR.
- move=> _ ???? -> _ IH1 _ IH2; by apply: cut_elim_comm_LPlusL.
- by move=> ??? _; apply: cut_elim_comm_LPlusR1.
- by move=> ??? _; apply: cut_elim_comm_LPlusR2.
- by move=> ???? -> _; apply: cut_elim_comm_LWeak.
- by move=> ???? -> _; apply: cut_elim_comm_LContr.
- by move=> ???? -> _; apply: cut_elim_comm_LDerel.
- by move=> ??????; apply: cut_elim_comm_LProm.
Qed.

Lemma cut_left_loli Γ A1 A2 :
  (∀ Γ', Γ' ⊢cf A1 → cut_left Γ' A1) →
  Γ ∪ mset1 A1 ⊢cf A2 →
  (∀ Γ', Γ' ⊢cf A2 → cut_left Γ' A2) →
  cut_left Γ (A1 ⊸ A2).
Proof.
move=> IHdA1 dA2 IHdA2 Δ B.
elim: Δ B / => //=.
- by move=> ?? ->; apply: cut_elim_comm_axiom; eauto.
- by move=> _ ?? -> _; apply: cut_elim_comm_L1L.
- by move=> _ ->; apply: cut_elim_comm_L1R.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL1.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL2.
- by move=> ??? _ IH1 _ IH2; apply: cut_elim_comm_LWithR.
- by move=> _ ???? -> _; apply: cut_elim_comm_LTensL.
- by move=> _ ???? ->; apply: cut_elim_comm_LTensR.
- move=> _ Γ1 Γ2 C1 C2 B ->.
  have [[<- <-]|ne] := altP (A1 ⊸ A2 =P C1 ⊸ C2).
    move=> dA1 _ dB _ _ /msetIU ->.
    move/(_ (Γ ∪ mset1 A1) dA2 _ _ dB _ erefl): IHdA2=> {}dB.
    rewrite (ACl (1*3*2)) /= in dB.
    move/(_ Γ1 dA1 _ _ dB _ erefl): IHdA1.
    by rewrite msetUA (ACl (2*(1*3))).
  by move=> *; apply: cut_elim_comm_LLoliL.
- by move=> ??? _; apply: cut_elim_comm_LLoliR.
- move=> _ ???? -> _ IH1 _ IH2; by apply: cut_elim_comm_LPlusL.
- by move=> ??? _; apply: cut_elim_comm_LPlusR1.
- by move=> ??? _; apply: cut_elim_comm_LPlusR2.
- by move=> ???? -> _; apply: cut_elim_comm_LWeak.
- by move=> ???? -> _; apply: cut_elim_comm_LContr.
- by move=> ???? -> _; apply: cut_elim_comm_LDerel.
- by move=> ??????; apply: cut_elim_comm_LProm.
Qed.

Lemma LPlusR' Γ A1 A2 : (Γ ⊢cf A1) + (Γ ⊢cf A2) → Γ ⊢cf A1 ⊕ A2.
Proof. by case=> *; eauto. Qed.
Hint Resolve LPlusR' : core.

Lemma cut_left_plus Γ A1 A2 :
  (Γ ⊢cf A1) + (Γ ⊢cf A2) →
  (∀ Γ, Γ ⊢cf A1 → cut_left Γ A1) →
  (∀ Γ, Γ ⊢cf A2 → cut_left Γ A2) →
  cut_left Γ (A1 ⊕ A2).
Proof.
move=> dA IHA1 IHA2 Δ B.
elim: Δ B / => //=.
- by move=> ?? ->; apply: cut_elim_comm_axiom; eauto.
- by move=> _ ?? -> _; apply: cut_elim_comm_L1L.
- by move=> _ ->; apply: cut_elim_comm_L1R.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL1.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL2.
- by move=> ??? _ IH1 _ IH2; apply: cut_elim_comm_LWithR.
- by move=> _ ???? -> _; apply: cut_elim_comm_LTensL.
- by move=> _ ???? ->; apply: cut_elim_comm_LTensR.
- by move=> _ ????? ->; apply: cut_elim_comm_LLoliL.
- by move=> ??? _; apply: cut_elim_comm_LLoliR.
- move=> _ Δ C1 C2 B ->.
  have [[<- <-]|ne] := altP (A1 ⊕ A2 =P C1 ⊕ C2).
    case: dA=> dA dB1 IHdB1 dB2 IHdB2 _ /msetIU ->.
    + by move/(_ _ dA _ _ dB1 _ erefl) in IHA1.
    + by move/(_ _ dA _ _ dB2 _ erefl) in IHA2.
  by move=> *; apply: cut_elim_comm_LPlusL.
- by move=> Δ B1 B2 dB1 IHdB1 Δ' /IHdB1 e; eauto.
- by move=> Δ B1 B2 dB2 IHdB2 Δ' /IHdB2 e; eauto.
- by move=> ???? -> _; apply: cut_elim_comm_LWeak.
- by move=> ???? -> _; apply: cut_elim_comm_LContr.
- by move=> ???? -> _; apply: cut_elim_comm_LDerel.
- by move=> ??????; apply: cut_elim_comm_LProm.
Qed.

Lemma banged_ctx_weak Γ Δ A :
  banged_ctx Γ →
  Δ ⊢cf A →
  Γ ∪ Δ ⊢cf A.
Proof.
elim/mset_rect: Γ=> [|B Γ IH]; rewrite ?mset0U //.
rewrite banged_ctxU banged_ctx1 andbC.
case: B=> //= B bΓ dA.
by rewrite (ACl (1*3*2)) /=; eauto.
Qed.

Lemma banged_ctx_contr Γ Δ A :
  banged_ctx Δ →
  Γ ∪ Δ ∪ Δ ⊢cf A →
  Γ ∪ Δ ⊢cf A.
Proof.
elim/mset_rect: Δ Γ=> [|B Δ IH] Γ; rewrite ?msetU0 //.
rewrite banged_ctxU banged_ctx1 andbC.
case: B=> //= B /IH {}IH.
rewrite !msetUA (ACl (1*3*5*2*4)) /= => /IH.
by rewrite (ACl (1*4*2*3)) /= => {}IH; eauto.
Qed.

Definition cut_right_gen Γ A Δ B : Type :=
  ∀ n Δ', Δ' ∪ msetM n (mset1 A) = Δ → msetM n Γ ∪ Δ' ⊢cf B.

Lemma cut_rightW Γ A Δ B : cut_right_gen Γ A Δ B → cut_right Γ A Δ B.
Proof.
move=> H Δ'.
rewrite -[mset1 A]msetM1 -[Γ]msetM1.
exact: H.
Qed.

Lemma cut_elim_comm_axiom_gen Γ A B :
  Γ ⊢cf A →
  cut_right_gen Γ A (mset1 B) B.
Proof.
move=> dA [|n].
- move=> ?; rewrite msetM0 msetU0 => ->.
  by rewrite msetM0 mset0U; eauto.
- move=> ?; rewrite msetMS [mset1 A ∪ _]msetUC msetUA.
  move=> /msetU1_eq1 [/eqP e <-].
  rewrite msetU_eq0 msetM_eq0 in e.
  case/andP: e=> [/eqP -> e].
  case: n e=> [|n] //=; last first.
    by move=> /eqP/(congr1 mcard); rewrite mcard1 mcard0.
  by rewrite msetM1 msetU0.
Qed.

Lemma cut_elim_comm_L1L_gen Γ Δ A C :
  A != 1 →
  cut_right_gen Γ A Δ C →
  cut_right_gen Γ A (Δ ∪ mset1 1) C.
Proof.
move=> ne IH n Δ' e.
case/mset_decPn1: Δ' Δ / e IH=> // Δ IH.
rewrite msetUA; by move/(_ _ _ erefl) in IH; eauto.
Qed.

Lemma cut_elim_comm_L1R_gen Γ A : cut_right_gen Γ A ∅ 1.
Proof.
move=> [|n] Δ.
- by rewrite !msetM0 msetU0 => ->; rewrite msetU0; eauto.
- by rewrite -addn1 msetMDl msetM1 msetUA=> /msetU1_eq0.
Qed.

Lemma cut_elim_comm_LWithL1_gen Γ Δ A B1 B2 C :
  A != B1 × B2 →
  cut_right_gen Γ A (Δ ∪ mset1 B1) C →
  cut_right_gen Γ A (Δ ∪ mset1 (B1 × B2)) C.
Proof.
move=> ne IH n Δ' e.
case/mset_decPn1: Δ' Δ / e IH=> // Δ IH.
rewrite msetUA.
rewrite (ACl (1*3*2)) /= in IH; move/(_ _ _ erefl) in IH.
by rewrite msetUA in IH; eauto.
Qed.

Lemma cut_elim_comm_LWithL2_gen Γ Δ A B1 B2 C :
  A != B1 × B2 →
  cut_right_gen Γ A (Δ ∪ mset1 B2) C →
  cut_right_gen Γ A (Δ ∪ mset1 (B1 × B2)) C.
Proof.
move=> ne IH n Δ' e.
case/mset_decPn1: Δ' Δ / e IH=> // Δ IH.
rewrite msetUA.
rewrite (ACl (1*3*2)) /= in IH; move/(_ _ _ erefl) in IH.
by rewrite msetUA in IH; eauto.
Qed.

Lemma cut_elim_comm_LWithR_gen Γ Δ A B1 B2 :
  cut_right_gen Γ A Δ B1 →
  cut_right_gen Γ A Δ B2 →
  cut_right_gen Γ A Δ (B1 × B2).
Proof. rewrite /cut_right_gen; by eauto. Qed.

Lemma cut_elim_comm_LTensL_gen Γ Δ A B1 B2 C :
  A != B1 ⊗ B2 →
  cut_right_gen Γ A (Δ ∪ mset1 B1 ∪ mset1 B2) C →
  cut_right_gen Γ A (Δ ∪ mset1 (B1 ⊗ B2)) C.
Proof.
move=> ne IH n Δ' e.
case/mset_decPn1: Δ' Δ / e IH=> // Δ IH.
rewrite msetUA.
rewrite (ACl (1*3*4*2)) /= in IH; move/(_ _ _ erefl) in IH.
by rewrite !msetUA in IH; eauto.
Qed.

Lemma cut_elim_comm_LTensR_gen Γ A Δ1 B1 Δ2 B2 :
  Δ1 ⊢cf B1 →
  cut_right_gen Γ A Δ1 B1 →
  Δ2 ⊢cf B2 →
  cut_right_gen Γ A Δ2 B2 →
  cut_right_gen Γ A (Δ1 ∪ Δ2) (B1 ⊗ B2).
Proof.
rewrite /cut_right_gen; move=> d1 IH1 d2 IH2 n Δ' e.
case/context_match2Pn: n Δ' Δ1 Δ2 / e d1 IH1 d2 IH2=> m n Δ1 Δ2 d1 IH1 d2 IH2.
move/(_ _ _ erefl) in IH1.
move/(_ _ _ erefl) in IH2.
by rewrite msetMDl msetUA (ACl ((1*3)*(2*4))) /=; eauto.
Qed.

Lemma cut_elim_comm_LLoliL_gen Γ A Δ1 B1 Δ2 B2 C :
  A != (B1 ⊸ B2) →
  Δ1 ⊢cf B1 →
  cut_right_gen Γ A Δ1 B1 →
  Δ2 ∪ mset1 B2 ⊢cf C →
  cut_right_gen Γ A (Δ2 ∪ mset1 B2) C →
  cut_right_gen Γ A (Δ1 ∪ Δ2 ∪ mset1 (B1 ⊸ B2)) C.
Proof.
move=> ne d1 IH1 d2 IH2 n Δ' e.
move eΔ: (Δ1 ∪ Δ2) e => Δ e.
case/mset_decPn1: Δ' Δ / e eΔ=> // Δ /esym e.
case/context_match2Pn: n Δ Δ1 Δ2 / e d1 IH1 d2 IH2=> n1 n2 Δ1 Δ2.
rewrite [Δ2 ∪ _ ∪ _](ACl (1*3*2)) /=.
move=> d1 /(_ _ _ erefl) IH1 d2 /(_ _ _ erefl) IH2.
rewrite msetUA in IH2.
rewrite msetMDl !msetUA (ACl (1*3*(2*4)*5)) /=.
by eauto.
Qed.

Lemma cut_elim_comm_LLoliR_gen Γ A Δ B1 B2 :
  cut_right_gen Γ A (Δ ∪ mset1 B1) B2 →
  cut_right_gen Γ A Δ (B1 ⊸ B2).
Proof.
rewrite /cut_right_gen => IH n Δ' e.
rewrite -e (ACl (1*3*2)) /= in IH.
by move/(_ _ _ erefl) in IH; rewrite msetUA in IH; eauto.
Qed.

Lemma cut_elim_comm_LPlusL_gen Γ A Δ B1 B2 C :
  A != B1 ⊕ B2 →
  cut_right_gen Γ A (Δ ∪ mset1 B1) C →
  cut_right_gen Γ A (Δ ∪ mset1 B2) C →
  cut_right_gen Γ A (Δ ∪ mset1 (B1 ⊕ B2)) C.
Proof.
move=> ne IH1 IH2 n Δ' e.
case/mset_decPn1: Δ' Δ / e IH1 IH2=> // Δ.
rewrite (ACl (1*3*2)) /= => /(_ _ _ erefl).
rewrite msetUA=> IH1.
rewrite (ACl (1*3*2)) /= => /(_ _ _ erefl).
rewrite msetUA=> IH2.
by rewrite msetUA; eauto.
Qed.

Lemma cut_elim_comm_LPlusR1_gen Γ A Δ B1 B2 :
  cut_right_gen Γ A Δ B1 →
  cut_right_gen Γ A Δ (B1 ⊕ B2).
Proof. by rewrite /cut_right_gen => ????; apply: LPlusR1'; eauto. Qed.

Lemma cut_elim_comm_LPlusR2_gen Γ A Δ B1 B2 :
  cut_right_gen Γ A Δ B2 →
  cut_right_gen Γ A Δ (B1 ⊕ B2).
Proof. by rewrite /cut_right_gen; eauto. Qed.

Lemma cut_elim_comm_LWeak_gen Γ A Δ B C :
  A != !B →
  cut_right_gen Γ A Δ C →
  cut_right_gen Γ A (Δ ∪ mset1 !B) C.
Proof.
move=> ne IH n Δ' e.
case/mset_decPn1: Δ' Δ / e IH => // Δ.
by move=> /(_ _ Δ erefl); rewrite msetUA; eauto.
Qed.

Lemma cut_elim_comm_LContr_gen Γ A Δ B C :
  A != !B →
  cut_right_gen Γ A (Δ ∪ mset1 !B ∪ mset1 !B) C →
  cut_right_gen Γ A (Δ ∪ mset1 !B) C.
Proof.
move=> ne IH n Δ' e.
case/mset_decPn1: Δ' Δ / e IH => // Δ.
rewrite (ACl (1*3*4*2)) /=.
by move=> /(_ _ _ erefl); rewrite !msetUA; eauto.
Qed.

Lemma cut_elim_comm_LDerel_gen Γ A Δ B C :
  A != !B →
  cut_right_gen Γ A (Δ ∪ mset1 B) C →
  cut_right_gen Γ A (Δ ∪ mset1 !B) C.
Proof.
move=> ne IH n Δ' e.
case/mset_decPn1: Δ' Δ / e IH => // Δ.
rewrite (ACl (1*3*2)) /=.
by move=> /(_ _ _ erefl); rewrite !msetUA; eauto.
Qed.

Lemma cut_elim_comm_LProm_gen Γ A Δ C :
  banged A ==> banged_ctx Γ →
  banged_ctx Δ →
  cut_right_gen Γ A Δ  C →
  cut_right_gen Γ A Δ !C.
Proof.
move=> bΓ bΔ IH n Δ' e; subst Δ; move/(_ _ _ erefl) in IH.
move: bΔ; rewrite banged_ctxU; case/andP=> bΔ bA.
move: bA bΓ; rewrite banged_ctxM banged_ctx1.
case: (n =P 0) IH=> /= [->|_].
  by rewrite msetM0 mset0U; eauto.
move=> IH -> /= bΓ.
suff ?: banged_ctx (msetM n Γ ∪ Δ') by eauto.
by rewrite banged_ctxU banged_ctxM bΓ orbT.
Qed.

Lemma cut_left_bang Γ A :
  banged_ctx Γ →
  Γ ⊢cf A →
  (∀ Γ, Γ ⊢cf A → cut_left Γ A) →
  cut_left Γ !A.
Proof.
move=> bΓ dA IHA Δ B dB; apply: cut_rightW.
elim: Δ B / dB => //=.
- by move=> ?? ->; apply: cut_elim_comm_axiom_gen; eauto.
- by move=> _ ?? -> _; apply: cut_elim_comm_L1L_gen.
- by move=> _ ->; apply: cut_elim_comm_L1R_gen.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL1_gen.
- by move=> _ ???? -> _; apply: cut_elim_comm_LWithL2_gen.
- by move=> ??? _ IH1 _ IH2; apply: cut_elim_comm_LWithR_gen.
- by move=> _ ???? -> _; apply: cut_elim_comm_LTensL_gen.
- by move=> _ ???? ->; apply: cut_elim_comm_LTensR_gen.
- by move=> _ ????? ->; apply: cut_elim_comm_LLoliL_gen.
- by move=> ??? _; apply: cut_elim_comm_LLoliR_gen.
- move=> _ ???? -> _ IH1 _ IH2; by apply: cut_elim_comm_LPlusL_gen.
- by move=> ??? _; apply: cut_elim_comm_LPlusR1_gen.
- by move=> ??? _; apply: cut_elim_comm_LPlusR2_gen.
- move=> _ Δ C B -> dB IHdB.
  have [{C} [<-]|ne] := altP (!A =P !C); first case=> [|n].
  + move=> Δ'; rewrite !msetM0 msetU0 mset0U => {Δ'}->.
    by apply: LWeak'.
  + move=> Δ'; rewrite !msetMS msetUA (ACl (1*3*2)) -[Γ ∪ _ ∪ _]msetUA /=.
    move=> /msetIU /IHdB dB'; by apply: banged_ctx_weak.
  move=> n Δ' e.
  case/mset_decPn1: Δ' Δ / e dB IHdB=> // Δ dB IHdB.
  by move/(_ _ _ erefl): IHdB; rewrite msetUA; eauto.
- move=> _ Δ C B ->.
  have [{C} [<-]|ne] := altP (!A =P !C).
    move=> dB IHdB [|n] Δ'.
  + by rewrite !msetM0 msetU0 mset0U => ->; apply: LContr'.
  + move=> /(congr1 (msetU ^~ (mset1 !A))).
    rewrite (ACl (1*(3*2))) /= -msetMS => /IHdB.
    rewrite !msetMS !msetUA.
    rewrite (ACl (3*4*1*2)) /= [Γ ∪ _ ∪ _](ACl (2*3*1)) /=.
    by apply: banged_ctx_contr.
  move=> dB IHdB n Δ' e.
  case/mset_decPn1: Δ' Δ / e dB IHdB=> // Δ dB IHdB.
  move: IHdB; rewrite (ACl (1*3*4*2)) /= => /(_ _ _ erefl).
  by rewrite !msetUA; eauto.
- move=> _ Δ C B ->.
  have [{C} [<-]|ne] := altP (!A =P !C).
    move=> dB IHdB [|n] Δ'.
  + by rewrite !msetM0 msetU0 mset0U => ->; apply: LDerel'.
  + rewrite msetMS msetUA (ACl (1*3*2)) /= => /msetIU ?; subst Δ.
    move: IHdB; rewrite (ACl (1*3*2)) /= => /(_ _ _ erefl).
    rewrite msetUA=> {}dB.
    move/(_ _ dA _ _ dB _ erefl): IHA.
    by rewrite msetUA -msetMS.
  by move=> _; apply: cut_elim_comm_LDerel_gen.
- move=> Δ B bΔ dB IHdB n Δ' eΔ'; subst Δ.
  move/(_ _ _ erefl): IHdB; apply: LProm'.
  move: bΔ; rewrite !banged_ctxU !banged_ctxM bΓ orbT.
  by case/andP.
Qed.

Lemma cut_elim_aux A Γ : Γ ⊢cf A → cut_left Γ A.
Proof.
elim/ll_rect': A Γ=> A IHA Γ dA.
elim: Γ A / dA IHA=> /=.
- by move=> Γ A -> _ ? B dB Δ eΔ; rewrite msetUC eΔ.
- move=> _ Γ A -> dA IH /IH {}IH Δ B dB Δ' eΔ; subst Δ.
  rewrite (ACl (1*3*2)) /=.
  by move/(_ _ _ dB _ erefl) in IH; eauto.
- move=> _ -> _; exact: cut_left_1.
- move=> _ Γ C1 C2 A -> dA IH /IH {}IH Δ B dB Δ' eΔ; subst Δ.
  rewrite (ACl (1*3*2)) /=.
  by move/(_ _ _ dB _ erefl): IH; rewrite (ACl (1*3*2)); eauto.
- move=> _ Γ C1 C2 A -> dA IH /IH {}IH Δ B dB Δ' eΔ; subst Δ.
  rewrite (ACl (1*3*2)) /=.
  by move/(_ _ _ dB _ erefl): IH; rewrite (ACl (1*3*2)); eauto.
- move=> Γ A1 A2 dA1 _ dA2 _ [IHA1 IHA2].
  by apply: cut_left_with; eauto.
- move=> _ Γ C1 C2 A -> dA IH /IH {}IH Δ B dB Δ' eΔ; subst Δ.
  rewrite (ACl (1*3*2)) /=.
  by move/(_ _ _ dB _ erefl): IH; rewrite (ACl (1*4*2*3)) /=; eauto.
- move=> _ Γ1 Γ2 A1 A2 -> dA1 _ dA2 _ [IHA1 IHA2].
  by apply: cut_left_tens; eauto.
- move=> _ Γ1 Γ2 C1 C2 A -> dC1 _ dA IH /IH {}IH Δ B dB Δ' eΔ; subst Δ.
  move/(_ _ _ dB _ erefl): IH.
  rewrite (ACl (1*3*2)) /= => {}dB.
  by rewrite (ACl (1*(2*4)*3)) /=; eauto.
- move=> Γ A1 A2 dA2 _ [IH1 IH2]; by apply: cut_left_loli.
- move=> _ Γ C1 C2 A -> dA1 IH1 dA2 IH2 IHA Δ B dB Δ' eΔ; subst Δ.
  move: IH1 IH2=> /(_ IHA) IH1 /(_ IHA) IH2.
  rewrite (ACl (1*3*2)) /=.
  move/(_ _ _ dB _ erefl): IH1; rewrite (ACl (1*3*2)) /= => IH1.
  move/(_ _ _ dB _ erefl): IH2; rewrite (ACl (1*3*2)) /= => IH2.
  by eauto.
- move=> Γ A1 A2 dA1 _ [IH1 IH2].
  apply: cut_left_plus; eauto.
- move=> Γ A1 A2 dA1 _ [IH1 IH2].
  apply: cut_left_plus; eauto.
- move=> _ Γ C A -> dA IH /IH {}IH Δ B dB Δ' eΔ; subst Δ.
  rewrite (ACl (1*3*2)) /=.
  by move/(_ _ _ dB _ erefl): IH; eauto.
- move=> _ Γ C A -> dA IH /IH {}IH Δ B dB Δ' eΔ; subst Δ.
  rewrite (ACl (1*3*2)) /=.
  move/(_ _ _ dB _ erefl): IH.
  by rewrite (ACl (1*4*2*3)) /=; eauto.
- move=> _ Γ C A -> dA IH /IH {}IH Δ B dB Δ' eΔ; subst Δ.
  rewrite (ACl (1*3*2)) /=.
  move/(_ _ _ dB _ erefl): IH.
  by rewrite (ACl (1*3*2)) /=; eauto.
- move=> Γ A bΓ dA IH ?.
  by eauto using cut_left_bang.
Qed.

Lemma cut_elim Γ A : Γ ⊢ A → Γ ⊢cf A.
Proof.
elim: Γ A /; try by move=> *; subst; eauto.
move=> _ Δ1 Δ2 A B -> _ d1 _ d2.
by apply: cut_elim_aux; eauto.
Qed.

End Derivations.
