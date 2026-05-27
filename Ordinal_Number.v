Require Export MorseKelley.mk_theorems.

(**********************************************************************)
(* 序数相关引理 *)

Lemma Less_eq_E : ∀ a b, Ensemble b -> Rrelation a E b <-> a ≺ b.
Proof.
  split; intros.
  - red in H0. appA2H H0. destruct H1,H1,H1.
    apply MKT55 in H1; ope. destruct H1. subst; auto.
  - red. appA2G.
Qed.

Lemma Less_eq_E' : ∀ a b, Ensemble b -> Rrelation a E b <-> a ∈ b.
Proof.
  split; intros. eapply Less_eq_E; eauto. unfold Rrelation; appA2G.
Qed.

Ltac NSym :=
  match goal with
   | H: ?x ∈ ?x
     |- _ => eapply MKT101 in H; destruct H
   | H: ?x ≺ ?x
    |- _ => try red in H; eapply MKT101 in H; destruct H
  end.

Lemma trans_Ord_Num : ∀a b, Ordinal_Number a -> b ≺ a -> Ordinal_Number b.
Proof.
  intros. red in H. New MKT113a. destruct H1 as [_ H3].
  apply H3 in H. apply H in H0. auto.
Qed.

(**********************************************************************)
(* 序数相关性质定理 *)

(* transitivity *)
Theorem Ord_Num_trans : ∀a b c, Ordinal_Number c
  -> a ≺ b -> b ≺ c -> a ≺ c.
Proof.
  intros. New MKT113a. apply @ MKT107 in H2. apply MKT88b in H2.
  red in H2. specialize H2 with a b c. New H1.
  eapply trans_Ord_Num in H3; eauto. New H0. eapply trans_Ord_Num in H4; eauto.
  eapply (Less_eq_E a c); eauto; eapply H2; eauto;
  try eapply Less_eq_E; eauto.
Qed.

Corollary Ord_Num_trans' : ∀a b c, Ordinal_Number c
  -> a ≼ b -> b ≺ c -> a ≺ c.
Proof.
  intros. destruct H0. eapply Ord_Num_trans; eauto.
  rewrite H0; auto.
Qed.

Corollary Ord_Num_trans'' : ∀a b c, Ordinal_Number c
  -> a ≺ b -> b ≼ c -> a ≺ c.
Proof.
  intros. destruct H1. eapply Ord_Num_trans; eauto.
  rewrite <- H1; auto.
Qed.

(* antisymmetry *)
Theorem Ord_Num_antisym : ∀ a b, Ordinal_Number a -> Ordinal_Number b
  -> a ≺ b -> ~ (b ≺ a).
Proof.
  intros. red in H1. red. unfold Less. eapply MKT102; eauto.
Qed.

(* trichotomy *)
Theorem Ord_Num_tri : ∀ a b, Ordinal_Number a -> Ordinal_Number b
  -> a ≺ b \/ a = b \/ b ≺ a.
Proof.
  intros. unfold Less. New H. appA2H H. appA2H H0.
  eapply (Lemma113 a b) in H; eauto.
  repeat destruct H; auto. eapply (Less_eq_E a b) in H; eauto.
  eapply (Less_eq_E b a) in H; eauto.
Qed.

(* non-density *)
Theorem Ord_Num_not_dense : ∀ a b, Ordinal_Number a -> Ordinal_Number b ->
  a ≺ b -> ~ (b ≺ PlusOne a).
Proof.
  intros. New H. apply MKT123 in H2. destruct H2.
  specialize H3 with b. red. intros. elim H3. appA2G. red. appA2G.
  eapply MKT49a. red in H0. appA2H H0. auto. appA2H H2; auto.
Qed.

(**********************************************************************)

(* 定义 后继序数 *)
Definition Suc_Ord a: Prop :=∃ x, Ordinal_Number x /\ a = PlusOne x.

(* 定义 极限序数 *)
Definition Lim_Ord a: Prop := Ordinal_Number a /\ ~(Suc_Ord a).


(**********************************************************************)
(* 序数定义相关Fact *)

Lemma uni_Suc_Lim : ∀a, Ordinal_Number a -> Suc_Ord a <-> ~ Lim_Ord a.
Proof.
  split; intros. red. intros. destruct H1. auto.
  unfold Lim_Ord in H0. apply notandor in H0. destruct H0.
  contradiction. apply NNPP. auto.
Qed.

Lemma OrdNum_classic : ∀a, Ordinal_Number a -> Suc_Ord a \/ Lim_Ord a.
Proof.
  intros. TF (Suc_Ord a). left. auto. right. red. auto.
Qed.

Ltac Suc_not_Lim :=
  match goal with
    H1: Lim_Ord ?x,
    H2: Suc_Ord ?x
    |- _ => eapply uni_Suc_Lim in H2; eauto; contradiction
  end.

(**********************************************************************)
(* 空、后继、极限相关Fact *)

(* Φ *)
Lemma Φ_is_Ord : Ordinal_Number Φ.
Proof.
  red. appA2G.
  split; red; intros. New (@ MKT16 u). contradiction. emf.
Qed.

Lemma Φ_is_Lim_Ord : Lim_Ord Φ.
Proof.
  split. apply Φ_is_Ord. red. intros. red in H. destruct H,H.
  assert( x ∈ PlusOne x ). { appA2G. } rewrite <- H0 in H1.
  New @ MKT16. specialize H2 with x. contradiction.
Qed.

Lemma Φ_is_First_Ord : ∀ a, Ordinal_Number a -> a <> Φ -> Φ ≺ a.
Proof.
  intros. New Φ_is_Ord. New H. eapply (Ord_Num_tri a Φ) in H2; eauto.
  try repeat (destruct H2; auto). eapply MKT16 in H2. destruct H2.
  elim H0. auto.
Qed.

(* Suc_Ord *)
Lemma Suc_is_Ord : ∀a, Suc_Ord a -> Ordinal_Number a.
Proof.
  intros. destruct H,H. red in H. apply Lem123 in H. red. subst. auto.
Qed.

(* Lim_Ord *)
Lemma Lim_Ord_1 : ∀a, Ordinal_Number a -> Lim_Ord a
  <-> (∀ b, b ≺ a -> PlusOne b ≺ a).
Proof.
  split; intros.
  - New H1. apply trans_Ord_Num in H2; auto. New H2.
    eapply Lem123 in H3; eauto. New H3.
    eapply (Ord_Num_tri (PlusOne b) a) in H3; eauto.
    destruct H3; auto. destruct H3. destruct H0. elim H5.
    red. exists b; split; auto.
    eapply Ord_Num_not_dense in H1; eauto. contradiction.
  - red. split; auto. red. intros. destruct H1,H1.
    assert( x ≺ a ). rewrite H2; appA2G.
    apply H0 in H3. rewrite H2 in H3. eapply MKT101; eauto.
Qed.

(**********************************************************************)

(* ω *)
Lemma ω_Num_is_Suc_Ord : ∀ a, a ∈ ω -> a <> Φ -> Suc_Ord a.
Proof.
  intros. assert(∀ x, x ∈ ω -> x = Φ \/ ∃ v, v ∈ ω /\ x = PlusOne v).
  apply Mathematical_Induction; eauto.
  eapply H1 in H; eauto. destruct H. contradiction.
  destruct H,H. red. exists x. split; eauto. New MKT138.
  eapply (trans_Ord_Num ω x) in H3; eauto.
Qed.

Lemma ω_is_Lim_Ord : Lim_Ord ω.
Proof.
  red. split. eapply MKT138. red. intros. destruct H.
  destruct H. assert( x ∈ ω ). rewrite H0; appA2G.
  eapply MKT134 in H1. rewrite H0 in H1. eapply MKT101; eauto.
Qed.

Lemma ω_is_first_Lim_Ord : ∀ a, a <> Φ -> a ≺ ω -> ~ Lim_Ord a.
Proof.
  intros. New (ω_Num_is_Suc_Ord _ H0 H). New H1.
  eapply Suc_is_Ord in H2. eapply uni_Suc_Lim; auto.
Qed.


(**********************************************************************)
(* 定义 上确界 *)
Definition Sup_R A := ∩ (\{ λ v, A ⊂ R /\ v ∈ R /\ (∀ a, a ∈ A -> a ≼ v) \}).

Lemma FirstMember_eq : ∀ a b A,
  A ⊂ R -> FirstMember a E A -> FirstMember b E A -> a = b.
Proof.
  intros. destruct H0,H1. TF( a = b ); auto. New H0. eapply H3 in H5.
  New H1. eapply H2 in H6. New (H _ H0). New (H _ H1).
  eapply Ord_Num_tri in H7; eauto.
  destruct H7. eapply Less_eq_E in H7. contradiction. eauto.
  destruct H7; symmetry; auto. eapply Less_eq_E in H7. contradiction. eauto.
Qed.

Lemma Sup_R_eq_U : ∀ A, A ⊂ R -> Ensemble A -> Sup_R A = ∪ A.
Proof.
  intros. New H. eapply MKT120 in H1.
  assert( H': Ensemble (∪ A) ). eapply AxiomVI; eauto.
  set( X := \{ λ v, A ⊂ R /\ v ∈ R /\ (∀ a, a ∈ A -> a ≼ v) \} ).
  assert( FirstMember (∪ A) E X ).
  { red. split. appA2G. try repeat (split; try appA2G; auto). intros.
    New (H _ H2). appA2H H3. assert( a ⊂ ∪ A ). red. intros. appA2G.
    eapply MKT118; eauto. intros. appA2H H2. deand. red. intros.
    eapply (Less_eq_E y (∪ A)) in H6; eauto. appA2H H6. rdeHex.
    eapply H5 in H8. destruct H8. eapply MKT102; eauto. subst. NSym. }
  assert( X ⊂ R /\ X <> Φ ) as [].
  { split. red; intros. appA2H H3. deand; auto. TF( X = Φ ); auto.
    red in H2. deand. rewrite H3 in H2. emf. }
  eapply Lemma121 in H3; eauto.
  pose proof (FirstMember_eq (∩ X) (∪ A) X). eapply H5 in H3; eauto.
  red; intros. appA2H H6. deand; auto.
Qed.

Lemma Sup_R_eq : ∀ A B, A ⊂ R -> B ⊂ A
  -> (∀ a, a ∈ A -> (∃ b, b ∈ B /\ a ≼ b)) -> Sup_R A = Sup_R B.
Proof.
  intros. unfold Sup_R.
  assert( \{ λ v, A ⊂ R /\ v ∈ R /\ (∀ a0, a0 ∈ A -> a0 ≼ v) \}
        = \{ λ v, B ⊂ R /\ v ∈ R /\ (∀ a0, a0 ∈ B -> a0 ≼ v) \} ).
  { eqext; appA2H H2; deand; appA2G.
    split. red. intros. apply H0,H in H6. auto. split; auto.
    try repeat (split; auto). intros. apply H1 in H6.
    rdeHex. eapply H5 in H6; eauto. destruct H6. destruct H7. left.
    eapply (Ord_Num_trans a0 x z); eauto. subst; eauto. left. auto.
    subst; auto. }
  rewrite H2. auto.
Qed.
