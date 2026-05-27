Require Export OrdinalNum.Ordinal_Number.

(**********************************************************************)
(* 关于序数的超限归纳法 *)

Theorem R_Transfinite_Induction : ∀ (P :Class -> Prop) ,
  ( ∀ a, a ∈ R -> ( ∀ b, b ∈ a -> P b ) -> P a )
  -> ( ∀ x, x ∈ R -> P x ).
Proof.
  intros. apply NNPP. red. intros.
  set ( B := \{ λ b, b ∈ R /\ ~ P b \} ).
  assert( B ⊂ R ). { red. intros. appA2H H2. apply H3. }
  TF ( B = Φ ). assert( x ∈ B ). appA2G.
  rewrite H3 in H4. emf.
  eapply Lemma121 in H2 as []; eauto.
  appA2H H2. destruct H5. eapply H in H5; eauto.
  intros. TF ( b ∈ B ). apply H4 in H8.
  unfold Rrelation in H8. elim H8. appA2G.
  apply NNPP. red. intros. elim H8. appA2G.
  split; auto. New MKT113a. destruct H10 as [_ H10].
  apply H10 in H5; auto.
Qed.

Theorem The_Second_R_Transfinite_Induction : ∀ (P: Class -> Prop), P Φ
  -> (∀ a, Suc_Ord (PlusOne a) -> P a -> P (PlusOne a))
  -> (∀ a, Lim_Ord a -> a ≠ Φ -> (∀ b, b ≺ a -> P b) -> P a)
  -> (∀ x, x ∈ R -> P x).
Proof.
  intros. eapply (R_Transfinite_Induction P); eauto. intros.
  TF(a = Φ). subst; auto.
  New H3. apply OrdNum_classic in H6 as [].
  - destruct H6,H6. rewrite H7. eapply H0; eauto. exists x0; eauto.
    eapply H4; eauto. rewrite H7; appA2G.
  - eapply H1; eauto.
Qed.

Theorem The_Second_R_Transfinite_Induction' : ∀ (P: Class -> Prop), P Φ
  -> (∀ a, a ∈ R -> P a -> P (PlusOne a))
  -> (∀ a, Lim_Ord a -> (∀ b, b ≺ a -> P b) -> P a)
  -> (∀ a, a ∈ R -> P a).
Proof.
  intros. eapply (R_Transfinite_Induction P); eauto. intros.
  TF(a0 = Φ). subst; auto.
  New H3. apply OrdNum_classic in H6 as [].
  - destruct H6,H6. apply H0 in H6. rewrite H7; auto.
    apply H4. rewrite H7. appA2G.
  - eapply H1; eauto.
Qed.

(* 关于自然数的超限归纳法 *)
Theorem ω_Transfinite_Induction : ∀ (P :Class -> Prop) ,
  ( ∀ a, a ∈ ω -> ( ∀ x, x ∈ a -> P x ) -> P a )
  -> ( ∀ y, y ∈ ω -> P y ).
Proof.
  intros. apply NNPP. red. intros.
  set ( B := \{ λ x, x ∈ ω /\ ~ P x \} ).
  assert( B ⊂ ω ). { red. intros. appA2H H2. apply H3. }
  TF ( B = Φ ). assert( y ∈ B ). appA2G.
  rewrite H3 in H4. emf. New MKT138. appA2H H4. New H5.
  apply MKT107 in H6. New H6. destruct H7 as [_ H7].
  eapply H7 in H2 as []; eauto. destruct H2.
  appA2H H2. destruct H9. eapply H in H9; eauto.
  intros. TF ( x0 ∈ B ). apply H8 in H12.
  unfold Rrelation in H12. elim H12. appA2G.
  apply NNPP. red. intros. elim H12. appA2G.
  split; auto. destruct H5 as [_ H5]. apply H5 in H9; auto.
Qed.

(* Check Mathematical_Induction. *)
(* ∀ (P :Class -> Prop), P Φ
  -> (∀ k, k ∈ ω -> P k -> P (PlusOne k))
  -> (∀ n, n ∈ ω -> P n).
Proof. *)


