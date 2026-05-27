Require Export OrdinalNum.R_Operation_Mult.

(* 幂运算 *)

Definition G1_E := \{\ λ u v, u ∈ μ /\ v = PlusOne Φ \}\.

Definition G2_E a := \{\ λ u v, u ∈ μ /\
  ( ( u ∈ R /\ v = u ⋅ a ) \/ ( u ∉ R /\ v = Φ ) ) \}\.

Definition G3_E := \{\ λ u v, u ∈ μ /\
  ( ( Function u /\ v = ∪(ran(u)) ) \/ ( ~ Function u /\ v = Φ ) ) \}\.

Theorem ExpFunction_R : ∀ a, a ∈ R -> exists ! F, OnTo F R R
  /\ F[Φ] = PlusOne Φ
  /\ ∀n, Ordinal_Number n -> F[PlusOne n] = F[n] ⋅ a
  /\ ∀n, Ordinal_Number n -> Lim_Ord n -> n ≠ Φ -> F[n] = ∪(ran(F|(n))).
Proof.
  intros.
  assert( F_G1: OnTo G1_E μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0.
    destruct H2. appoA2H H1. destruct H4; subst; auto.
    eqext. eapply MKT19; eauto. appA2G. exists (PlusOne Φ). appoA2G.
    red. intros. eapply MKT19; eauto. }
  assert( F_G2: OnTo (G2_E a) μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0.
    destruct H2 as [_ H2]. appoA2H H1. destruct H3 as [_ H3].
    try repeat (destruct H2,H3; try contradiction; subst; auto).
    eqext. eapply MKT19; eauto. appA2G. TF ( z ∈ R ).
    exists (z ⋅ a). appoA2G. eapply MKT49a; eauto.
    eapply R_Mult_in_R in H; eauto. exists Φ. appoA2G.
    red. intros. eapply MKT19; eauto. }
  assert( F_G3: OnTo G3_E μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0. destruct H2. appoA2H H1.
    destruct H4,H3,H3. destruct H5. destruct H5; subst; auto.
    destruct H5. contradiction. destruct H5,H5. contradiction. subst; auto.
    eqext. eapply MKT19; eauto. TF ( Function z ). appA2G.
    exists (∪(ran(z))). appoA2G. eapply MKT49a; eauto. apply AxiomVI.
    apply AxiomV; auto. apply fdme; auto.
    appA2G. exists Φ. appoA2G. red. intros. eapply MKT19; eauto. }
  New F_G1. eapply (Recursion_R.Recursion_R G1_E (G2_E a) G3_E) in H0; eauto.
  destruct H0 as [F [H0 H1]]. exists F. split.
  - clear H1. destruct H0,H1.
    assert( H_F: OnTo F R R ).
    destruct H0,H3. repeat (split; auto).
    red. intros. eapply Einr in H5; eauto. destruct H5,H5.
    assert( ( ∀ x, x ∈ R -> F[x] ∈ R ) ).
    { apply R_Transfinite_Induction. intros.
      TF( a0 = Φ ). subst a0.
      assert( G1_E [Φ] = PlusOne Φ ).
      { eqext. appA2H H9. apply H10. appA2G. appoA2G.
        appA2G. intros. appA2H H10. appoA2H H11. destruct H12; subst; auto. }
      rewrite H1,H9. auto.
      New H7. apply OrdNum_classic in H10 as [].
      destruct H10,H10.
      assert( Ensemble F[x0] ).
      { red in H10. rewrite <- H3 in H10. apply Property_dm in H10; auto. }
      New H10. apply H2 in H13 as [H13 _].
      assert( x0 ∈ a0 ). rewrite H11. appA2G. apply H8 in H14.
      assert( (F[x0] ⋅ a) ∈ R ). eapply R_Mult_in_R in H; eauto.
      assert( (G2_E a) [F[x0]] = F[x0] ⋅ a ).
      { eqext. appA2H H16. apply H17. appA2G. appoA2G. appA2G. intros.
        appA2H H17. appoA2H H18. destruct H19 as [_ H19].
        repeat (destruct H19,H19; try contradiction; subst; auto). }
      rewrite H11,H13,H16. auto.
      New H10. destruct H11 as [H11 _]. New H11.
      apply H2 in H11 as [_ H11]. apply H11 in H12; auto. clear H11.
      New H0. eapply (Property_res_dom F a0) in H11 as [];
      try rewrite H3; eauto. New H0. apply (MKT126a F a0) in H14.
      assert( Ensemble (∪ ran( F | (a0))) ).
      { apply AxiomVI. eapply frne; eauto. }
      assert( G3_E [F | (a0)] = ∪(ran(F | (a0))) ).
      { eqext. appA2H H16. apply H17. appA2G. appoA2G.
        appA2G. intros. appA2H H17. appoA2H H18. destruct H19.
        repeat (destruct H20,H20; try contradiction; subst; auto). }
      rewrite H12,H16.
      assert( ran( F | (a0)) ⊂ R ).
      { red; intros. eapply Einr in H17; eauto. destruct H17,H17. rewrite H18.
        rewrite H13 in H17. eapply (Property_res F a0 x0) in H0 as [H0 _];
        try rewrite H3; eauto. rewrite H0. apply H8. auto. }
      eapply MKT120 in H17. appA2G. }
    rewrite H6. apply H7. rewrite H3 in H5; auto.
    split; auto. split.
    + rewrite H1. eqext. appA2H H3. apply H4. appA2G. appoA2G.
      appA2G. intros. appA2H H4. appoA2H H5. destruct H6; subst; auto.
    + intros n H'. pose proof H' as H''. apply H2 in H'. clear H2.
      destruct H'. split.
      * clear H3. rewrite H2. assert( F[n] ∈ R ).
        { destruct H_F,H4. red in H''. rewrite <- H4 in H''.
          apply Property_dm in H''; auto. }
        eqext. appA2H H4. apply H5; clear H5.
        New H3. eapply (R_Mult_in_R F[n] a) in H5; eauto.
        appA2G. appoA2G. eapply MKT49a; eauto. split; auto. appA2H H3; auto.
        appA2G. intros. appA2H H5. appoA2H H6.
        destruct H7 as [_ H7].
        try repeat destruct H7,H7; try contradiction; subst; auto.
      * clear H2. intros. apply H3 in H2; clear H3; auto. rewrite H2.
        pose proof H0 as H'. destruct H' as [H' _].
        eapply (MKT126a F n0) in H'; eauto.
        destruct H4 as [H3 _]. destruct H0,H4. New H0.
        eapply (Property_res_dom F n0) in H0; try rewrite H4; eauto.
        destruct H0. eqext. appA2H H9. apply H10. clear H10.
        pose proof H' as H'''. eapply frne in H'''; eauto.
        assert(Ensemble (∪(ran(F|(n0))))). apply AxiomVI; auto.
        appA2G. appoA2G. appA2G. intros. appA2H H10. appoA2H H11. destruct H12.
        try repeat destruct H13,H13; subst; auto; contradiction.
  - clear H0. intros. specialize H1 with x'. apply H1. clear H1.
    destruct H0,H1. split. destruct H0,H3. split; auto. split.
    + rewrite H1. symmetry. eqext. appA2H H3. apply H4. appA2G. appoA2G.
      appA2G. intros. appA2H H4. appoA2H H5. destruct H6; subst; auto.
    + intros n H'. pose proof H' as H''. apply H2 in H'. clear H2.
      destruct H'. split.
      * clear H3. symmetry. rewrite H2. assert( H': x'[n] ∈ R ).
        { destruct H0,H3. red in H''. rewrite <- H3 in H''.
          apply Property_dm in H''; auto. }
        eqext. appA2H H3. apply H4; clear H4. New H.
        eapply (R_Mult_in_R x'[n] a) in H4; eauto.
        appA2G. appoA2G. eapply MKT49a; eauto. split; auto. appA2H H'; auto.
        appA2G. intros. appA2H H4. appoA2H H5. destruct H6.
        repeat (destruct H7,H7; try contradiction; subst; auto).
      * clear H2. intros. apply H3 in H2; clear H3; auto. rewrite H2.
        pose proof H0 as H'. destruct H' as [H' _].
        eapply (MKT126a x' n0) in H'; eauto.
        destruct H4 as [H3 _]. destruct H0,H4.
        eapply (Property_res_dom x' n0) in H0; try rewrite H4; eauto.
        destruct H0. symmetry. eqext. appA2H H8. apply H9. clear H9.
        pose proof H' as H'''. eapply frne in H'''; eauto.
        assert(Ensemble (∪(ran(x'|(n0))))). apply AxiomVI; auto.
        appA2G. appoA2G. appA2G. intros. appA2H H9. appoA2H H10. destruct H11.
        try repeat destruct H12,H12; subst; auto; contradiction.
Qed.

(* 对于任意a，运算Exp_R *)

Definition Exp_R a b:= ∩(\{ λ u, Ordinal_Number a /\
  ( ∀ F, OnTo F R R
  -> F[Φ] = PlusOne Φ
  -> (∀n, Ordinal_Number n -> F[PlusOne n] = F[n] ⋅ a)
  -> (∀n, Ordinal_Number n -> Lim_Ord n -> n ≠ Φ -> F[n] = ∪(ran(F|(n))))
  -> u = F[b]) \}).

Notation "a ^ b" := (Exp_R a b).

(**********************************************************************)
(* 幂验证 *)

Theorem Exp_R_Φ_r : forall a,
  Ordinal_Number a -> a ^ Φ = PlusOne Φ.
Proof.
  intros. New H. apply ExpFunction_R in H0.
  destruct H0 as [F [H0 H0']]. assert( a ^ Φ = F[Φ] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. destruct H0,H0,H3. New Φ_is_Ord. red in H5. rewrite <- H3 in H5.
    apply Property_dm in H5; eauto. repeat split; auto. intros.
    assert( F = F0 ). eapply H0'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[Φ] ). eapply H3; eapply H0; eauto. rewrite H4; auto. }
  rewrite H1. destruct H0,H2. auto.
Qed.

Theorem Exp_R_Suc : forall a b,
  Ordinal_Number a -> Ordinal_Number b -> a ^ (PlusOne b) = (a ^ b) ⋅ a.
Proof.
  intros. pose proof H as H_a. apply ExpFunction_R in H.
  destruct H as [F [H H']].
  assert( E: a ^ (PlusOne b)  =  F[PlusOne b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. red in H0. apply Lem123 in H0. destruct H,H,H3.
    rewrite <- H3 in H0. eapply Property_dm in H0; eauto. repeat split; auto.
    intros. assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[PlusOne b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite E. assert( E1: a ^ b  =  F[b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. red in H0. destruct H,H,H3.
    rewrite <- H3 in H0. eapply Property_dm in H0; eauto.
    repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite E1. destruct H,H1. apply H2 in H0. destruct H0. auto.
Qed.

Theorem Exp_R_Lim : forall a b,
  Ordinal_Number a -> Lim_Ord b -> b ≠ Φ
  -> a ^ b = ∪ \{ λ v, ∃ u, u ≺ b /\ v = (a ^ u) \}.
Proof.
  intros. pose proof H as H_a. apply ExpFunction_R in H.
  destruct H as [F [H H']].
  assert( a ^ b  =  F[b] ).
  { destruct H0. eqext. appA2H H3. apply H4.
    clear H4. appA2G. destruct H,H,H5. red in H0. rewrite <- H5 in H0.
    apply MKT69b in H0. auto. repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H4.
    assert( y = F[b] ). eapply H5; eapply H; eauto. rewrite H6; auto. }
  rewrite H2.
  assert( \{ λ v, ∃ u, u ≺ b /\ v = (a ^ u) \} = ran(F | (b)) ).
  { pose proof H as H''. destruct H,H,H4. eqext. appA2G. appA2H H6.
    destruct H7,H7. exists x. appA2G.
    assert( a ^ x = F[x] ).
    { destruct H0 as [H0 _]. eqext. appA2H H9. apply H10. clear H10.
      assert( Ensemble F[x] ).
      eapply trans_Ord_Num in H7; eauto. red in H7. rewrite <- H4 in H7.
      apply MKT69b in H7; auto. appA2G.
      red in H0. New H7. eapply MKT111 in H7; eauto.
      repeat split; auto. intros.
      assert( F = F0 ). eapply H'; eauto. subst F0. auto.
      appA2H H0; auto. appA2G. intros. appA2H H10.
      assert( y = F[x] ). eapply H11; eapply H''; eauto. rewrite H12; auto. }
    destruct H0 as [H0 _]. New H7. eapply trans_Ord_Num in H7; eauto.
    red in H7. rewrite <- H4 in H7. rewrite H9 in H8. subst z. split.
    eapply Property_Value; eauto. appoA2G.
    appA2H H6. destruct H7. appA2H H7.
    destruct H8. appoA2H H9. clear H9. destruct H10.
    appA2G. exists x. split; auto.
    assert( a ^ x = F[x] ).
    { destruct H0. eqext. appA2H H12. apply H13. clear H13.
      assert( Ensemble F[x] ).
      eapply trans_Ord_Num in H9; eauto. red in H9. rewrite <- H4 in H9.
      apply MKT69b in H9; auto. appA2G.
      eapply trans_Ord_Num in H9; eauto. repeat split; auto. intros.
      assert( F = F0 ). eapply H'; eauto. subst F0. auto.
      appA2G. intros. appA2H H13.
      assert( y = F[x] ). eapply H14; eapply H''; eauto. rewrite H15; auto. }
    rewrite H11. eapply Property_Fun in H8; eauto. }
  rewrite H3. New H0. destruct H,H0,H5. New H0. apply H7 in H0.
  destruct H0 as [_ H0]. eapply H0 in H8; eauto.
Qed.

(**********************************************************************)
(* 幂相关性质 *)

Corollary R_Exp_in_R : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> (a ^ b) ∈ R .
Proof.
  intros. pose proof H as H_a. pose proof H0 as H_b.
  apply ExpFunction_R in H. destruct H as [F [H H']].
  assert( a ^ b  =  F[b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. destruct H,H,H3. red in H0. rewrite <- H3 in H0.
    apply MKT69b in H0. auto. repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite H1. destruct H,H,H3. red in H_b. rewrite <- H3 in H_b.
  eapply Property_dm in H_b; auto.
Qed.

Corollary R_Exp_in_R' : forall a b, Ordinal_Number a -> (a ^ b) ∈ R
  -> Ordinal_Number b.
Proof.
  intros. pose proof H as H_a. apply ExpFunction_R in H.
  destruct H as [F [H _]]. TF( Ordinal_Number b ); auto.
  assert( a ^ b = ∩ \{ λ u, u = μ \} ).
  { unfold Exp_R.
    assert( \{ λ u, Ordinal_Number a /\
          (∀ F0, OnTo F0 R R -> F0 [Φ] = PlusOne Φ ->
          (∀ n, Ordinal_Number n -> F0 [PlusOne n] = F0 [n] ⋅ a ) ->
          (∀ n, Ordinal_Number n -> Lim_Ord n -> n ≠ Φ ->
           F0 [n] = ∪ ran( F0 | (n))) -> u = F0 [b]) \} = \{ λ u, u = μ \} ).
    { eqext. appA2H H2. appA2G. destruct H3. specialize H4 with F.
      destruct H,H5. assert( F[b] = μ ). eapply @ MKT69a; eauto.
      destruct H,H7. rewrite H7. auto. rewrite <- H7. eapply H4; eauto.
      intros. eapply H6 in H8 as []; eauto. intros. New H8.
      eapply H6 in H8 as [_ H8]. eapply H8 in H11; eauto.
      appA2H H2. subst z. eapply MKT39 in H2; destruct H2. }
   rewrite H2; clear H2. auto. }
  assert( ∩ \{ λ u, u = μ \} = μ ). eqext. appA2H H3; auto. appA2G. intros.
  appA2H H4. rewrite H5 in H4. eapply MKT39 in H4; destruct H4.
  rewrite H3 in H2. rewrite H2 in H0. appA2H H0. eapply MKT39 in H0; destruct H0.
Qed.

Corollary ω_Exp_in_ω : forall a b, a ∈ ω -> b ∈ ω
  -> (a ^ b) ∈ ω .
Proof.
  intros. assert( a ∈ R ). appA2H H. destruct H1. appA2G.
  eapply (ω_Transfinite_Induction (fun x => a ^ x ∈ ω )); eauto.
  intros. TF( a0 = Φ ). subst a0. rewrite Exp_R_Φ_r; eauto.
  New (ω_Num_is_Suc_Ord a0 H2 H4). destruct H5,H5.
  assert( x ∈ a0 ). subst a0. appA2G. apply H3 in H7.
  subst a0. rewrite Exp_R_Suc; eauto. eapply (ω_Mult_in_ω (a ^ x) a); eauto.
Qed.

Lemma R_Exp_1 : forall a b, Ordinal_Number a -> Ordinal_Number b -> Φ ≺ a -> b <> Φ
  -> a ≼ a ^ b.
Proof.
  intros. generalize dependent b.
  eapply (R_Transfinite_Induction (fun x => x <> Φ -> a ≼ a ^ x)); eauto.
  intros. TF( a = Φ ). rewrite H4 in H1. red in H1. emf.
  New H0. eapply OrdNum_classic in H5 as [].
  - New H5. destruct H5,H5.
    rewrite H7. rewrite Exp_R_Suc; eauto.
    assert( x ∈ a0 ). rewrite H7. appA2G.
    TF( x = Φ ). subst. rewrite Exp_R_Φ_r; auto.
    rewrite Mult_R_com_PlusOneΦ, Mult_R_Suc, Mult_R_Φ_r, Add_R_Φ_l; auto.
    right; auto. eapply R_Mult_2; eauto. apply R_Exp_in_R; eauto.
    apply H2 in H8; auto. red. intros.
    rewrite H10 in H8. destruct H8. emf. contradiction.
  - eapply MKT118. appA2H H; auto.
    New( R_Exp_in_R a a0 H H0 ). appA2H H6; auto.
    red. intros. rewrite Exp_R_Lim; eauto. appA2G.
    exists a. split; auto. appA2G.
    exists (PlusOne Φ). split. New H0. New (Φ_is_First_Ord a0 H7 H3).
    eapply Lim_Ord_1 in H8; eauto.
    rewrite Exp_R_Suc; try eapply Φ_is_Ord; auto. rewrite Exp_R_Φ_r; eauto.
    rewrite Mult_R_com_PlusOneΦ, Mult_R_Suc, Mult_R_Φ_r, Add_R_Φ_l; auto.
    eapply Φ_is_Ord; auto.
Qed.

Lemma R_Exp_2 : forall a b, Ordinal_Number a -> Ordinal_Number b -> (PlusOne Φ) ≺ a
  -> b ≼ a ^ b.
Proof.
  intros. generalize dependent b.
  eapply (R_Transfinite_Induction (fun x => x ≼ a ^ x)); eauto.
  intros. New H0. New (R_Exp_in_R a a0 H H0). eapply OrdNum_classic in H3 as [].
  - New H3. destruct H3,H3.
    assert( x ∈ a0 ). rewrite H6; appA2G.
    New H7. apply H2 in H7.  subst a0. eapply R_Add_1; eauto.
    destruct H7. assert( a ^ x ∈ a ^ (PlusOne x) ).
    { New (R_Exp_in_R a x H H3). New (Mult_R_PlusOneΦ (a ^ x) H7).
      rewrite <- H9. rewrite Exp_R_Suc; eauto.
      eapply Mult_R_PrOrder_a; eauto. New (Lem123 Φ Φ_is_Ord); auto.
      red. intros. rewrite H10 in H6. emf. }
    clear H8. eapply Ord_Num_trans; eauto.
    assert( a ^ x <> Φ ). red. intros.
    New H6. rewrite H7 in H9. New (Exp_R_Φ_r a H). rewrite <- H9 in H10.
    rewrite H7 in H10. rewrite <- H10 in H8. emf.
    rewrite Exp_R_Suc; auto. rewrite <- H6. rewrite <- H6 in H7.
    New (Lem123 _ Φ_is_Ord).
    New (Mult_R_PrOrder_a (PlusOne Φ) a x H9 H H3 H7 H1).
    rewrite Mult_R_PlusOneΦ in H10; eauto.
  - TF( a0 = Φ ). subst. left; rewrite Exp_R_Φ_r; auto. appA2G.
    eapply MKT118. appA2H H0; auto. appA2H H4; auto.
    red. intros. rewrite Exp_R_Lim; eauto. appA2G. New H6.
    apply H2 in H6. New H7. apply trans_Ord_Num in H7; auto.
    New (R_Exp_in_R a z H H7). destruct H6.
    exists (a ^ z). split; auto. appA2G.
    TF( z = Φ ). exists (PlusOne Φ). subst z. split. appA2G. appA2G.
    exists Φ. split; auto. rewrite Exp_R_Φ_r; auto.
    rewrite H6. exists (a ^ (PlusOne z)). split.
    rewrite <- H6. rewrite Exp_R_Suc; eauto. rewrite <- H6.
    New (Lem123 _ Φ_is_Ord).
    New (Mult_R_PrOrder_a (PlusOne Φ) a z H11 H H7 H10 H1).
    rewrite Mult_R_PlusOneΦ in H12; eauto.
    appA2G. apply Lem123 in H7. New (R_Exp_in_R a (PlusOne z)); eauto.
    exists (PlusOne z). split. apply Lim_Ord_1; eauto. auto.
Qed.

Lemma R_Exp_3 : forall a b, Ordinal_Number a -> Ordinal_Number b -> (PlusOne Φ) ≺ b
  -> b ^ a ≺ b ^ PlusOne a.
Proof.
  intros. TF( a = Φ ). subst a.
  rewrite Exp_R_Suc, Exp_R_Φ_r, Mult_R_com_PlusOneΦ, Mult_R_Suc,
      Mult_R_Φ_r, Add_R_Φ_l; eauto.
  New (R_Exp_in_R b a H0 H). assert( Φ ∈ PlusOne Φ ). appA2G.
  New (Ord_Num_trans _ _ b H0 H4 H1). New (R_Exp_1 b a H0 H H5 H2).
  New (Mult_R_PlusOneΦ (b ^ a) (R_Exp_in_R b a H0 H)).
  rewrite <- H7. rewrite Exp_R_Suc; auto.
  eapply Mult_R_PrOrder_a; eauto. apply Lem123, Φ_is_Ord.
  red. intros. destruct H6. rewrite H8 in H6. emf. rewrite H8 in H6.
  rewrite H6 in H5. unfold Less in H5. emf.
Qed.

(* 保序(左单调性) *)
Theorem Exp_R_PrOrder_a : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b -> PlusOne Φ ≺ b
  -> ( a1 ≺ a2 -> b ^ a1 ≺ b ^ a2 ).
Proof.
  intros. generalize dependent a2.
  eapply (R_Transfinite_Induction (fun x => a1 ≺ x -> b ^ a1 ≺ b ^ x)); eauto.
  intros a2 H0 H3 H4. TF( a2 = Φ ). subst. unfold Less in H4. emf.
  apply OrdNum_classic in H0 as [].
  + destruct H0,H0. assert(x ∈ a2). subst; appA2G.
    assert( a1 ≼ x ). New (Ord_Num_tri a1 x H H0).
    destruct H8. left; auto. destruct H8. right; auto.
    rewrite H6 in H4. eapply Ord_Num_not_dense in H8; eauto. contradiction.
    destruct H8.
    * eapply Ord_Num_trans; eauto. apply R_Exp_in_R; eauto. rewrite H6.
      eapply Lem123; eauto. subst a2. eapply R_Exp_3; eauto.
    * subst a1 a2. eapply R_Exp_3; eauto.
  + New (R_Exp_in_R b a1 H1 H). New H0. destruct H7 as [H7 _].
    New (R_Exp_3 a1 b H H1 H2).
    assert ( b ^ PlusOne a1 ⊂ b ^ a2 ).
    { red. intros. rewrite Exp_R_Lim; eauto. appA2G.
      exists (b ^ PlusOne a1). split; auto. New (Lem123 _ H).
      New (R_Exp_in_R b (PlusOne a1) H1 H10).
      appA2G. exists (PlusOne a1). split; auto.
      eapply Lim_Ord_1; eauto. }
    unfold Less in *. apply H9 in H8; auto.
Qed.

Theorem Exp_R_PrOrder_b : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b -> PlusOne Φ ≺ b
  -> ( b ^ a1 ≺ b ^ a2 -> a1 ≺ a2 ).
Proof.
  intros. New H. eapply (Ord_Num_tri a1 a2) in H4; eauto.
  destruct H4; auto. destruct H4. subst. NSym.
  eapply Exp_R_PrOrder_a in H4; eauto.
  eapply (Ord_Num_antisym (b ^ a1) (b ^ a2)) in H3;
  try eapply R_Exp_in_R; eauto. contradiction.
Qed.

Theorem Exp_R_PrOrder : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b -> PlusOne Φ ≺ b
  -> ( a1 ≺ a2 <-> b ^ a1 ≺ b ^ a2 ).
Proof.
  intros. split; intros; try eapply Exp_R_PrOrder_a; eauto.
  try eapply Exp_R_PrOrder_b; eauto.
Qed.

Lemma R_Exp_3' : forall a b, Ordinal_Number a -> Ordinal_Number b -> (PlusOne Φ) ≺ b
  -> Φ ≺ b ^ a.
Proof.
  intros. TF( a = Φ ). subst. rewrite Exp_R_Φ_r; eauto. appA2G.
  New (Φ_is_First_Ord _ H H2). eapply Exp_R_PrOrder_a in H3; eauto.
  rewrite Exp_R_Φ_r in H3; auto. assert( Φ ∈ PlusOne Φ ). appA2G.
  eapply Ord_Num_trans; eauto. eapply R_Exp_in_R; eauto. apply Φ_is_Ord.
Qed.

(* 消去 *)
Theorem Exp_R_Cancellation : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b -> PlusOne Φ ≺ b
  -> ( b ^ a1 = b ^ a2 <-> a1 = a2 ).
Proof.
  split; intros.
  - New H. eapply (Ord_Num_tri a1 a2) in H4; eauto.
    try repeat destruct H4; auto. eapply Exp_R_PrOrder_a in H4; eauto.
    rewrite H3 in H4. NSym.
    eapply (Exp_R_PrOrder_a a2 a1) in H4; eauto.
    rewrite H3 in H4. NSym.
  - New H. eapply (Ord_Num_tri a1 a2) in H4; eauto.
    try repeat destruct H4; subst; auto.
Qed.

Lemma R_Exp_4 : forall a b, Ordinal_Number a -> Lim_Ord b -> b <> Φ -> PlusOne Φ ≺ a
  -> Lim_Ord (a ^ b) /\ (a ^ b) <> Φ.
Proof.
  intros. New H0. destruct H3 as [H3 _]. New (R_Exp_in_R a b H H3). split.
  eapply Lim_Ord_1; eauto. intros x H5. rewrite Exp_R_Lim in H5; eauto.
  appA2H H5. rdeHex. appA2H H7. destruct H8 as [b' []]. subst x0.
  New H0. destruct H9 as [H9 _]. New (trans_Ord_Num b b' H9 H8).
  New (R_Exp_in_R a b' H H10). eapply R_Add_1 in H6; eauto. destruct H6.
  - eapply (Exp_R_PrOrder_a _ _ a) in H8; eauto. eapply Ord_Num_trans; eauto.
  - rewrite H6. eapply Exp_R_PrOrder_a; eauto.
  - eapply trans_Ord_Num in H6; eauto.
  - red. intros. assert( Φ ∈ PlusOne Φ ). appA2G.
    New (Ord_Num_trans Φ (PlusOne Φ) a H H6 H2).
    New (R_Exp_1 a b H H3 H7 H1). destruct H8; rewrite H5 in H8. emf.
    rewrite H8 in H7. unfold Less in H7. emf.
Qed.

(* 分配Distributivity *)
Theorem Exp_R_Distri : ∀ a b c,
  Ordinal_Number a -> Ordinal_Number b -> Ordinal_Number c -> PlusOne Φ ≺ a
  -> a ^ (b + c) = a ^ b ⋅ a ^ c.
Proof.
  intros. generalize dependent c. apply R_Transfinite_Induction. intros.
  TF( a0 = Φ ). subst. rewrite Exp_R_Φ_r,Add_R_Φ_r; eauto.
  rewrite Mult_R_PlusOneΦ; eauto. eapply R_Exp_in_R; eauto.
  New H1. apply OrdNum_classic in H5 as [].
  - destruct H5. rdeHex. assert (x ∈ a0). rewrite H6. appA2G.
    New H7. apply H3 in H7. subst a0. New (R_Exp_in_R a b H H0).
    New (R_Exp_in_R a x H H5). New (R_Add_in_R b x H0 H5).
    rewrite Add_R_Suc, Exp_R_Suc, Exp_R_Suc; eauto.
    rewrite <- (Mult_R_Association); eauto. rewrite H7; auto.
  - New (R_Exp_4 a a0 H H5 H4 H2). New (R_Add_5 _ _ H0 H5 H4).
    destruct H6 as [H6 _]. destruct H7.
    New (R_Exp_4 a (b + a0) H H7 H8 H2).
    rewrite Exp_R_Lim; eauto.

    set( A := \{ λ v,∃ u, u ≺ b + a0 /\ v = a ^ u \} ).
    set( B := \{ λ v,∃ u, (b + u ≺ b + a0) /\ v = (a ^ (b + u)) \} ).
    assert( A ⊂ R ).
    { red. intros. appA2H H10. rdeHex.
      eapply trans_Ord_Num in H11; try destruct H7; eauto. New H.
      eapply (R_Exp_in_R a x) in H11; eauto. rewrite H12. auto. }
    assert( Ens_A: Ensemble A ).
    { destruct H7 as [H7 _]. assert( A ⊂ (a ^ (b + a0)) ).
      red. intros. appA2H H11. rdeHex. New (trans_Ord_Num (b + a0) x H7 H12).
      subst z. eapply Exp_R_PrOrder_a; eauto. destruct H9,H9.
      eapply (MKT33 (a ^ (b + a0)) A); eauto. }
    rewrite <- (Sup_R_eq_U A); eauto.

    assert( Sup_R A = Sup_R B ).
    { eapply Sup_R_eq; eauto.
      red; intros. appA2H H11. rdeHex. appA2G.
      intros. New H11. appA2H H11. rdeHex. subst a1.
      set (C := \{ λ v, v ∈ R /\ x ≼ b + v \}).
      assert( ∃ y0, FirstMember y0 E C ).
      { exists (∩ C). eapply Lemma121; eauto. red; intros.
        appA2H H14. destruct H16; auto.
        assert( a0 ∈ C ). appA2G. split; auto. left; auto.
        apply NEexE. exists a0; auto. }
      destruct H14 as [y0 H14].
      assert( y0 ≼ a0 ). destruct H14. appA2H H14. destruct H17.
      New (Ord_Num_tri y0 a0 H17 H1). destruct H19. left; auto.
      destruct H19. right; auto.
      assert( a0 ∈ C ). appA2G; split; auto. left; auto.
      eapply H16 in H20. elim H20. eapply Less_eq_E; auto. destruct H16.
      + New (trans_Ord_Num a0 y0 H1 H16).
        eapply (Add_R_PrOrder_a y0 a0 b) in H16; eauto.
        destruct H7 as [H7 _]. New (trans_Ord_Num (b + a0) (b + y0) H7 H16).
        New (trans_Ord_Num (b + a0) x H7 H13).
        assert( x ≼ b + y0 ).
        { destruct H14. appA2H H14. destruct H21. auto. }
        assert( H'': a ^ (b + y0) ∈ B ).
        { appA2G. New (R_Exp_in_R a (b + y0) H H18). appA2H H21. auto. }
        destruct H20.
        eapply (Exp_R_PrOrder_a x (b + y0) a) in H20; eauto.
        exists(a ^ (b + y0)). split; auto; left; auto.
        exists(a ^ (b + y0)). split; auto. rewrite H20; right; auto.
      + subst y0. destruct H7. New (trans_Ord_Num (b + a0) x H7 H13).
        assert( H'': ∀ v, v ∈ a0 -> b + v ≺ x ).
        { intros. New (trans_Ord_Num a0 v H1 H18).
          New (R_Add_in_R b v H0 H19). TF( v ∈ C ).
          destruct H14. eapply H22 in H21. elim H21.
          eapply Less_eq_E; eauto.
          New (Ord_Num_tri (b + v) x H20 H17). destruct H22; auto.
          assert( v ∈ C ). appA2G. split; auto. destruct H22. right; auto.
          left; auto. contradiction. }
        assert( b + a0 ≼ x ).
        { eapply MKT118; eauto. red in H7,H17. appA2H H7; auto.
          appA2H H17; auto. red; intros.
          rewrite Add_R_Lim in H18; eauto. appA2H H18. rdeHex.
          appA2H H20. rdeHex. New (trans_Ord_Num a0 x1 H1 H21).
          eapply H'' in H21. subst x0. eapply Ord_Num_trans; eauto. }
        destruct H18. New (MKT102 (b + a0) x H18 H13). destruct H19.
        rewrite H18 in H13. NSym. }
    rewrite H11; clear H11.

    assert( B = \{ λ v, ∃u, ((u ≺ a0) /\ (v = (a ^ (b + u)))) \} ).
    { try repeat ( eqext; appA2H H11; rdeHex; appA2G; exists x; split; auto).
      eapply Add_R_PrOrder_b in H12; eauto. destruct H7.
      apply trans_Ord_Num in H12; eauto. apply R_Add_in_R' in H12; eauto.
      eapply (Add_R_PrOrder_a x a0 b); eauto.
      eapply trans_Ord_Num in H12; eauto. }
    rewrite H11; clear H11.

    assert( \{ λ v, ∃u, ((u ≺ a0) /\ (v = (a ^ (b + u)))) \}
          = \{ λ v, ∃u, ((u ≺ a0) /\ (v = (a ^ b ⋅ a ^ u))) \} ).
    { eqext; repeat (appA2H H11; rdeHex; appA2G; exists x; split; auto;
      eapply H3 in H12; eauto; rewrite H13; auto). }
    rewrite H11; clear H11.

    set( A' := \{ λ v,∃ u, u ≺ a ^ a0 /\ v = a ^ b ⋅ u \} ).
    set( B' := \{ λ v,∃ u, (a ^ u ≺ a ^ a0) /\ v = (a ^ b ⋅ a ^ u) \} ).

    assert( B' = \{ λ v, ∃u, ((u ≺ a0) /\ (v = (a ^ b ⋅ a ^ u))) \} ).
    { New (R_Exp_in_R a a0 H H1).
      try repeat ( eqext; appA2H H12; rdeHex; appA2G; exists x; split; auto).
      eapply Exp_R_PrOrder_b in H13; eauto.
      apply trans_Ord_Num in H13; eauto. apply R_Exp_in_R' in H13; eauto.
      eapply Exp_R_PrOrder_a in H13; eauto.
      apply trans_Ord_Num in H13; eauto. }
    rewrite <- H11; clear H11.
    assert( H' : a ^ b <> Φ ).
    { assert( Φ ∈ PlusOne Φ ). appA2G.
      TF( b = Φ ). subst b. rewrite Exp_R_Φ_r; eauto. red. intros.
      rewrite H12 in H11. emf.
      New (Ord_Num_trans Φ (PlusOne Φ) a H H11 H2).
      New (R_Exp_1 a b H H0 H13 H12). red; intros.
      destruct H14; rewrite H15 in H14. emf.
      rewrite H14 in H13. unfold Less in H13. emf. }

    assert( A' ⊂ R ).
    { red. intros. appA2H H11. rdeHex. eapply trans_Ord_Num in H12; eauto. New H.
      New (R_Exp_in_R a b H H0). rewrite H13. eapply R_Mult_in_R; eauto.
      eapply (R_Exp_in_R a a0); eauto. }
    assert( Ens_A': Ensemble A' ).
    { New (R_Exp_in_R a b H H0). New (R_Exp_in_R a a0 H H1).
      assert( A' ⊂ (a ^ b ⋅ a ^ a0) ).
      red. intros. appA2H H14. rdeHex. subst z.
      eapply (Mult_R_PrOrder_a x (a ^ a0)) in H15; eauto.
      eapply trans_Ord_Num; eauto.
      eapply (MKT33 (a ^ b ⋅ a ^ a0) A'); eauto.
      eapply R_Mult_in_R in H13; eauto. }

    assert( Sup_R A' = Sup_R B' ).
    { eapply Sup_R_eq; eauto.
      red; intros. appA2H H12. rdeHex. appA2G.
      intros. New H12. appA2H H12. rdeHex. subst a1.
      set (C' := \{ λ v, v ∈ R /\ x ≼ a ^ v \}).
      assert( a0 ∈ C' ). appA2G; split; auto. left; auto.
      assert( ∃ y0, FirstMember y0 E C' ).
      { exists (∩ C'). eapply Lemma121; eauto. red; intros.
        appA2H H17. rdeHex; auto. apply NEexE. exists a0; auto. }
      destruct H17 as [y0 H17].
      assert( y0 ≼ a0 ). destruct H17. appA2H H17. rdeHex.
      New (Ord_Num_tri y0 a0 H19 H1). destruct H21. left; auto.
      destruct H21. right; auto.
      eapply H18 in H15. elim H15. eapply Less_eq_E; auto. destruct H18.
      + New (trans_Ord_Num a0 y0 H1 H18).
        eapply (Exp_R_PrOrder_a y0 a0 a) in H18; eauto.
        assert( x ≼ a ^ y0 ).
        { destruct H17. appA2H H17. rdeHex. auto. }
        destruct H6 as [H6 _]. New (R_Exp_in_R a b H H0).
        New (trans_Ord_Num (a ^ a0) (a ^ y0) H6 H18).
        assert( H'': (a ^ b ⋅ a ^ y0) ∈ B' ).
        { appA2G. New (R_Mult_in_R (a ^ b) (a ^ y0) H21 H22). appA2H H23. auto. }
        destruct H20. New (trans_Ord_Num (a ^ y0) x H22 H20).
        eapply (Mult_R_PrOrder_a x (a ^ y0) (a ^ b)) in H20; eauto.
        exists(a ^ b ⋅ a ^ y0). split; auto; left; auto.
        exists(a ^ b ⋅ a ^ y0). split; auto. right. rewrite H20. auto.
      + subst y0. destruct H6 as [H6 _].
        New (trans_Ord_Num (a ^ a0) x H6 H14).
        assert( H'': ∀ v, v ∈ a0 -> a ^ v ≺ x ).
        { intros. New (trans_Ord_Num a0 v H1 H19).
          New (R_Exp_in_R a v H H20). TF( v ∈ C' ).
          destruct H17. eapply H23 in H22. elim H22.
          eapply Less_eq_E; eauto.
          New (Ord_Num_tri (a ^ v) x H21 H18). destruct H23; auto.
          assert( v ∈ C' ). appA2G. split; auto. destruct H23. right; auto.
          left; auto. contradiction. }
        assert( a ^ a0 ≼ x ).
        { eapply MKT118; eauto. appA2H H6; auto.
          appA2H H18; auto. red; intros.
          rewrite Exp_R_Lim in H19; eauto. appA2H H19. rdeHex.
          appA2H H21. rdeHex. New (trans_Ord_Num a0 x1 H1 H22).
          eapply H'' in H22. subst x0. eapply Ord_Num_trans; eauto. }
        destruct H19. New (MKT102 (a ^ a0) x H19 H14). destruct H20.
        rewrite H19 in H14. NSym. }
    rewrite <- H12; clear H12. rewrite Sup_R_eq_U; eauto.
    rewrite (Mult_R_Lim _ (a ^ a0)); eauto.
    eapply R_Exp_in_R; eauto. red. intros.
    assert( Φ ∈ PlusOne Φ ). appA2G.
    New (Ord_Num_trans Φ (PlusOne Φ) a H H13 H2).
    New (R_Exp_1 a a0 H H1 H14 H4). destruct H15.
    rewrite H12 in H15. emf. rewrite H12 in H15. rewrite H15 in H14.
    unfold Less in H14. emf.
Qed.

(**********************************************************************)
(* 相关示例 *)

Fact Exp_R_PlusOneΦ_l : forall a, a ∈ R -> PlusOne Φ ^ a = PlusOne Φ.
Proof.
  eapply R_Transfinite_Induction; eauto. intros.
  New (Lem123 _ Φ_is_Ord).
  TF( a = Φ ). subst a. rewrite Exp_R_Φ_r; eauto.
  New H. eapply OrdNum_classic in H3 as [].
  - destruct H3,H3. assert( x ∈ a ). rewrite H4; appA2G.
    apply H0 in H5. subst a. rewrite Exp_R_Suc; eauto.
    rewrite H5, Mult_R_PlusOneΦ; auto.
  - rewrite Exp_R_Lim; eauto. eqext.
    appA2H H4. rdeHex. appA2H H6. rdeHex. apply H0 in H7.
    rewrite H7 in H8. subst x. auto. appA2G.
    exists (PlusOne Φ). split; auto. appA2G.
    exists Φ. split. apply Φ_is_First_Ord; auto.
    rewrite Exp_R_Φ_r; auto.
Qed.

Fact Exp_R_PlusOneΦ_r : forall a, a ∈ R -> a ^ PlusOne Φ = a.
Proof.
  intros. New Φ_is_Ord.
  rewrite Exp_R_Suc,Exp_R_Φ_r,Mult_R_com_PlusOneΦ,Mult_R_PlusOneΦ; eauto.
Qed.

Fact Exp_R_ω : forall a, a ∈ ω -> PlusOne Φ ≺ a -> a ^ ω = ω.
Proof.
  intros. New MKT138. New (trans_Ord_Num ω a H1 H).
  assert( ω <> Φ ). red. intros. New MKT135a. rewrite H3 in H4. emf.
  eapply MKT27. split.
  - red. intros. New ω_is_Lim_Ord. rewrite Exp_R_Lim in H4; eauto.
    appA2H H4. rdeHex. appA2H H7. rdeHex. subst x. destruct H5 as [H5 _].
    New (ω_Exp_in_ω a x0 H H8). New (Ord_Num_trans z (a ^ x0) ω H5 H6 H9).
    unfold Less in H10; auto.
  - New (R_Exp_in_R a ω H2 H1). New (R_Exp_2 a ω H2 H1 H0).
    eapply MKT118; eauto. appA2H H4; auto.
Qed.

(* 交换律不成立 *)

Fact Exp_R_nocom : (PlusOne Φ) ^ ω <> ω ^ (PlusOne Φ).
Proof.
  New MKT138. New Φ_is_Ord. rewrite Exp_R_PlusOneΦ_l,Exp_R_PlusOneΦ_r; eauto.
  red; intros. New MKT135a. eapply Lim_Ord_1 in H2; eauto. rewrite H1 in H2.
  unfold Less in H2. NSym. apply ω_is_Lim_Ord.
Qed.

(* 结合律不成立 *)

Fact Exp_R_noassociation : ω ^ (PlusOne Φ ^ ω) <> (ω ^ PlusOne Φ) ^ ω.
Proof.
  New MKT138. New Φ_is_Ord. rewrite Exp_R_PlusOneΦ_l,Exp_R_PlusOneΦ_r; eauto.
  red; intros. assert( ω ∈ ω ^ ω ).
  { New ω_is_Lim_Ord. New MKT135a.
    assert( ω <> Φ ). red. intros. rewrite H4 in H3. emf.
    rewrite Exp_R_Lim; eauto. appA2G. New H0. apply Lem123 in H5.
    exists (ω ^ (PlusOne (PlusOne Φ))). split.
    rewrite Exp_R_Suc, Exp_R_Suc, Exp_R_Φ_r,
      Mult_R_com_PlusOneΦ, Mult_R_PlusOneΦ; eauto.
    rewrite Mult_R_Lim; auto. appA2G.
    exists (ω + ω). split. rewrite Add_R_Lim; auto. appA2G.
    exists (PlusOne ω). split. appA2G. appA2G.
    exists (PlusOne Φ). split. apply MKT134; auto.
    rewrite Add_R_Suc, Add_R_Φ_r; auto.
    appA2G. New (R_Add_in_R ω ω H H). appA2H H6. auto.
    exists (PlusOne (PlusOne Φ)). split. apply MKT134; auto.
    rewrite Mult_R_Suc; auto. rewrite Mult_R_PlusOneΦ; auto.
    appA2G. apply Lem123 in H5.
    New (R_Exp_in_R ω (PlusOne (PlusOne Φ)) H H5). appA2H H6. auto.
    exists (PlusOne (PlusOne Φ)). split. apply MKT134; auto. auto. }
  rewrite <- H1 in H2. NSym.
Qed.