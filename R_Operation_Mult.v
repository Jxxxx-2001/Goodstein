Require Export OrdinalNum.R_Operation_Add.

(* 乘法 *)

Definition G1_M := \{\ λ u v, u ∈ μ /\ v = Φ \}\.

Definition G2_M a := \{\ λ u v, u ∈ μ /\
  ( ( u ∈ R /\ v = u + a ) \/ ( u ∉ R /\ v = Φ ) ) \}\.

Definition G3_M := \{\ λ u v, u ∈ μ /\
  ( ( Function u /\ v = ∪(ran(u)) ) \/ ( ~ Function u /\ v = Φ ) ) \}\.

Theorem MultFunction_R : ∀ a, a ∈ R -> exists ! F, OnTo F R R
  /\ F[Φ] = Φ
  /\ ∀n, Ordinal_Number n -> F[PlusOne n] = F[n] + a
  /\ ∀n, Ordinal_Number n -> Lim_Ord n -> n ≠ Φ -> F[n] = ∪(ran(F|(n))).
Proof.
  intros.
  assert( F_G1: OnTo G1_M μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0.
    destruct H2. appoA2H H1. destruct H4; subst; auto.
    eqext. eapply MKT19; eauto. appA2G. exists Φ. appoA2G.
    red. intros. eapply MKT19; eauto. }
  assert( F_G2: OnTo (G2_M a) μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0.
    destruct H2 as [_ H2]. appoA2H H1. destruct H3 as [_ H3].
    try repeat (destruct H2,H3; try contradiction; subst; auto).
    eqext. eapply MKT19; eauto. appA2G. TF ( z ∈ R ).
    exists (z + a). appoA2G. eapply MKT49a; eauto.
    eapply R_Add_in_R in H; eauto. exists Φ. appoA2G.
    red. intros. eapply MKT19; eauto. }
  assert( F_G3: OnTo G3_M μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0. destruct H2. appoA2H H1.
    destruct H4,H3,H3. destruct H5. destruct H5; subst; auto.
    destruct H5. contradiction. destruct H5,H5. contradiction. subst; auto.
    eqext. eapply MKT19; eauto. TF ( Function z ). appA2G.
    exists (∪(ran(z))). appoA2G. eapply MKT49a; eauto. apply AxiomVI.
    apply AxiomV; auto. apply fdme; auto.
    appA2G. exists Φ. appoA2G. red. intros. eapply MKT19; eauto. }
  New F_G1. eapply (Recursion_R.Recursion_R G1_M (G2_M a) G3_M) in H0; eauto.
  destruct H0 as [F [H0 H1]]. exists F. split.
  - clear H1. destruct H0,H1.
    assert( H_F: OnTo F R R ).
    destruct H0,H3. repeat (split; auto).
    red. intros. eapply Einr in H5; eauto. destruct H5,H5.
    assert( ( ∀ x, x ∈ R -> F[x] ∈ R ) ).
    { apply R_Transfinite_Induction. intros.
      TF( a0 = Φ ). subst a0.
      assert( G1_M [Φ] = Φ ).
      { eqE. appA2H H9. apply H10. appA2G. appoA2G. }
      rewrite H1,H9. auto.
      New H7. apply OrdNum_classic in H10 as [].
      destruct H10,H10.
      assert( Ensemble F[x0] ).
      { red in H10. rewrite <- H3 in H10. apply Property_dm in H10; auto. }
      New H10. apply H2 in H13 as [H13 _].
      assert( x0 ∈ a0 ). rewrite H11. appA2G. apply H8 in H14.
      assert( (F[x0] + a) ∈ R ). eapply R_Add_in_R in H; eauto.
      assert( (G2_M a) [F[x0]] = F[x0] + a ).
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
      assert( G3_M [F | (a0)] = ∪(ran(F | (a0))) ).
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
    + rewrite H1. eqE. appA2H H3. apply H4. appA2G. appoA2G.
    + intros n H'. pose proof H' as H''. apply H2 in H'. clear H2.
      destruct H'. split.
      * clear H3. rewrite H2. assert( F[n] ∈ R ).
        { destruct H_F,H4. red in H''. rewrite <- H4 in H''.
          apply Property_dm in H''; auto. }
        eqext. appA2H H4. apply H5; clear H5.
        New H3. eapply (R_Add_in_R F[n] a) in H5; eauto.
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
    + rewrite H1. symmetry. eqE. appA2H H3. apply H4. appA2G. appoA2G.
    + intros n H'. pose proof H' as H''. apply H2 in H'. clear H2.
      destruct H'. split.
      * clear H3. symmetry. rewrite H2. assert( H': x'[n] ∈ R ).
        { destruct H0,H3. red in H''. rewrite <- H3 in H''.
          apply Property_dm in H''; auto. }
        eqext. appA2H H3. apply H4; clear H4. New H.
        eapply (R_Add_in_R x'[n] a) in H4; eauto.
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

(* 对于任意a，运算Mult_R *)

Definition Mult_R a b:= ∩(\{ λ u, Ordinal_Number a /\
  (∀ F, OnTo F R R
  -> F[Φ] = Φ
  -> (∀n, Ordinal_Number n -> F[PlusOne n] = F[n] + a)
  -> (∀n, Ordinal_Number n -> Lim_Ord n -> n ≠ Φ -> F[n] = ∪(ran(F|(n))))
  -> u = F[b]) \}).

Notation "a ⋅ b" := (Mult_R a b)(at level 40).

(**********************************************************************)
(* 乘法验证 *)

Theorem Mult_R_Φ_r : forall a,
  Ordinal_Number a -> a ⋅ Φ = Φ.
Proof.
  intros. eqE. New H. apply MultFunction_R in H.
  destruct H as [F [[H' [H _]] _]]. appA2H H0. apply H2; clear H2. appA2G.
Qed.

Theorem Mult_R_Suc : forall a b,
  Ordinal_Number a -> Ordinal_Number b -> a ⋅ (PlusOne b) = (a ⋅ b) + a.
Proof.
  intros. pose proof H as H_a. apply MultFunction_R in H.
  destruct H as [F [H H']].
  assert( E: a ⋅ (PlusOne b)  =  F[PlusOne b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    assert( Ensemble (F[PlusOne b]) ).
    red in H0. apply Lem123 in H0. destruct H,H,H3.
    rewrite <- H3 in H0. eapply Property_dm in H0; eauto.
    appA2G. repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[PlusOne b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite E. assert( E1: a ⋅ b  =  F[b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. red in H0. destruct H,H,H3.
    rewrite <- H3 in H0. eapply Property_dm in H0; eauto.
    repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite E1. destruct H,H1. apply H2 in H0. destruct H0. auto.
Qed.

Theorem Mult_R_Lim : forall a b,
  Ordinal_Number a -> Lim_Ord b -> b ≠ Φ
  -> a ⋅ b = ∪ \{ λ v, ∃ u, u ≺ b /\ v = (a ⋅ u) \}.
Proof.
  intros. pose proof H as H_a. apply MultFunction_R in H.
  destruct H as [F [H H']].
  assert( a ⋅ b  =  F[b] ).
  { destruct H0. eqext. appA2H H3. apply H4.
    clear H4. appA2G. destruct H,H,H5. red in H0. rewrite <- H5 in H0.
    apply MKT69b in H0. auto. repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H4.
    assert( y = F[b] ). eapply H5; eapply H; eauto. rewrite H6; auto. }
  rewrite H2.
  assert( \{ λ v, ∃ u, u ≺ b /\ v = (a ⋅ u) \} = ran(F | (b)) ).
  { pose proof H as H''. destruct H,H,H4. eqext. appA2G. appA2H H6.
    destruct H7,H7. exists x. appA2G.
    assert( a ⋅ x = F[x] ).
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
    assert( a ⋅ x = F[x] ).
    { destruct H0 as [H0 _]. eqext. appA2H H11. apply H12. clear H12.
      assert( Ensemble F[x] ).
      eapply trans_Ord_Num in H9; eauto. red in H9. rewrite <- H4 in H9.
      apply Property_dm in H9; auto. eauto. appA2G.
      eapply trans_Ord_Num in H9; eauto. repeat split; auto. intros.
      assert( F = F0 ). eapply H'; eauto. subst F0. auto.
      appA2H H0; auto. appA2G. intros. appA2H H13.
      assert( y = F[x] ). eapply H14; eapply H''; eauto. rewrite H15; auto. }
    rewrite H11. eapply Property_Fun in H8; eauto. }
  rewrite H3. New H0. destruct H,H0,H5. New H0. apply H7 in H0.
  destruct H0 as [_ H0]. eapply H0 in H8; eauto.
Qed.

Theorem Mult_R_Φ_l : forall a, Ordinal_Number a -> Φ ⋅ a = Φ.
Proof.
  intros. generalize dependent a.
  eapply (R_Transfinite_Induction (fun x => (Φ ⋅ x) = Φ )); eauto.
  intros. TF( a = Φ ). subst. rewrite Mult_R_Φ_r; eauto.
  New H. New Φ_is_Ord. eapply OrdNum_classic in H2 as []; eauto.
  destruct H2,H2. rewrite H4. assert( x ∈ a ). rewrite H4; appA2G.
  eapply H0 in H5; eauto. rewrite Mult_R_Suc; try rewrite H5; eauto.
  rewrite Add_R_Φ_l; eauto. rewrite Mult_R_Lim; eauto.
  eqext. appA2H H4. destruct H5,H5. appA2H H6. destruct H7,H7. New H7.
  eapply H0 in H9. subst x. rewrite H9 in H5. emf. emf.
Qed.

(**********************************************************************)
(* 乘法相关性质 *)

Corollary R_Mult_in_R : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> (a ⋅ b) ∈ R .
Proof.
  intros. pose proof H as H_a. pose proof H0 as H_b.
  apply MultFunction_R in H. destruct H as [F [H H']].
  assert( a ⋅ b  =  F[b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. destruct H,H,H3. red in H0. rewrite <- H3 in H0.
    apply MKT69b in H0. auto. repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite H1. destruct H,H,H3. red in H_b. rewrite <- H3 in H_b.
  eapply Property_dm in H_b; auto.
Qed.

Corollary R_Mult_in_R' : forall a b, Ordinal_Number a -> (a ⋅ b) ∈ R
  -> Ordinal_Number b.
Proof.
  intros. pose proof H as H_a. apply MultFunction_R in H.
  destruct H as [F [H _]]. TF( Ordinal_Number b ); auto.
  assert( a ⋅ b = ∩ \{ λ u, u = μ \} ).
  { unfold Mult_R.
    assert( \{ λ u, Ordinal_Number a /\
          (∀ F0, OnTo F0 R R -> F0 [Φ] = Φ ->
          (∀ n, Ordinal_Number n -> F0 [PlusOne n] = F0 [n] + a ) ->
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

Corollary ω_Mult_in_ω : forall a b, a ∈ ω -> b ∈ ω
  -> (a ⋅ b) ∈ ω .
Proof.
  intros. assert( a ∈ R ). appA2H H. destruct H1. appA2G.
  eapply (ω_Transfinite_Induction (fun x => a ⋅ x ∈ ω )); eauto.
  intros. TF( a0 = Φ ). subst a0. rewrite Mult_R_Φ_r; eauto.
  New (ω_Num_is_Suc_Ord a0 H2 H4). destruct H5,H5.
  assert( x ∈ a0 ). subst a0. appA2G. apply H3 in H7.
  subst a0. rewrite Mult_R_Suc; eauto. eapply (ω_Add_in_ω (a ⋅ x) a); eauto.
Qed.

(* 保序(左单调性) *)
Theorem Mult_R_PrOrder_a : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b -> b <> Φ
  -> ( a1 ≺ a2 -> b ⋅ a1 ≺ b ⋅ a2 ).
Proof.
  intros. generalize dependent a2.
  eapply (R_Transfinite_Induction (fun x => a1 ≺ x -> b ⋅ a1 ≺ b ⋅ x)); eauto.
  intros. TF( a = Φ ). subst. unfold Less in H4. emf.
  apply OrdNum_classic in H0 as [].
  + destruct H0,H0. assert(x ∈ a). subst; appA2G.
    New H. red in H8. New H0. eapply (Ord_Num_tri x a1) in H9; eauto.
    destruct H9. subst a. eapply (Ord_Num_not_dense x a1) in H9; eauto.
    unfold Less in H4. contradiction. destruct H9.
    * subst x. rewrite H6. rewrite Mult_R_Suc; auto.
      eapply R_Add_4; eauto. eapply R_Mult_in_R; eauto.
    * eapply H3 in H7; eauto. rewrite H6.
      rewrite Mult_R_Suc; auto. New (R_Mult_in_R b x H1 H0).
      assert( b ⋅ x ≺ b ⋅ x + b ). eapply R_Add_4; eauto.
      eapply Ord_Num_trans; eauto. eapply R_Add_in_R; eauto.
  + assert( a1 ∈ PlusOne a1 ). appA2G. assert( PlusOne a1 ∈ a ).
    { pose proof H as H'. red in H. New H. apply Lem123 in H7.
      New H0. destruct H8. pose proof H8 as H''.
      eapply (Ord_Num_tri (PlusOne a1) a) in H8; eauto.
      try repeat destruct H8; eauto. elim H9. exists a1; auto.
      eapply (Ord_Num_not_dense a1 a) in H'; eauto. contradiction. }
    New H7. eapply H3 in H7; eauto. rewrite (Mult_R_Lim b a); eauto.
    unfold Less. appA2G. exists (b ⋅ PlusOne a1). split; eauto.
    appA2G. eapply (R_Mult_in_R b (PlusOne a1)) in H1; eauto.
    red in H. apply Lem123 in H. auto.
Qed.

Theorem Mult_R_PrOrder_b : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b -> b <> Φ
  -> ( b ⋅ a1 ≺ b ⋅ a2 -> a1 ≺ a2 ).
Proof.
  intros. New H. eapply (Ord_Num_tri a1 a2) in H4; eauto.
  destruct H4; auto. destruct H4. subst. NSym.
  eapply Mult_R_PrOrder_a in H4; eauto.
  eapply (Ord_Num_antisym (b ⋅ a1) (b ⋅ a2)) in H3;
  try eapply R_Mult_in_R; eauto. contradiction.
Qed.

Theorem Mult_R_PrOrder : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b -> b <> Φ
  -> ( a1 ≺ a2 <-> b ⋅ a1 ≺ b ⋅ a2 ).
Proof.
  intros. split; intros; try eapply Mult_R_PrOrder_a; eauto.
  try eapply Mult_R_PrOrder_b; eauto.
Qed.

(* 消去 *)
Theorem Mult_R_Cancellation : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b -> b <> Φ
  -> ( b ⋅ a1 = b ⋅ a2 <-> a1 = a2 ).
Proof.
  split; intros.
  - New H. eapply (Ord_Num_tri a1 a2) in H4; eauto.
    try repeat destruct H4; auto. eapply Mult_R_PrOrder_a in H4; eauto.
    rewrite H3 in H4. NSym.
    eapply (Mult_R_PrOrder_a a2 a1) in H4; eauto.
    rewrite H3 in H4. NSym.
  - New H. eapply (Ord_Num_tri a1 a2) in H4; eauto.
    try repeat destruct H4; subst; auto.
Qed.

Lemma R_Mult_1 : forall a b, Ordinal_Number a -> Ordinal_Number b -> b <> Φ
  -> a ≼ a ⋅ b.
Proof.
  intros. generalize dependent b.
  eapply (R_Transfinite_Induction (fun x => x <> Φ -> a ≼ a ⋅ x)); eauto.
  intros. TF( a = Φ ). subst. rewrite Mult_R_Φ_l; eauto. right; auto.
  New H0. eapply OrdNum_classic in H4 as [].
  - New H4. destruct H5,H5.
    rewrite H6. rewrite Mult_R_Suc; eauto.
    assert( x ∈ a0 ). rewrite H6. appA2G.
    TF( x = Φ ). subst. rewrite Mult_R_Φ_r; auto. rewrite Add_R_Φ_l; auto.
    right. auto. apply H1 in H7; auto. New (R_Mult_in_R a x H H5).
    destruct H7. assert( (a ⋅ x) ∈ ((a ⋅ x) + a) ). eapply R_Add_4; eauto.
    left. eapply Ord_Num_trans; eauto. eapply R_Add_in_R; eauto.
    rewrite <- H7. left. apply R_Add_4; eauto.
  - eapply MKT118. appA2H H; auto. New H4. destruct H4 as [H4 _].
    New( R_Mult_in_R a a0 H H4 ). appA2H H6; auto.
    red. intros. rewrite Mult_R_Lim; eauto. appA2G.
    exists a. split; auto. appA2G.
    exists (PlusOne Φ). split. New H4. destruct H6 as [H6 _].
    New (Φ_is_First_Ord a0 H6 H2).
    eapply Lim_Ord_1 in H7; eauto.
    rewrite Mult_R_Suc; auto. rewrite Mult_R_Φ_r,Add_R_Φ_l; eauto.
    eapply Φ_is_Ord; auto.
Qed.

Lemma R_Mult_2 : forall a b, Ordinal_Number a -> Ordinal_Number b -> a <> Φ
  -> b ≼ a ⋅ b.
Proof.
  intros. generalize dependent b.
  eapply (R_Transfinite_Induction (fun x => x ≼ a ⋅ x)); eauto.
  intros. New H0. eapply OrdNum_classic in H3 as [].
  - New H3. destruct H3,H3.
    assert( x ∈ a0 ). rewrite H5; appA2G. New H6. apply H2 in H6.
    assert( x ∈ a ⋅ a0 ). rewrite H5. rewrite Mult_R_Suc; eauto.
    New (R_Mult_in_R a x H H3).
    assert( (a ⋅ x) ∈ (a ⋅ x + a) ). eapply R_Add_4; eauto.
    destruct H6. rewrite Add_Union; eauto. appA2G.
    rewrite <- H6. eapply R_Add_4; eauto.
    eapply R_Add_1 in H8; eauto. rewrite <- H5 in H8; auto.
    eapply R_Mult_in_R; eauto.
  - TF( a0 = Φ ). subst. right; rewrite Mult_R_Φ_r; auto.
    eapply MKT118. appA2H H0; auto.
    New( R_Mult_in_R a a0 H H0). appA2H H5; auto.
    red. intros. New H5. eapply H2 in H5. destruct H5.
    New( trans_Ord_Num a0 z H0 H6 ).
    eapply (Mult_R_PrOrder_a z a0 a) in H6; eauto.
    New( R_Mult_in_R a a0 H H0).
    New (Ord_Num_trans z (a ⋅ z) (a ⋅ a0) H8 H5 H6). auto.
    rewrite H5. eapply Mult_R_PrOrder_a; eauto.
    eapply trans_Ord_Num; eauto.
Qed.

Lemma R_Mult_3 : forall a b, Ordinal_Number a -> Lim_Ord b -> a ≠ Φ
  -> Lim_Ord (a ⋅ b).
Proof.
  intros. TF( b = Φ ). subst. rewrite Mult_R_Φ_r; eauto.
  New H0. destruct H3 as [H' _]. New (R_Mult_in_R a b H H').
  eapply Lim_Ord_1; eauto. intros. rewrite Mult_R_Lim in H4; eauto.
  appA2H H4. destruct H5,H5. appA2H H6. destruct H7,H7. subst x.
  New H7. apply trans_Ord_Num in H8; auto. New (R_Mult_in_R a x0 H H8).
  eapply R_Add_1 in H5; eauto. eapply (Mult_R_PrOrder_a x0 b a) in H7; eauto.
  destruct H5. try eapply Ord_Num_trans; eauto. rewrite H5; auto.
  eapply trans_Ord_Num; eauto.
Qed.

(* 分配Distributivity *)
Theorem Mult_R_Distri : ∀ a b c,
  Ordinal_Number a -> Ordinal_Number b -> Ordinal_Number c ->
  a ⋅ (b + c) = a ⋅ b + a ⋅ c.
Proof.
  intros. TF( a = Φ ). subst. New (R_Add_in_R b c H0 H1).
  rewrite Mult_R_Φ_l,Mult_R_Φ_l,Mult_R_Φ_l,Add_R_Φ_l; eauto.
  generalize dependent c. apply R_Transfinite_Induction. intro c.
  intros. TF( c = Φ ).
  subst. rewrite Mult_R_Φ_r,Add_R_Φ_r,Add_R_Φ_r; eauto.
  eapply R_Mult_in_R; eauto.
  New H1. apply OrdNum_classic in H5 as [].
  - destruct H5,H5. rewrite H6. rewrite Add_R_Suc,Mult_R_Suc; auto.
    assert( x ∈ c ). rewrite H6. appA2G. New H7. apply H3 in H7. rewrite H7.
    rewrite Add_R_Association,Mult_R_Suc; eauto. apply R_Mult_in_R; auto.
    apply trans_Ord_Num in H8; auto. apply R_Mult_in_R; auto.
    apply R_Add_in_R; auto.
  - New (R_Add_5 b c H0 H5 H4). destruct H6 as [H6 H6'].
    rewrite Mult_R_Lim; eauto.
    set( A := \{ λ v,∃ u, u ≺ b + c /\ v = a ⋅ u \} ).
    set( B := \{ λ v,∃ u, (b + u ≺ b + c) /\ v = (a ⋅ (b + u)) \} ).
    assert( A ⊂ R ).
    { red. intros. appA2H H7. destruct H8,H8.
      eapply trans_Ord_Num in H8; eauto. New H.
      eapply (R_Mult_in_R a x) in H10; eauto. rewrite <- H9 in H10. auto.
      eapply (R_Add_in_R b c); eauto. }
    assert( Ens_A: Ensemble A ).
    { destruct H6 as [H6 _]. assert( A ⊂ (a ⋅ (b + c)) ).
      red. intros. appA2H H8. rdeHex. New (trans_Ord_Num (b + c) x H6 H9).
      subst z. eapply Mult_R_PrOrder_a; eauto.
      New (R_Mult_in_R a (b + c) H H6).
      eapply (MKT33 (a ⋅ (b + c)) A); eauto. }
    rewrite <- (Sup_R_eq_U A); eauto.

    assert( Sup_R A = Sup_R B ).
    { eapply Sup_R_eq; eauto.
      red; intros. appA2H H8. destruct H9,H9. appA2G.
      intros. New H8. appA2H H8. rdeHex. subst a0.
      set (C := \{ λ v, v ∈ R /\ x ≼ b + v \}).
      assert( ∃ y0, FirstMember y0 E C ).
      { exists (∩ C). eapply Lemma121; eauto. red; intros.
        appA2H H11. destruct H12; auto.
        assert( c ∈ C ). appA2G. split; auto. left; auto.
        apply NEexE. exists c; auto. }
      destruct H11 as [y0 H11].
      assert( y0 ≼ c ). destruct H11. appA2H H11. destruct H13. destruct H5.
      New (Ord_Num_tri y0 c H13 H5). destruct H16. left; auto.
      destruct H16. right; auto.
      assert( c ∈ C ). appA2G; split; auto. left; auto.
      eapply H12 in H17. elim H17. eapply Less_eq_E; auto. destruct H12.
      + New (trans_Ord_Num c y0 H1 H12).
        eapply (Add_R_PrOrder_a y0 c b) in H12; eauto.
        destruct H6 as [H6 _]. New (trans_Ord_Num (b + c) (b + y0) H6 H12).
        New (trans_Ord_Num (b + c) x H6 H10).
        assert( x ≼ b + y0 ).
        { destruct H11. appA2H H11. destruct H17. auto. }
        assert( H'': a ⋅ (b + y0) ∈ B ).
        { appA2G. New (R_Mult_in_R a (b + y0) H H14). appA2H H17. auto. }
        destruct H16.
        eapply (Mult_R_PrOrder_a x (b + y0) a) in H16; eauto.
        exists(a ⋅ (b + y0)). split; auto; left; auto.
        exists(a ⋅ (b + y0)). split; auto.
        right; eapply (Mult_R_Cancellation); auto.
      + subst y0. destruct H6. New (trans_Ord_Num (b + c) x H6 H10).
        assert( H'': ∀ v, v ∈ c -> b + v ≺ x ).
        { intros. New (trans_Ord_Num c v H1 H14).
          New (R_Add_in_R b v H0 H15). TF( v ∈ C ).
          destruct H11. eapply H18 in H17. elim H17.
          eapply Less_eq_E; eauto.
          New (Ord_Num_tri (b + v) x H16 H13). destruct H18; auto.
          assert( v ∈ C ). appA2G. split; auto. destruct H18. right; auto.
          left; auto. contradiction. }
        assert( b + c ≼ x ).
        { eapply MKT118; eauto. red in H6,H13. appA2H H6; auto.
          appA2H H13; auto. red; intros.
          rewrite Add_R_Lim in H14; eauto. appA2H H14. rdeHex.
          appA2H H16. rdeHex. New (trans_Ord_Num c x1 H1 H17).
          eapply H'' in H17. subst x0. eapply Ord_Num_trans; eauto. }
        destruct H14. New (MKT102 (b + c) x H14 H10). destruct H15.
        rewrite H14 in H10. NSym. }
    rewrite H8; clear H8.

    assert( B = \{ λ v, ∃u, ((u ≺ c) /\ (v = (a ⋅ (b + u)))) \} ).
    { try repeat ( eqext; appA2H H8; rdeHex; appA2G; exists x; split; auto).
      eapply Add_R_PrOrder_b in H9; eauto. destruct H6.
      apply trans_Ord_Num in H9; eauto. apply R_Add_in_R' in H9; eauto.
      eapply (Add_R_PrOrder_a x c b); eauto.
      eapply trans_Ord_Num in H9; eauto. }
    rewrite H8; clear H8.

    assert( \{ λ v, ∃u, ((u ≺ c) /\ (v = (a ⋅ (b + u)))) \}
          = \{ λ v, ∃u, ((u ≺ c) /\ (v = (a ⋅ b + a ⋅ u))) \} ).
    { eqext; repeat (appA2H H8; rdeHex; appA2G; exists x; split; auto;
      eapply H3 in H9; eauto; rewrite H10; auto). }
    rewrite H8; clear H8.

    set( A' := \{ λ v,∃ u, u ≺ a ⋅ c /\ v = a ⋅ b + u \} ).
    set( B' := \{ λ v,∃ u, (a ⋅ u ≺ a ⋅ c) /\ v = (a ⋅ b + a ⋅ u) \} ).

    assert( B' = \{ λ v, ∃u, ((u ≺ c) /\ (v = (a ⋅ b + a ⋅ u))) \} ).
    { New (R_Mult_in_R a c H H1).
      try repeat ( eqext; appA2H H9; rdeHex; appA2G; exists x; split; auto).
      eapply Mult_R_PrOrder_b in H10; eauto.
      apply trans_Ord_Num in H10; eauto. apply R_Mult_in_R' in H10; eauto.
      eapply Mult_R_PrOrder_a in H10; eauto.
      apply trans_Ord_Num in H10; eauto. }
    rewrite <- H8; clear H8.

    assert( A' ⊂ R ).
    { red. intros. appA2H H8. rdeHex. eapply trans_Ord_Num in H9; eauto. New H.
      eapply (R_Mult_in_R a b) in H11; eauto. rewrite H10.
      eapply (R_Add_in_R (a ⋅ b) x) in H11; eauto.
      eapply (R_Mult_in_R a c); eauto. }
    assert( Ens_A': Ensemble A' ).
    { New (R_Mult_in_R a b H H0). New (R_Mult_in_R a c H H1).
      assert( A' ⊂ (a ⋅ b + a ⋅ c) ).
      red. intros. appA2H H11. rdeHex. subst z.
      eapply (Add_R_PrOrder_a x (a ⋅ c)) in H12; eauto.
      eapply trans_Ord_Num; eauto.
      eapply (MKT33 (a ⋅ b + a ⋅ c) A'); eauto.
      eapply R_Add_in_R in H10; eauto. }

    assert( Sup_R A' = Sup_R B' ).
    { eapply Sup_R_eq; eauto.
      red; intros. appA2H H9. rdeHex. appA2G.
      intros. New H9. appA2H H9. rdeHex. subst a0.
      set (C' := \{ λ v, v ∈ R /\ x ≼ a ⋅ v \}).
      assert( c ∈ C' ). appA2G; split; auto. left; auto.
      assert( ∃ y0, FirstMember y0 E C' ).
      { exists (∩ C'). eapply Lemma121; eauto. red; intros.
        appA2H H13. rdeHex; auto. apply NEexE. exists c; auto. }
      destruct H13 as [y0 H13].
      assert( y0 ≼ c ). destruct H13. appA2H H13. rdeHex.
      New (Ord_Num_tri y0 c H15 H1). destruct H17. left; auto.
      destruct H17. right; auto.
      eapply H14 in H12. elim H12. eapply Less_eq_E; auto. destruct H14.
      + New (trans_Ord_Num c y0 H1 H14).
        eapply (Mult_R_PrOrder_a y0 c a) in H14; eauto.
        assert( x ≼ a ⋅ y0 ).
        { destruct H13. appA2H H13. rdeHex. auto. }
        New (R_Mult_in_R a c H H1). New (R_Mult_in_R a b H H0).
        New (trans_Ord_Num (a ⋅ c) (a ⋅ y0) H17 H14).
        assert( H'': (a ⋅ b + a ⋅ y0) ∈ B' ).
        { appA2G. New (R_Add_in_R (a ⋅ b) (a ⋅ y0) H18 H19). appA2H H20. auto. }
        destruct H16. New (trans_Ord_Num (a ⋅ y0) x H19 H16).
        eapply (Add_R_PrOrder_a x (a ⋅ y0) (a ⋅ b)) in H16; eauto.
        exists(a ⋅ b + a ⋅ y0). split; auto; left; auto.
        exists(a ⋅ b + a ⋅ y0). split; auto. right. rewrite H16. auto.
      + subst y0. New (R_Mult_in_R a c H H1).
        New (trans_Ord_Num (a ⋅ c) x H14 H11).
        assert( H'': ∀ v, v ∈ c -> a ⋅ v ≺ x ).
        { intros. New (trans_Ord_Num c v H1 H16).
          New (R_Mult_in_R a v H H17). TF( v ∈ C' ).
          destruct H13. eapply H20 in H19. elim H19.
          eapply Less_eq_E; eauto.
          New (Ord_Num_tri (a ⋅ v) x H18 H15). destruct H20; auto.
          assert( v ∈ C' ). appA2G. split; auto. destruct H20. right; auto.
          left; auto. contradiction. }
        assert( a ⋅ c ≼ x ).
        { eapply MKT118; eauto. appA2H H14; auto.
          appA2H H15; auto. red; intros.
          rewrite Mult_R_Lim in H16; eauto. appA2H H16. rdeHex.
          appA2H H18. rdeHex. New (trans_Ord_Num c x1 H1 H19).
          eapply H'' in H19. subst x0. eapply Ord_Num_trans; eauto. }
        destruct H16. New (MKT102 (a ⋅ c) x H16 H11). destruct H17.
        rewrite H16 in H11. NSym. }
    rewrite <- H9; clear H9. rewrite Sup_R_eq_U; eauto.
    New (R_Mult_3 a c H H5 H2). rewrite (Add_R_Lim _ (a ⋅ c)); eauto.
    eapply R_Mult_in_R; eauto. red. intros. New (R_Mult_1 a c H H1 H4).
    destruct H11. rewrite H10 in H11. emf. rewrite H10 in H11. contradiction.
Qed.

(* 结合 *)
Theorem Mult_R_Association : ∀ a b c, a ∈ R -> b ∈ R -> c ∈ R
  -> (a ⋅ b) ⋅ c = a ⋅ (b ⋅ c).
Proof.
  intros. TF( b = Φ ). subst. rewrite Mult_R_Φ_r,Mult_R_Φ_l,Mult_R_Φ_r; eauto.
  generalize dependent c. apply R_Transfinite_Induction. intros. TF( a0 = Φ ).
  subst. rewrite Mult_R_Φ_r,Mult_R_Φ_r,Mult_R_Φ_r; eauto.
  eapply R_Mult_in_R; eauto.
  New H1. apply OrdNum_classic in H5 as [].
  - destruct H5,H5. rewrite H6. New (R_Mult_in_R a b H H0).
    rewrite Mult_R_Suc; auto. assert( x ∈ a0 ). rewrite H6. appA2G.
    New H8. apply H3 in H9. rewrite H9. rewrite <- Mult_R_Distri; auto.
    rewrite Mult_R_Suc; auto. apply R_Mult_in_R; auto.
  - New (R_Mult_3 b a0 H0 H5 H2). New (R_Mult_in_R a b H H0). TF( a = Φ ).
    rewrite H8. repeat rewrite Mult_R_Φ_l; eauto. eapply R_Mult_in_R; eauto.
    assert( Lim_Ord ((a ⋅ b) ⋅ a0) ).
    { eapply R_Mult_3; eauto. red. intros. New (R_Mult_1 a b H H0 H2).
      destruct H10. rewrite H9 in H10. emf. rewrite H9 in H10. contradiction. }
    assert( Lim_Ord (a ⋅ (b ⋅ a0)) ). eapply R_Mult_3; eauto.
    rewrite Mult_R_Lim; eauto.

    assert( \{ λ v, ∃u, ((u ≺ a0) /\ (v = (((a ⋅ b) ⋅ u)))) \}
          = \{ λ v, ∃u, ((u ≺ a0) /\ (v = (a ⋅ (b ⋅ u)))) \}  ).
    { try repeat (eqext; appA2H H11; rdeHex; appA2G; exists x; split; auto;
      apply H3 in H12; subst z; auto). }
    rewrite H11; clear H11.

    assert( \{ λ v, ∃u, ((u ≺ a0) /\ (v = (a ⋅ (b ⋅ u)))) \}
          = \{ λ v, ∃u, ((b ⋅ u ≺ b ⋅ a0) /\ (v = (a ⋅ (b ⋅ u)))) \}  ).
    { try repeat (eqext; appA2H H11; rdeHex; appA2G; exists x; split; auto).
      New H12. eapply trans_Ord_Num in H12; eauto;
      eapply (Mult_R_PrOrder_a x a0 b) in H14; eauto.
      New (R_Mult_in_R b a0 H0 H1); New H12; eapply trans_Ord_Num in H12; eauto.
      eapply R_Mult_in_R' in H12; eauto.
      eapply (Mult_R_PrOrder_b x a0 b) in H15; eauto. }
    rewrite H11; clear H11.

    set (A := \{ λ v,∃ u, u ≺ b ⋅ a0 /\ v = a ⋅ u \}).
    set (B := \{ λ v,∃ u, (b ⋅ u ≺ b ⋅ a0) /\ (v = (a ⋅ (b ⋅ u))) \}).
    assert( B ⊂ R ).
    { red. intros. appA2H H11. rdeHex. destruct H6.
      eapply trans_Ord_Num in H12; eauto. subst z.
      eapply (R_Mult_in_R a (b ⋅ x)); eauto. }
    assert( Ens_B: Ensemble B ).
    { destruct H6 as [H6 _]. assert( B ⊂ (a ⋅ (b ⋅ a0)) ).
      red. intros. appA2H H12. rdeHex.
      subst z. New H13. eapply trans_Ord_Num in H13; eauto.
      eapply Mult_R_PrOrder_a; eauto.
      New (R_Mult_in_R a (b ⋅ a0) H H6).
      eapply (MKT33 (a ⋅ (b ⋅ a0)) B); eauto. }
    rewrite <- Sup_R_eq_U; eauto.
    assert( A ⊂ R ).
    { red. intros. appA2H H12. rdeHex. destruct H6.
      eapply trans_Ord_Num in H13; eauto. subst z.
      eapply (R_Mult_in_R a x); eauto. }
    assert( Sup_R A = Sup_R B ).
    { eapply Sup_R_eq; eauto.
      red; intros. appA2H H13. rdeHex. appA2G.
      intros. New H13. appA2H H13. rdeHex. subst a1.
      set (C := \{ λ v, v ∈ R /\ x ≼ b ⋅ v \}).
      assert( ∃ y0, FirstMember y0 E C ).
      { exists (∩ C). eapply Lemma121; eauto. red; intros.
        appA2H H16. destruct H17; auto.
        assert( a0 ∈ C ). appA2G. split; auto. left; auto.
        apply NEexE. exists a0; auto. }
      destruct H16 as [y0 H16].
      assert( y0 ≼ a0 ). destruct H16. appA2H H16. rdeHex.
      New (Ord_Num_tri y0 a0 H18 H1). destruct H20. left; auto.
      destruct H20. right; auto.
      assert( a0 ∈ C ). appA2G; split; auto. left; auto.
      eapply H17 in H21. elim H21. eapply Less_eq_E; auto. destruct H17.
      + New (trans_Ord_Num a0 y0 H1 H17).
        eapply (Mult_R_PrOrder_a y0 a0 b) in H17; eauto.
        destruct H6 as [H6 _]. New (trans_Ord_Num (b ⋅ a0) (b ⋅ y0) H6 H17).
        New (trans_Ord_Num (b ⋅ a0) x H6 H15).
        assert( x ≼ b ⋅ y0 ).
        { destruct H16. appA2H H16. destruct H22. auto. }
        assert( H'': a ⋅ (b ⋅ y0) ∈ B ).
        { appA2G. New (R_Mult_in_R a (b ⋅ y0) H H19). appA2H H22. auto. }
        destruct H21. eapply (Mult_R_PrOrder_a x (b ⋅ y0) a) in H21; eauto.
        exists(a ⋅ (b ⋅ y0)). split; auto; left; auto.
        exists(a ⋅ (b ⋅ y0)). split; auto.
        right; eapply (Mult_R_Cancellation); auto.
      + subst y0. destruct H6. New (trans_Ord_Num (b ⋅ a0) x H6 H15).
        assert( H'': ∀ v, v ∈ a0 -> b ⋅ v ≺ x ).
        { intros. New (trans_Ord_Num a0 v H1 H19).
          New (R_Mult_in_R b v H0 H20). TF( v ∈ C ).
          destruct H16. eapply H23 in H22. elim H22. eapply Less_eq_E; eauto.
          New (Ord_Num_tri (b ⋅ v) x H21 H18). destruct H23; auto.
          assert( v ∈ C ). appA2G. split; auto. destruct H23. right; auto.
          left; auto. contradiction. }
        assert( b ⋅ a0 ≼ x ).
        { eapply MKT118; eauto. appA2H H6; auto. appA2H H18; auto. red; intros.
          rewrite Mult_R_Lim in H19; eauto. appA2H H19. rdeHex.
          appA2H H21. rdeHex. New (trans_Ord_Num a0 x1 H1 H22).
          eapply H'' in H22. subst x0. eapply Ord_Num_trans; eauto. }
        destruct H19. New (MKT102 (b ⋅ a0) x H19 H15). destruct H20.
        rewrite H19 in H15. NSym. }
    rewrite <- H13; clear H13.
    assert( Ens_A : Ensemble A ).
    { destruct H6 as [H6 _]. assert( A ⊂ (a ⋅ (b ⋅ a0)) ).
      red. intros. appA2H H13. rdeHex.
      subst z. New H14. eapply trans_Ord_Num in H14; eauto.
      eapply Mult_R_PrOrder_a; eauto. New (R_Mult_in_R a (b ⋅ a0) H H6).
      eapply (MKT33 (a ⋅ (b ⋅ a0)) A); eauto. }
    rewrite Sup_R_eq_U; eauto. rewrite Mult_R_Lim; eauto.
    red. intros. New (R_Mult_1 b a0 H0 H1 H4).
    destruct H14; rewrite H13 in H14. emf. contradiction.
Qed.

Theorem Mult_Union : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> a ⋅ b = \{ λ v, ∃ u w, u ≺ b /\ w ≺ a /\ v = (a ⋅ u + w) \}.
Proof.
  intros. generalize dependent b.
  eapply (R_Transfinite_Induction); eauto. intros.
  TF( a0 = Φ ). subst. rewrite Mult_R_Φ_r; eauto.
  assert( \{ λ v, ∃ u w, u ≺ Φ /\ w ≺ a /\ v = (a ⋅ u + w) \} = Φ ).
  { eqE. appA2H H2. destruct H3,H3,H3. red in H3. emf. }
  rewrite H2. auto. New H0. eapply OrdNum_classic in H3 as [].
  - destruct H3,H3. rewrite H4. rewrite Mult_R_Suc; eauto.
    unfold PlusOne. assert( x ∈ a0 ). rewrite H4. appA2G.
    eqext. appA2G.
    rewrite Add_Union in H6; eauto. appA2H H6.
    destruct H7. apply H1 in H5. rewrite H5 in H7.
    appA2H H7. destruct H8,H8. exists x0,x1. rdeHex.
    split; auto. appA2G.
    appA2H H7. destruct H8,H8. exists x,x0. split; auto. appA2G.
    eapply R_Mult_in_R; eauto.
    appA2H H6. rdeHex. appA2H H7. destruct H10.
    + New H10. eapply trans_Ord_Num in H11; eauto.
      eapply R_Add_1 in H10; eauto.
      assert( z ∈ a ⋅ PlusOne x0 ). rewrite Mult_R_Suc,H9; eauto.
      eapply Add_R_PrOrder_a; eauto. eapply (trans_Ord_Num a); eauto.
      eapply R_Mult_in_R; eauto. eapply Ord_Num_trans; eauto.
      eapply R_Add_in_R; try eapply R_Mult_in_R; eauto.
      TF( a = Φ ). subst a. red in H8. emf.
      assert( a ⋅ x ≺ a ⋅ x + a ).
      New (Φ_is_First_Ord a H H13); eauto.
      eapply (Add_R_PrOrder_a _ _ (a ⋅ x)) in H14; eauto.
      rewrite(Add_R_Φ_r (a ⋅ x)) in H14; eauto. eapply R_Mult_in_R; eauto.
      eapply Φ_is_Ord; eauto. eapply R_Mult_in_R; eauto.
      destruct H10. assert( Ordinal_Number (PlusOne x0) ).
      eapply (trans_Ord_Num x); eauto.
      assert( a ⋅ PlusOne x0 ≺ a ⋅ x ). eapply Mult_R_PrOrder_a; eauto.
      eapply Ord_Num_trans; eauto.
      eapply R_Add_in_R; try eapply R_Mult_in_R; eauto.
      rewrite H10. auto.
    + appA2H H10. New H3. appA2H H12. eapply MKT19 in H12.
      apply H11 in H12. subst x0. subst z.
      eapply Add_R_PrOrder_a; eauto. eapply (trans_Ord_Num a x1); eauto.
      eapply R_Mult_in_R; eauto.
  - rewrite Mult_R_Lim; auto.
    eqext. appA2H H4. destruct H5,H5. appA2H H6. destruct H7,H7.
    appA2G. subst x. New H7. apply H1 in H7. rewrite H7 in H5. appA2H H5.
    rdeHex. exists x,x1. split; auto. eapply Ord_Num_trans; eauto.
    appA2H H4. rdeHex. appA2G.
    New H5. eapply trans_Ord_Num in H8; eauto.
    apply Lim_Ord_1 in H5; eauto. New H5. eapply H1 in H5.
    exists (a ⋅ PlusOne x). split.
    rewrite Mult_R_Suc; eauto. rewrite H7.
    eapply Add_R_PrOrder_a; eauto. eapply (trans_Ord_Num a); eauto.
    eapply R_Mult_in_R; eauto.
    appA2G. exists R. eapply R_Mult_in_R, (trans_Ord_Num a0); eauto.
Qed.

Lemma Mult_Union' : ∀ a b c d, Ordinal_Number a -> Ordinal_Number d -> b ≺ d
  -> c ≺ a -> a ⋅ b + c ≺ a ⋅ d.
Proof.
  intros. New (trans_Ord_Num d b H0 H1). New (trans_Ord_Num a c H H2).
  rewrite (Mult_Union a d); eauto. appA2G. exists R.
  eapply R_Add_in_R; try eapply R_Mult_in_R; eauto.
Qed.

Theorem Mult_R_PrOrder_c : ∀ a b,
  Ordinal_Number a -> Ordinal_Number b -> PlusOne Φ ≼ a -> a ≺ b ->
   exists! c, c ∈ (R × R) /\ Second c ≺ a /\ b = a ⋅ (First c) + (Second c).
Proof.
  intros. New (Mult_Union a b H H0).
  assert( a <> Φ ). red. intros. subst a. destruct H1. emf.
  assert( Φ ∈ PlusOne Φ ). appA2G. rewrite H1 in H4. emf.
  New (R_Mult_2 a b H H0 H4). New (R_Mult_in_R a b H H0).
  destruct H5.
  - rewrite H3 in H5. appA2H H5. rdeHex.
    New (trans_Ord_Num b x H0 H7). New (trans_Ord_Num a x0 H H8).
    exists [x,x0]. split.
    + split. appA2G. eapply MKT49a; eauto.
      rewrite MKT54a,MKT54b; eauto; ope.
    + intros. rdeHex. appA2H H12. rdeHex. subst x'.
      eapply MKT55; eauto. rewrite MKT54a, MKT54b in H14; eauto.
      rewrite (MKT54b x1 x2) in H13; eauto.
      assert( x = x1 ).
      { New (Ord_Num_tri x x1 H10 H16).
        destruct H15. New (Mult_Union' a x x0 x1 H H16 H15 H8).
        assert( a ⋅ x1 ≼ a ⋅ x1 + x2 ).
        { eapply R_Add_3'; eauto. eapply R_Mult_in_R; eauto. }
        rewrite <- H14 in H19. rewrite <- H9 in H18. destruct H19.
        eapply Ord_Num_trans in H19; eauto. NSym.
        rewrite H19 in H18. NSym.
        destruct H15; auto.
        New (Mult_Union' a x1 x2 x H H10 H15 H13).
        assert( a ⋅ x ≼ a ⋅ x + x0 ).
        { eapply R_Add_3'; eauto. eapply R_Mult_in_R; eauto. }
        rewrite <- H14 in H18. rewrite <- H9 in H19. destruct H19.
        eapply Ord_Num_trans in H19; eauto. NSym.
        rewrite H19 in H18. NSym. }
      split; auto. subst b. eapply (Mult_R_Cancellation x x1 a) in H15; eauto.
      rewrite H15 in H14. eapply (Add_R_Cancellation x0 x2 (a ⋅ x1)); eauto.
      eapply R_Mult_in_R; eauto.
  - exists [b,Φ]. split.
    + split. appA2G. exists b,Φ. try repeat split; auto.
      apply Φ_is_Ord. appA2H H0. rewrite MKT54a,MKT54b; auto; ope.
      split. eapply Φ_is_First_Ord; eauto. rewrite Add_R_Φ_r; auto.
    + intros. rdeHex. appA2H H7. rdeHex. subst x'.
      eapply MKT55; eauto. rewrite MKT54a, MKT54b in H9; eauto.
      rewrite (MKT54b x x0) in H8; eauto.
      assert( b = x ).
      { New (Ord_Num_tri b x H0 H11).
        destruct H10. apply (Mult_R_PrOrder_a _ _ a) in H10; auto.
        assert( a ⋅ x ≼ a ⋅ x + x0 ).
        { eapply R_Add_3'; eauto. eapply R_Mult_in_R; eauto. }
        rewrite <- H5 in H10. rewrite <- H9 in H13. destruct H13.
        eapply Ord_Num_trans in H13; eauto. NSym.
        rewrite H13 in H10. NSym. destruct H10; auto.
        New (Mult_Union' a x x0 b H H0 H10 H8). rewrite <- H5,H9 in H13.
        NSym. }
      split; auto. rewrite H5 in H9.
      rewrite <- (Add_R_Φ_r (a ⋅ b)) in H9. rewrite H10 in H9.
      eapply (Add_R_Cancellation Φ x0) in H9; eauto.
      apply Φ_is_Ord. eapply R_Mult_in_R; eauto.
      eapply R_Mult_in_R; eauto.
Qed.

(**********************************************************************)
(* 相关示例 *)

Fact Mult_R_PlusOneΦ : forall a,
  Ordinal_Number a -> a ⋅ (PlusOne Φ) = a.
Proof.
  intros. New Φ_is_Ord.
  rewrite Mult_R_Suc, Mult_R_Φ_r, Add_R_Φ_l; eauto.
Qed.

Fact Mult_R_com_PlusOneΦ : ∀ a, Ordinal_Number a -> (PlusOne Φ) ⋅ a = a ⋅ (PlusOne Φ).
Proof.
  intros. New Φ_is_Ord. rewrite Mult_R_Suc, Mult_R_Φ_r, Add_R_Φ_l; eauto.
  generalize dependent a. apply R_Transfinite_Induction. intros.
  TF( a = Φ ). subst a. rewrite Mult_R_Φ_r; eauto. apply Lem123; auto.
  New H. apply OrdNum_classic in H3 as [].
  - New H3. destruct H3,H3. assert( x ∈ a ). rewrite H5. appA2G.
    apply H1 in H6. rewrite H5, Mult_R_Suc, H6; try eapply Lem123; eauto.
    rewrite Add_R_Suc, Add_R_Φ_r; eauto.
  - rewrite Mult_R_Lim; try eapply Lem123; eauto. eqext. appA2H H4.
    rdeHex. appA2H H6. rdeHex. New H7. apply H1 in H7. subst. rewrite H7 in H5.
    eapply Ord_Num_trans; eauto. appA2G. New H4.
    apply trans_Ord_Num in H4; auto. apply Lim_Ord_1 in H5; eauto.
    exists (PlusOne z). split; appA2G. New H5. apply H1 in H5.
    exists (PlusOne z); split; auto.
Qed.

(* 交换律不成立 *)

Fact Mult_R_nocom : PlusOne (PlusOne Φ) ⋅ ω <> ω ⋅ PlusOne (PlusOne Φ).
Proof.
  New Φ_is_Ord. New ω_is_Lim_Ord. New H0. destruct H1 as [H1 _].
  New H. apply Lem123 in H2. rewrite Mult_R_Suc; eauto.
  rewrite Mult_R_Suc; eauto. rewrite Mult_R_Φ_r; eauto.
  rewrite Add_R_Φ_l; eauto. New H2. apply Lem123 in H2. New MKT135a.
  TF( ω = Φ ). rewrite H5 in H4. emf.
  assert( PlusOne (PlusOne Φ) ⋅ ω = ω ).
  { assert( H' : ω ≼ PlusOne (PlusOne Φ) ⋅ ω ).
    eapply R_Mult_2; eauto. red. intros.
    assert ( PlusOne Φ ∈ PlusOne (PlusOne Φ) ).
    appA2G. rewrite H6 in H7. emf.
    assert( H'': PlusOne (PlusOne Φ) ⋅ ω ≼ ω ).
    { assert( ∀ a , a ∈ ω -> PlusOne (PlusOne Φ) ⋅ a ∈ ω ).
      { intros. apply @ MKT134 in H4. apply @ MKT134 in H4.
        eapply ω_Mult_in_ω; eauto. }
        rewrite Mult_R_Lim; eauto.
        set (A := \{ λ v,∃ u, u ≺ ω /\ v = PlusOne (PlusOne Φ) ⋅ u \}).
        eapply MKT118; eauto. assert( A ⊂ R ).
        red. intros. appA2H H7. rdeHex. apply trans_Ord_Num in H8; eauto.
        subst z. apply R_Mult_in_R; eauto. apply MKT120; auto.
        red. intros. appA2H H7. rdeHex. appA2H H9. rdeHex.
        apply H6 in H10. rewrite <- H11 in H10. (eapply Ord_Num_trans); eauto. }
      New (R_Mult_in_R (PlusOne (PlusOne Φ)) ω H2 H1). appA2H H6.
      eapply MKT27. split; eapply MKT118; auto. }
  rewrite H6. red. intros.
  assert( ω ∈ ω + ω ).
  { New MKT135a. rewrite Add_R_Lim ; eauto. appA2G.
    exists (PlusOne ω). split; appA2G. exists (PlusOne Φ).
    split. eapply Lim_Ord_1; eauto. rewrite Add_R_Suc; eauto.
    rewrite Add_R_Φ_r; eauto. }
  rewrite <- H7 in H8. NSym.
Qed.
