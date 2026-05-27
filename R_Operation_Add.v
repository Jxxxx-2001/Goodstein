Require Export OrdinalNum.Induction.
Require Export OrdinalNum.Recursion.

(* 加法 *)

Definition G1_A a := \{\ λ u v, u ∈ μ /\ v = a \}\.

Definition G2_A := \{\ λ u v, u ∈ μ /\ v = PlusOne u \}\.

Definition G3_A := \{\ λ u v, u ∈ μ /\
  ( ( Function u /\ v = ∪(ran(u)) ) \/ ( ~ Function u /\ v = Φ ) ) \}\.

Theorem AddFunction_R : ∀ a, a ∈ R -> exists ! F, OnTo F R R
  /\ F[Φ] = a
  /\ ∀n, Ordinal_Number n -> F[PlusOne n] = PlusOne F[n]
  /\ ∀n, Ordinal_Number n -> Lim_Ord n -> n ≠ Φ -> F[n] = ∪(ran(F|(n))).
Proof.
  intros.
  assert( F_G1: OnTo (G1_A a) μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0.
    destruct H2. appoA2H H1. destruct H4; subst; auto.
    eqext. eapply MKT19; eauto. TF ( z = Φ ). subst. appA2G. exists a. appoA2G.
    appA2G. exists a. appoA2G. red. intros. eapply MKT19; eauto. }
  assert( F_G2: OnTo G2_A μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0. destruct H2. appoA2H H1.
    destruct H4; subst; auto.
    eqext. eapply MKT19; eauto. appA2G. exists (PlusOne z). appoA2G.
    red. intros. eapply MKT19; eauto. }
  assert( F_G3: OnTo G3_A μ μ ).
  { repeat split. eapply PisRel. intros. appoA2H H0. destruct H2. appoA2H H1.
    destruct H4,H3,H3. destruct H5. destruct H5; subst; auto.
    destruct H5. contradiction. destruct H5,H5. contradiction. subst; auto.
    eqext. eapply MKT19; eauto. TF( Function z ). appA2G.
    exists (∪(ran(z))). appoA2G. eapply MKT49a; eauto. apply AxiomVI.
    apply AxiomV; auto. apply fdme; auto.
    appA2G. exists Φ. appoA2G. red. intros. eapply MKT19; eauto. }
  New F_G1. eapply (Recursion_R.Recursion_R (G1_A a) G2_A G3_A) in H0; eauto.
  destruct H0 as [F [H0 H1]]. exists F. split.
  - clear H1. destruct H0,H1. split.
    destruct H0,H3. repeat (split; auto).
    red. intros. eapply Einr in H5; eauto. destruct H5,H5.
    assert( ( ∀ x, x ∈ R -> F[x] ∈ R ) ).
    { apply R_Transfinite_Induction. intros.
      TF( a0 = Φ ). subst a0.
      assert( (G1_A a) [Φ] = a ).
      { eqext. appA2H H9. apply H10. appA2G. appoA2G. appA2G.
        intros. appA2H H10. appoA2H H11. destruct H12; subst; auto. }
      rewrite H1,H9. auto.
      New H7. apply OrdNum_classic in H10 as [].
      destruct H10,H10.
      assert( Ensemble F[x0] ).
      { red in H10. rewrite <- H3 in H10. apply Property_dm in H10; auto. }
      New H10. apply H2 in H13 as [H13 _].
      assert( G2_A [F[x0]] = PlusOne F[x0] ).
      { eqext. appA2H H14. apply H15. appA2G. appoA2G.
        appA2G. intros. appA2H H15. appoA2H H16. destruct H17; subst; auto. }
      rewrite H11,H13,H14. apply Lem123. apply H8. rewrite H11; auto. appA2G.
      New H10. destruct H11 as [H11 _]. New H11.
      apply H2 in H11 as [_ H11]. apply H11 in H12; auto. clear H11.
      New H0. eapply (Property_res_dom F a0) in H11 as [];
      try rewrite H3; eauto. New H0. apply (MKT126a F a0) in H14.
      assert( Ensemble (∪ ran( F | (a0))) ).
      { apply AxiomVI. eapply frne; eauto. }
      assert( G3_A [F | (a0)] = ∪(ran(F | (a0))) ).
      { eqext. appA2H H16. apply H17. appA2G. appoA2G.
        appA2G. intros. appA2H H17. appoA2H H18. destruct H19.
        repeat (destruct H20,H20; try contradiction; subst; auto). }
      rewrite H12,H16.
      assert( ran( F | (a0)) ⊂ R ).
      { red; intros. eapply Einr in H17; eauto. destruct H17,H17. rewrite H18.
        rewrite H13 in H17. eapply (Property_res F a0 x0) in H0 as [H0 _];
        try rewrite H3; eauto. rewrite H0. apply H8. auto. }
      eapply MKT120 in H17. appA2G. }
    rewrite H6. apply H7. rewrite H3 in H5; auto. split.
    + rewrite H1. eqext. appA2H H3. apply H4. appA2G. appoA2G.
      appA2G; intros. appA2H H4. appoA2H H5. destruct H6.
      try repeat destruct H7,H7; destruct H7; auto; subst; auto.
    + intros n H'. pose proof H' as H''. apply H2 in H'. clear H2.
      destruct H'. split.
      * clear H3. rewrite H2. eqext. appA2H H3. apply H4; clear H4.
        assert(Ensemble F[n]). destruct H0,H4. red in H''.
        rewrite <- H4 in H''. eapply (@ Property_dm F n) in H0; eauto.
        assert(Ensemble (PlusOne F[n])). eauto. appA2G. appoA2G.
        appA2G. intros. appA2H H4. appoA2H H5. destruct H6; subst; auto.
      * clear H2. intros. apply H3 in H2; clear H3; auto. rewrite H2.
        pose proof H0 as H'. destruct H' as [H' _].
        eapply (MKT126a F n0) in H'; eauto.
        destruct H4 as [H3 _]. destruct H0,H4. New H0.
        eapply (Property_res_dom F n0) in H0 as [];
        try rewrite H4; eauto. eqext. appA2H H9. apply H10. clear H10.
        pose proof H' as H'''. eapply frne in H'''; eauto.
        assert(Ensemble (∪(ran(F|(n0))))). apply AxiomVI; auto.
        appA2G. appoA2G. appA2G. intros. appA2H H10. appoA2H H11. destruct H12.
        try repeat destruct H13,H13; subst; auto; contradiction.
  - clear H0. intros. specialize H1 with x'. apply H1. clear H1. destruct H0,H1.
    split; auto. destruct H0,H3. split; auto. split.
    + rewrite H1. symmetry. eqext. appA2H H3. apply H4. appA2G. appoA2G.
      appA2G; intros. appA2H H4. appoA2H H5. destruct H6.
      try repeat destruct H7,H7; destruct H7; auto; subst; auto.
    + intros n H'. pose proof H' as H''. apply H2 in H'. clear H2.
      destruct H'. split.
      * clear H3. symmetry. rewrite H2. eqext. appA2H H3. apply H4; clear H4.
        assert(Ensemble x'[n]). destruct H0,H4.
        red in H''. rewrite <- H4 in H''.
        eapply (@ Property_dm x' n) in H0; eauto.
        assert(Ensemble (PlusOne x'[n])). eauto. appA2G. appoA2G.
        appA2G. intros. appA2H H4. appoA2H H5. destruct H6; subst; auto.
      * clear H2. intros. apply H3 in H2; clear H3; auto. rewrite H2.
        pose proof H0 as H'. destruct H' as [H' _].
        eapply (MKT126a x' n0) in H'; eauto. destruct H4 as [H3 _].
        destruct H0,H4. eapply (Property_res_dom x' n0) in H0 as [];
        try rewrite H4; eauto. symmetry. eqext. appA2H H8. apply H9. clear H9.
        pose proof H' as H'''. eapply frne in H'''; eauto.
        assert(Ensemble (∪(ran(x'|(n0))))). apply AxiomVI; auto.
        appA2G. appoA2G. appA2G. intros. appA2H H9. appoA2H H10. destruct H11.
        try repeat destruct H12,H12; subst; auto; contradiction.
Qed.

(* 对于任意a，运算Add_R *)
(* 如果 b ∉ R 则 u = μ, 取元的交 a + b = ∩ \{ λ u, u = μ \} = μ , 取元的并 a + b ≠ μ *)

Definition Add_R a b:= ∩ \{ λ u, Ordinal_Number a /\
  (∀ F, OnTo F R R
  -> F[Φ] = a
  -> (∀n, Ordinal_Number n -> F[PlusOne n] = PlusOne F[n])
  -> (∀n, Ordinal_Number n -> Lim_Ord n -> n ≠ Φ -> F[n] = ∪(ran(F|(n))))
  -> u = F[b]) \}.

Notation "a + b" := (Add_R a b).

(**********************************************************************)
(* 加法验证 *)

Lemma Add_R_Φ_r : forall a, Ordinal_Number a -> a + Φ = a.
Proof.
  intros. New H. apply AddFunction_R in H0.
  destruct H0 as [F [H0 H0']]. assert( a + Φ = F[Φ] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. destruct H0,H0,H3. New Φ_is_Ord. red in H5. rewrite <- H3 in H5.
    apply Property_dm in H5; eauto. repeat split; auto. intros.
    rewrite H3. destruct H0,H6. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[Φ] ). eapply H3; eapply H0; eauto. rewrite H4; auto. }
  rewrite H1. destruct H0,H2. auto.
Qed.

Lemma Add_R_Suc : forall a b,
  Ordinal_Number a -> Ordinal_Number b -> a + (PlusOne b) = PlusOne (a + b).
Proof.
  intros. pose proof H as H_a. apply AddFunction_R in H.
  destruct H as [F [H H']].
  assert( E: a + (PlusOne b)  =  F[PlusOne b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    assert( Ensemble (F[PlusOne b]) ).
    red in H0. apply Lem123 in H0. destruct H,H,H3.
    rewrite <- H3 in H0. eapply Property_dm in H0; eauto.
    appA2G. repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[PlusOne b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite E. assert( E1: a + b  =  F[b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. red in H0. destruct H,H,H3.
    rewrite <- H3 in H0. eapply Property_dm in H0; eauto.
    repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite E1. destruct H,H1. apply H2 in H0. destruct H0. auto.
Qed.

Lemma Add_R_Lim : forall a b,
  Ordinal_Number a -> Lim_Ord b -> b ≠ Φ
  -> a + b = ∪ \{ λ v, ∃ u, u ≺ b /\ v = (a + u) \}.
Proof.
  intros. pose proof H as H_a. apply AddFunction_R in H.
  destruct H as [F [H H']].
  assert( a + b  =  F[b] ).
  { destruct H0. eqext. appA2H H3. apply H4.
    clear H4. appA2G. destruct H,H,H5. red in H0. rewrite <- H5 in H0.
    apply MKT69b in H0. auto. repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H4.
    assert( y = F[b] ). eapply H5; eapply H; eauto. rewrite H6; auto. }
  rewrite H2.
  assert( \{ λ v, ∃ u, u ≺ b /\ v = (a + u) \} = ran(F | (b)) ).
  { pose proof H as H''. destruct H,H,H4. eqext. appA2G. appA2H H6.
    destruct H7,H7. exists x. appA2G.
    assert( a + x = F[x] ).
    { destruct H0 as [H0 _]. eqext. appA2H H9. apply H10. clear H10.
      assert( Ensemble F[x] ).
      eapply trans_Ord_Num in H7; eauto. red in H7. rewrite <- H4 in H7.
      apply MKT69b in H7; auto. appA2G.
      red in H0. appA2H H0. New H7. eapply MKT111 in H7; eauto.
      repeat split; auto.
      intros. assert( F = F0 ). eapply H'; eauto. subst F0. auto.
      appA2G. intros. appA2H H10.
      assert( y = F[x] ). eapply H11; eapply H''; eauto. rewrite H12; auto. }
    split. destruct H0 as [H0 _]. eapply trans_Ord_Num in H7; eauto.
    red in H7. rewrite <- H4 in H7. rewrite H9 in H8. subst z.
    eapply Property_Value; eauto. appoA2G.
    appA2H H6. destruct H7. appA2H H7.
    destruct H8. appoA2H H9. clear H9. destruct H10.
    appA2G. exists x. split; auto.
    assert( a + x = F[x] ).
    { destruct H0. eqext. appA2H H12. apply H13. clear H13.
      assert( Ensemble F[x] ).
      eapply trans_Ord_Num in H9; eauto. red in H9. rewrite <- H4 in H9.
      apply MKT69b in H9; auto. appA2G.
      red in H0. New H9. eapply MKT111 in H9; eauto.
      repeat split; auto. intros.
      assert( F = F0 ). eapply H'; eauto. subst F0. auto. appA2H H0. auto.
      appA2G. intros. appA2H H13.
      assert( y = F[x] ). eapply H14; eapply H''; eauto. rewrite H15; auto. }
    rewrite H11. eapply Property_Fun in H8; eauto. }
  rewrite H3. New H0. destruct H,H0,H5. New H0. apply H7 in H0.
  destruct H0 as [_ H0]. eapply H0 in H8; eauto.
Qed.

Lemma Add_R_Φ_l : forall a, Ordinal_Number a -> Φ + a = a.
Proof.
  intros. eapply (R_Transfinite_Induction (fun x => (Φ + x) = x )); eauto.
  intros. TF( a0 = Φ ). subst. rewrite Add_R_Φ_r; eauto.
  New H0. eapply OrdNum_classic in H3; eauto. New Φ_is_Ord. destruct H3.
  destruct H3,H3. rewrite H5. assert( x ∈ a0 ). rewrite H5; appA2G.
  eapply H1 in H6; eauto. rewrite Add_R_Suc; try rewrite H6; eauto.
  rewrite Add_R_Lim; eauto.
  eqext. appA2H H5. destruct H6,H6. appA2H H7. destruct H8,H8. New H8.
  eapply H1 in H10. subst x. rewrite H10 in H6. destruct H3.
  eapply Ord_Num_trans; eauto.
  appA2G. exists (PlusOne z). split; appA2G; auto.
  exists (PlusOne z). clear H4. New H5. eapply trans_Ord_Num in H5; eauto.
  eapply (Lim_Ord_1 a0) in H3; eauto. split; try symmetry; auto.
Qed.

(**********************************************************************)
(* 加法相关性质 *)

Corollary R_Add_in_R : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> (a + b) ∈ R .
Proof.
  intros. pose proof H as H_a. pose proof H0 as H_b.
  apply AddFunction_R in H. destruct H as [F [H H']].
  assert( a + b  =  F[b] ).
  { eqext. appA2H H1. apply H2. clear H2.
    appA2G. destruct H,H,H3. red in H0. rewrite <- H3 in H0.
    apply MKT69b in H0. auto. repeat split; auto. intros.
    assert( F = F0 ). eapply H'; eauto. subst F0. auto.
    appA2G. intros. appA2H H2.
    assert( y = F[b] ). eapply H3; eapply H; eauto. rewrite H4; auto. }
  rewrite H1. destruct H,H,H3. red in H_b. rewrite <- H3 in H_b.
  eapply Property_dm in H_b; auto.
Qed.

Corollary R_Add_in_R' : forall a b, Ordinal_Number a -> (a + b) ∈ R
  -> Ordinal_Number b.
Proof.
  intros. pose proof H as H_a. apply AddFunction_R in H.
  destruct H as [F [H _]]. TF( Ordinal_Number b ); auto.
  assert( a + b = ∩ \{ λ u, u = μ \} ).
  { unfold Add_R.
    assert( \{ λ u, Ordinal_Number a /\
          (∀ F0, OnTo F0 R R -> F0 [Φ] = a ->
          (∀ n, Ordinal_Number n -> F0 [PlusOne n] = PlusOne F0 [n]) ->
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

Corollary ω_Add_in_ω : forall a b, a ∈ ω -> b ∈ ω
  -> (a + b) ∈ ω .
Proof.
  intros. assert( a ∈ R ). appA2H H. destruct H1. appA2G.
  eapply (ω_Transfinite_Induction (fun x => a + x ∈ ω )); eauto.
  intros. TF( a0 = Φ ). subst a0. rewrite Add_R_Φ_r; eauto.
  New (ω_Num_is_Suc_Ord a0 H2 H4). destruct H5,H5.
  assert( x ∈ a0 ). subst a0. appA2G. apply H3 in H7.
  subst a0. rewrite Add_R_Suc; eauto.
Qed.

(* 保序(左单调性) *)
Theorem Add_R_PrOrder_a : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b
  -> ( a1 ≺ a2 -> b + a1 ≺ b + a2 ).
Proof.
  intros.
  eapply (R_Transfinite_Induction (fun x => a1 ≺ x -> b + a1 ≺ b + x)); eauto.
  intros. TF( a = Φ ). subst. unfold Less in H5. emf.
  apply OrdNum_classic in H3 as [].
  + destruct H3,H3. assert(x ∈ a). subst; appA2G.
    New H. red in H9. New H3. eapply (Ord_Num_tri x a1) in H10; eauto.
    destruct H10. subst a. eapply (Ord_Num_not_dense x a1) in H10; eauto.
    unfold Less in H5. contradiction. destruct H10.
    * subst x. rewrite H7. rewrite Add_R_Suc; auto.
      eapply (R_Add_in_R b a1) in H1; eauto. appA2G.
    * eapply H4 in H8; eauto. rewrite H7.
      rewrite Add_R_Suc; auto. New H1.
      eapply (R_Add_in_R b x) in H11; eauto.
      New H11. eapply Lem123 in H12. red in H.
      eapply (R_Add_in_R b a1) in H; eauto.
      eapply (Ord_Num_trans (b + a1) (b + x) (PlusOne (b + x))); eauto.
      appA2G; eauto.
  + assert( a1 ∈ PlusOne a1 ). appA2G. assert( PlusOne a1 ∈ a ).
    { pose proof H as H'. red in H. New H. apply Lem123 in H8.
      New H3. destruct H9. pose proof H9 as H''.
      eapply (Ord_Num_tri (PlusOne a1) a) in H9; eauto.
      try repeat destruct H9; eauto. elim H10. exists a1; auto.
      eapply (Ord_Num_not_dense a1 a) in H'; eauto. contradiction. }
    New H8. eapply H4 in H8; eauto. rewrite (Add_R_Lim b a); eauto.
    unfold Less. appA2G. exists (b + PlusOne a1). split; eauto.
    appA2G. eapply (R_Add_in_R b (PlusOne a1)) in H1; eauto.
    red in H. apply Lem123 in H. auto.
Qed.

Theorem Add_R_PrOrder_b : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b
  -> ( b + a1 ≺ b + a2 -> a1 ≺ a2 ).
Proof.
  intros. New H. eapply (Ord_Num_tri a1 a2) in H3; eauto.
  destruct H3; auto. destruct H3. subst. NSym.
  eapply Add_R_PrOrder_a in H3; eauto.
  eapply (Ord_Num_antisym (b + a1) (b + a2)) in H2;
  try eapply R_Add_in_R; eauto. contradiction.
Qed.

Theorem Add_R_PrOrder : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b
  -> ( a1 ≺ a2 <-> b + a1 ≺ b + a2 ).
Proof.
  intros. split; intros; try eapply Add_R_PrOrder_a; eauto.
  try eapply Add_R_PrOrder_b; eauto.
Qed.

(* 消去 *)
Theorem Add_R_Cancellation : ∀ a1 a2 b,
  Ordinal_Number a1 -> Ordinal_Number a2-> Ordinal_Number b
  -> ( b + a1 = b + a2 <-> a1 = a2 ).
Proof.
  split; intros.
  - New H. eapply (Ord_Num_tri a1 a2) in H3; eauto.
    try repeat destruct H3; auto. eapply Add_R_PrOrder_a in H3; eauto.
    rewrite H2 in H3. NSym.
    eapply (Add_R_PrOrder_a a2 a1) in H3; eauto.
    rewrite H2 in H3. NSym.
  - New H. eapply (Ord_Num_tri a1 a2) in H3; eauto.
    try repeat destruct H3; subst; auto.
Qed.

Ltac ONtrans_eq :=
  match goal with
   | H1: ?a ≼ ?b ,
     H2: ?b ≺ ?c ,
     H3: ?c ∈ R
    |- ?a ∈ ?c  => eapply Ord_Num_trans'; eauto
   | H1: ?a ≺ ?b ,
     H2: ?b ≼ ?c ,
     H3: ?c ∈ R
    |- ?a ∈ ?c => eapply Ord_Num_trans''; eauto
  end.

(* 结合 *)

Lemma R_Add_1 : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> b ≺ a -> PlusOne b ≼ a.
Proof.
  intros. New H0. eapply Lem123 in H2. New H2.
  eapply (Ord_Num_tri (PlusOne b) a) in H3; auto.
  red; try repeat (destruct H3; auto).
  eapply Ord_Num_not_dense in H1; eauto. contradiction.
Qed.

Lemma R_Add_2 : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> a ≼ b -> PlusOne a ≼ PlusOne b.
Proof.
  intros. New H. New H0. eapply Lem123 in H2,H3.
  New H2. eapply (Ord_Num_tri (PlusOne a) (PlusOne b)) in H4; eauto.
  red. try repeat (destruct H4; auto).
  assert( b ≺ PlusOne b ). appA2G. assert( a ≺ PlusOne b ). red. ONtrans_eq.
  eapply R_Add_1 in H6; eauto.
Qed.

Lemma R_Add_2' : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> (a ≺ b <-> PlusOne a ≺ PlusOne b).
Proof.
  split; intros.
  - eapply R_Add_1 in H1; eauto. assert( b ∈ PlusOne b ). appA2G.
    eapply Ord_Num_trans'; eauto. eapply Lem123; eauto.
  - New (Ord_Num_tri a b H H0); eauto. try repeat (destruct H2; auto).
    NSym. eapply R_Add_1 in H2; eauto. assert( a ≺ PlusOne a ). appA2G.
    assert( PlusOne b ≺ PlusOne a ). eapply Ord_Num_trans'; eauto.
    eapply Lem123; eauto.
    eapply Ord_Num_antisym in H1; try contradiction;
    try eapply Lem123; eauto.
Qed.

Lemma R_Add_3 : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> b ≼ a + b.
Proof.
  intros. generalize dependent b.
  eapply (R_Transfinite_Induction (fun x => x ≼ a + x)); eauto.
  intros. New H0. eapply OrdNum_classic in H2 as [].
  - New H2. destruct H3,H3.
    assert( x ∈ a0 ). rewrite H4; appA2G. New H5. eapply H1 in H6.
    rewrite H4. rewrite Add_R_Suc; eauto. eapply R_Add_2; eauto.
    eapply R_Add_in_R; eauto.
  - TF( a0 = Φ ). subst. rewrite Add_R_Φ_r; eauto. TF( a = Φ ).
    right; auto. left. eapply Φ_is_First_Ord; eauto.
    eapply MKT118. appA2H H0; auto.
    New( R_Add_in_R a a0 H H0). appA2H H4; auto.
    red. intros. New H4. eapply H1 in H5.
    New( trans_Ord_Num a0 z H0 H4 ).
    eapply (Add_R_PrOrder_a z a0 a) in H6; eauto.
    New( R_Add_in_R a a0 H H0). eapply Less_eq_E',Less_eq_E; eauto.
    red. ONtrans_eq.
Qed.

Lemma R_Add_3' : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> a ≼ a + b.
Proof.
  intros. generalize dependent b.
  eapply (R_Transfinite_Induction (fun x => a ≼ a + x)); eauto.
  intros. New H0. eapply OrdNum_classic in H2 as [].
  - New H2. destruct H3,H3.
    assert( x ∈ a0 ). rewrite H4; appA2G. New H5. eapply H1 in H6.
    rewrite H4. rewrite Add_R_Suc; eauto. destruct H6. left.
    New (R_Add_in_R a x H H3). assert( (a + x) ∈ PlusOne (a + x) ). appA2G.
    eapply (Ord_Num_trans a (a + x)); eauto. eapply Lem123; eauto. left.
    rewrite <- H6. appA2G.
  - TF( a0 = Φ ). subst. rewrite Add_R_Φ_r; eauto. right. auto.
    TF( a = Φ ). subst. rewrite Add_R_Φ_l; eauto. left.
    eapply Φ_is_First_Ord; eauto.
    eapply MKT118. appA2H H; auto. New H2. destruct H5 as [H5 _].
    New( R_Add_in_R a a0 H H5 ). appA2H H6; auto.
    red. intros. rewrite Add_R_Lim; eauto. appA2G.
    exists a. split; auto. appA2G.
    exists Φ. split. eapply Φ_is_First_Ord; eauto.
    rewrite Add_R_Φ_r; auto.
Qed.

Lemma R_Add_4 : forall a b, Ordinal_Number a -> Ordinal_Number b -> b <> Φ
  -> a ≺ a + b.
Proof.
  intros. assert( Φ ≺ b ). apply Φ_is_First_Ord; auto.
  eapply (Add_R_PrOrder_a Φ b a) in H2; eauto.
  rewrite Add_R_Φ_r in H2; auto. apply Φ_is_Ord.
Qed.

Lemma R_Add_5 : forall a b, Ordinal_Number a -> Lim_Ord b -> b ≠ Φ
  -> Lim_Ord (a + b) /\ a + b <> Φ.
Proof.
  intros. New H0. destruct H2 as [H2 _]. New H.
  eapply (R_Add_in_R a b) in H3; eauto. New H.
  eapply (R_Add_3 a b) in H4; eauto. New H2.
  eapply Φ_is_First_Ord in H5; auto.
  assert( a + b <> Φ ).
  { red. intros. rewrite H6 in H4. destruct H4.
    eapply MKT16; eauto. subst b. NSym. }
  split; auto. eapply Lim_Ord_1; eauto. intros.
  New H7. eapply trans_Ord_Num in H8; eauto.
  rewrite Add_R_Lim in H7; eauto. appA2H H7. destruct H9. deand.
  appA2H H10. destruct H11,H11.
  subst x. eapply R_Add_1 in H9; eauto. New H11.
  eapply trans_Ord_Num in H12; eauto.
  eapply (Add_R_PrOrder_a x0 b a) in H12; eauto. New H11.
  eapply (Add_R_PrOrder_a x0 b a) in H13; eauto.
  destruct H9; try rewrite H9; auto. eapply Ord_Num_trans; eauto.
  eapply trans_Ord_Num in H11; eauto.
  eapply trans_Ord_Num in H11; try eapply R_Add_in_R; eauto.
Qed.

Theorem Add_R_Association : ∀ a b c, a ∈ R -> b ∈ R -> c ∈ R
  -> (a + b) + c = a + (b + c).
Proof.
  intros. generalize dependent c. apply R_Transfinite_Induction. intro c.
  intros. TF (c = Φ).
  - subst. rewrite Add_R_Φ_r,Add_R_Φ_r; auto.
    apply R_Add_in_R; auto.
  - New H1. apply OrdNum_classic in H4 as [].
    * destruct H4,H4. subst c. rewrite Add_R_Suc,Add_R_Suc,
      Add_R_Suc; try apply R_Add_in_R; auto. rewrite H2. auto. appA2G.
    * rewrite Add_R_Lim; try apply R_Add_in_R; auto.
      assert( (∪ \{ λ v, ∃u, ((u ≺ c) /\ (v = ((a + b) + u))) \}) 
        = (∪ \{ λ v, ∃u, ((u ≺ c) /\ (v = (a + (b + u)))) \})  ).
      { eqext; appA2H H5; rdeHex; appA2H H7; rdeHex;
        appA2G; exists x; split; auto; appA2G; exists x0; split; auto;
        eapply H2 in H8; eauto. rewrite <- H8. auto. rewrite H8; auto. }
      rewrite H5; clear H5.
      assert( Lim_Ord (b + c) /\ (b + c) <> Φ ) as []. eapply R_Add_5; eauto.
      rewrite Add_R_Lim; auto.
      assert( \{ λ v, ∃u, ((u ≺ c) /\ (v = (a + (b + u)))) \} =
              \{ λ v, ∃u, ((b + u ≺ b + c) /\ (v = (a + (b + u)))) \} ).
      { eqext; appA2H H7; rdeHex; appA2G; exists x; split; auto.
        eapply Add_R_PrOrder_a; eauto. eapply trans_Ord_Num; eauto.
        eapply (Add_R_PrOrder_b x c b); eauto.
        eapply (R_Add_in_R' b x); eauto.
        eapply trans_Ord_Num in H8; eauto. eapply R_Add_in_R; eauto. }
      rewrite H7; clear H7.
      set (A := \{ λ v,∃ δ, δ ≺ b + c /\ v = a + δ \}).
      set (B := \{ λ v,∃ ε, (b + ε ≺ b + c) /\ (v = (a + (b + ε))) \}).
      New H5. destruct H7 as [H' _].
      symmetry. pose proof (Sup_R_eq A B) as H0'.
      assert( A ⊂ R ).
      { red. intros. appA2H H7. destruct H8,H8.
        eapply trans_Ord_Num in H8; eauto. New H.
        eapply (R_Add_in_R a x) in H10; eauto. rewrite <- H9 in H10. auto. }
      assert( B ⊂ A ). { red; intros. appA2H H8. destruct H9,H9. appA2G. }
      assert( A': Ensemble A ).
      { destruct H5 as [H5 _]. assert( A ⊂ (a + (b + c)) ).
        red. intros. appA2H H9. rdeHex. New (trans_Ord_Num (b + c) x H5 H10).
        subst z. eapply Add_R_PrOrder_a; eauto.
        New (R_Add_in_R a (b + c) H H5).
        eapply (MKT33 (a + (b + c)) A); eauto. }
      assert( B': Ensemble B ). eapply MKT33; eauto.
      New H7. eapply H0' in H9; eauto.
      rewrite <- (Sup_R_eq_U A); eauto. rewrite <- (Sup_R_eq_U B); eauto.
      red; intros.  apply H8 in H10. apply H7 in H10. auto.

      intros. New H10. appA2H H10. destruct H12 as [δ [H12 H13]]. subst a0.
      set (C := \{ λ v, v ∈ R /\ δ ≼ b + v \}).
      assert( ∃ ε, FirstMember ε E C ).
      { exists (∩ C). eapply Lemma121; eauto. red; intros.
        appA2H H13. destruct H14; auto.
        assert( c ∈ C ). appA2G. split; auto. left; auto.
        apply NEexE. exists c; auto. }
      destruct H13 as [ε H13].
      assert( ε ≼ c ). destruct H13. appA2H H13. destruct H15. destruct H4.
      New (Ord_Num_tri ε c H15 H4). destruct H18. left; auto.
      destruct H18. right; auto.
      assert( c ∈ C ). appA2G; split; auto. left; auto.
      eapply H14 in H19. elim H19. eapply Less_eq_E; auto.

      destruct H14.
      + New (trans_Ord_Num c ε H1 H14).
        eapply (Add_R_PrOrder_a ε c b) in H14; eauto.
        destruct H5 as [H5' _]. New (trans_Ord_Num (b + c) (b + ε) H5' H14).
        New (trans_Ord_Num (b + c) δ H5' H12).
        assert( δ ≼ b + ε ).
        { destruct H13. appA2H H13. destruct H18. auto. }
        assert( H'': a + (b + ε) ∈ B ).
        { appA2G. New (R_Add_in_R a (b + ε) H H5). appA2H H18. auto. }
        destruct H17.
        eapply (Add_R_PrOrder_a δ (b + ε) a) in H16; eauto.
        exists(a + (b + ε)). split; auto; left; auto.
        exists(a + (b + ε)). split; auto.
        right; eapply (Add_R_Cancellation); auto.
      + subst ε. destruct H5. New (trans_Ord_Num (b + c) δ H5 H12).
        assert( H'': ∀ c0, c0 ∈ c -> b + c0 ≺ δ ).
        { intros. New (trans_Ord_Num c c0 H1 H16).
          New (R_Add_in_R b c0 H0 H17). TF( c0 ∈ C ).
          destruct H13. eapply H20 in H19. elim H19.
          eapply Less_eq_E; eauto.
          New (Ord_Num_tri (b + c0) δ H18 H15). destruct H20; auto.
          assert( c0 ∈ C ). appA2G. split; auto. destruct H20. right; auto.
          left; auto. contradiction. }
        assert( b + c ≼ δ ).
        { eapply MKT118; eauto. red in H5,H15. appA2H H5; auto.
          appA2H H15; auto. red; intros.
          rewrite Add_R_Lim in H16; eauto. appA2H H16. rdeHex.
          appA2H H18. rdeHex. New (trans_Ord_Num c x0 H1 H19).
          eapply H'' in H19. subst x. eapply Ord_Num_trans; eauto. }
        destruct H16. New (MKT102 (b + c) δ H16 H12). destruct H17.
        rewrite H16 in H12. NSym.
Qed.

(* 补差律 *)
Lemma R_Add_6 : forall a b c, Ordinal_Number a -> Ordinal_Number c
  -> a + b ≺ c -> b ≼ c.
Proof.
  intros. New H1. eapply trans_Ord_Num, R_Add_in_R' in H2; eauto.
  New (Ord_Num_tri b c H2 H0).
  destruct H3. left; auto. destruct H3. right; auto.
  eapply Ord_Num_trans in H3; eauto.
  New (R_Add_3 a b H H2). red in H0. left. ONtrans_eq.
Qed.

Theorem Add_R_Sub_1 : ∀ a b,
  Ordinal_Number a -> Ordinal_Number b -> b ≼ a ->
  ( exists c, c ≼ a /\ b + c = a ).
Proof.
  intros. generalize dependent a.
  eapply (R_Transfinite_Induction
  (fun x => b ≼ x -> ∃ c, c ≼ x /\ b + c = x)); eauto.
  intros. TF( a = Φ ). subst. destruct H2. emf.
  exists Φ. subst. split; try right; eauto. rewrite Add_R_Φ_l; auto.
  New H. apply OrdNum_classic in H4 as [].
  + destruct H2.
    * New H4. destruct H5,H5. assert( b ≼ x ).
      { New (Ord_Num_tri b x H0 H5). destruct H7.
        left; auto. destruct H7; right; auto. rewrite H6 in H2. 
        eapply Ord_Num_not_dense in H7; eauto. contradiction. }
      assert( x ∈ a ). subst; appA2G.
      eapply H1 in H8; eauto. destruct H8,H8.
      assert( Ordinal_Number x0 ). destruct H8.
      eapply trans_Ord_Num; eauto. subst x0. auto.
      exists (PlusOne x0). split. eapply R_Add_1; eauto.
      rewrite H6. assert( x ≺ PlusOne x ). appA2G. red. eapply Lem123 in H5.
      ONtrans_eq. rewrite Add_R_Suc; auto. rewrite H9. auto.
    * exists Φ. split. left. eapply Φ_is_First_Ord; eauto.
      rewrite Add_R_Φ_r; auto.
  + destruct H2.
    * set(c := \{ λ v,∃ u, b ≺ u /\ u ≺ a /\ b + v = u \}).
      assert( H': c ⊂ R ). red; intros. appA2H H5. rdeHex. subst x.
      eapply trans_Ord_Num in H7; eauto. eapply R_Add_in_R' in H7; eauto.
      New H'. assert( c ⊂ (∪ c) ). red; intros. appA2G. exists (PlusOne z).
      split. appA2G. appA2G. appA2H H6. rdeHex. exists (PlusOne x).
      New (trans_Ord_Num a x H H8). New (Lem123 _ H10).
      split. assert( x ∈ PlusOne x ). appA2G. eapply Ord_Num_trans; eauto.
      split. eapply Lim_Ord_1 in H8; eauto. rewrite Add_R_Suc,H9; auto.
      rewrite <- H9 in H10. eapply R_Add_in_R' in H10; eauto.
      apply MKT120 in H5. New (@ Th110ano (∪ c) R H5 MKT113a).
      destruct H7.
      ** assert( Ensemble c ). eapply (MKT33 (∪ c) c); eauto.
         New (Sup_R_eq_U c H' H8). apply OrdNum_classic in H7 as [].
         -- destruct H7,H7. assert( x ∈ ∪ c ). rewrite H10. appA2G.
            New H11. appA2H H12. rdeHex. New H14. appA2H H15. rdeHex.
            New H14. apply H' in H19. New H13. New H17.
            apply trans_Ord_Num in H20,H21; eauto.
            assert( PlusOne x0 ∈ c ).
            { appA2G. exists (PlusOne x1). assert( x1 ∈ PlusOne x1 ).
              appA2G. eapply Ord_Num_trans in H22; try apply Lem123; eauto.
              eapply Lim_Ord_1 in H17; eauto. repeat split; auto.
              rewrite Add_R_Suc,H18; eauto. }
            assert( PlusOne x ∈ PlusOne x0 ).
            { eapply R_Add_1 in H13; eauto. destruct H13.
              assert( x0 ∈ PlusOne x0 ). appA2G.
              eapply Ord_Num_trans; eauto. eapply Lem123; eauto.
              rewrite H13; appA2G. }
            apply H6 in H22. rewrite H10 in H22.
            eapply Ord_Num_antisym in H22; try eapply Lem123; eauto.
            contradiction.
         -- assert( (Φ) ∈ (∪ c) ). appA2G. exists (PlusOne Φ). split. appA2G.
            appA2G. exists (PlusOne b). split. appA2G. split.
            eapply Lim_Ord_1 in H2; eauto. rewrite Add_R_Suc, Add_R_Φ_r; eauto.
            eapply Φ_is_Ord. assert( ∪ c <> Φ ).
            red; intros. rewrite H11 in H10. emf.
            exists (∪ c). split. eapply MKT118; eauto. appA2H H. auto.
            red. intros. appA2H H12. rdeHex. appA2H H14. rdeHex. subst x0.
            assert( b + z ≺ a ).
            { New H13. eapply Ord_Num_trans; eauto.
              eapply trans_Ord_Num,R_Add_in_R' in H16; eauto.
              eapply (Add_R_PrOrder_a _ _ b) in H13; eauto.
              eapply trans_Ord_Num; eauto. }
            eapply R_Add_6 in H17,H16; eauto. destruct H17; auto.
            destruct H16. eapply Ord_Num_trans; eauto. subst x.
            rewrite H17 in H13. NSym.
            TF( b = Φ ).
            subst b. destruct H7. rewrite Add_R_Φ_l; eauto.
            eqext. appA2H H13. rdeHex. New H15. apply H' in H16.
            appA2H H15. rdeHex. rewrite Add_R_Φ_l in H19; eauto.
            subst x. eapply Ord_Num_trans; eauto.
            appA2G. New (trans_Ord_Num a z H H13). New (Lem123 z H14).
            exists (PlusOne z). split; appA2G.
            exists (PlusOne z). split. eapply Φ_is_First_Ord; eauto.
            red; intros. assert( z ∈ PlusOne z ). appA2G.
            rewrite H16 in H17. emf. split. eapply Lim_Ord_1; eauto.
            rewrite Add_R_Φ_l; auto.

            rewrite Add_R_Lim; try rewrite H9; eauto.
            eqext. appA2H H13. rdeHex. appA2H H15. rdeHex.
            appA2H H16. rdeHex. appA2H H19. rdeHex.
            New H21. eapply trans_Ord_Num in H23; eauto. subst. New H23.
            eapply R_Add_in_R' in H23; eauto.
            eapply (Add_R_PrOrder_a _ _ b) in H18; eauto.
            eapply Ord_Num_trans in H18; eauto.
            eapply Ord_Num_trans in H21; eauto.
            eapply trans_Ord_Num in H18; eauto. appA2G.
            New (trans_Ord_Num _ _ H H13).
            TF( z ∈ b ). exists b. split; auto. appA2G. exists Φ.
            split; try rewrite Add_R_Φ_r; auto.
            assert( b ≼ z ). { appA2H H0. appA2H H14. eapply MKT118; eauto.
            New (@ Th110ano z b H17 H16). destruct H18; auto. contradiction. }
            clear H15. New H13.
            apply H1 in H13; auto. rdeHex. exists (PlusOne z). split.
            appA2G. appA2G. assert( Ordinal_Number x ).
            rewrite <- H17 in H14. eapply R_Add_in_R' in H14; eauto.
            exists( PlusOne x ). split. appA2G.
            exists( PlusOne (PlusOne x) ). split. appA2G. right. appA2G. appA2G.
            exists( PlusOne (PlusOne z) ). assert( z ∈ PlusOne (PlusOne z) ).
            destruct H16; appA2G; left; appA2G. destruct H16.
            split. eapply Ord_Num_trans; eauto. try eapply Lem123; eauto.
            split. try repeat (eapply Lim_Ord_1; try eapply Lem123; eauto).
            rewrite Add_R_Suc,Add_R_Suc,H17; eauto. eapply Lem123; eauto.
            subst z. rewrite <- H16. split. appA2G. left; appA2G.
            split. try repeat (eapply Lim_Ord_1; try eapply Lem123; eauto).
            rewrite Add_R_Suc,Add_R_Suc; try rewrite <- H16; eauto.
            eapply Lem123; eauto. symmetry.
            rewrite Add_R_Suc; try rewrite H13; auto. rewrite H17; auto.
      ** apply H7 in H. appA2H H. rdeHex. appA2H H9. rdeHex.
         assert( x ≼ a ). rewrite <- H12 in H11. destruct H4.
         eapply R_Add_6 in H11; eauto.
         destruct H13,H4. eapply Ord_Num_antisym in H13; eauto. contradiction.
         eapply trans_Ord_Num; eauto.
         rewrite H13 in H8. NSym.
    * exists Φ. split. left. eapply Φ_is_First_Ord; eauto.
      rewrite Add_R_Φ_r; auto.
Qed.

Theorem Add_R_Sub_2 : ∀ a b,
  Ordinal_Number a -> Ordinal_Number b -> b ≼ a ->
  ∀ c1 c2, (c1 ≼ a /\ b + c1 = a) -> (c2 ≼ a /\ b + c2 = a) -> c1 = c2.
Proof.
  intros. deand. New H4. rewrite <- H5 in H4.
  eapply (Add_R_Cancellation c2 c1 b) in H4; eauto.
  rewrite <- H6 in H. eapply R_Add_in_R' in H; eauto.
  rewrite <- H5 in H. eapply R_Add_in_R' in H; eauto.
Qed.

Theorem Add_R_Sub : ∀ a b,
  Ordinal_Number a -> Ordinal_Number b -> b ≼ a ->
  ( exists! c, c ≼ a /\ b + c = a ).
Proof.
  intros. New (Add_R_Sub_1 _ _ H H0 H1). rdeHex. exists x. split. auto.
  intros. New (Add_R_Sub_2 _ _ H H0 H1 x'). symmetry. apply H5; auto.
Qed.

Theorem Add_Union : forall a b, Ordinal_Number a -> Ordinal_Number b
  -> a + b = a ∪ \{ λ v, ∃ u, u ≺ b /\ v = (a + u) \}.
Proof.
  intros. generalize dependent b.
  eapply (R_Transfinite_Induction); eauto. intros.
  TF( a0 = Φ ). subst. rewrite Add_R_Φ_r; eauto.
  assert( \{ λ v, ∃ u, u ≺ Φ /\ v = (a + u) \} = Φ ).
  { eqE. appA2H H2. destruct H3,H3. eapply MKT16 in H3. destruct H3. }
  rewrite H2. eqext. appA2G. appA2H H3. destruct H4. auto. emf.
  New H0. eapply OrdNum_classic in H3 as [].
  - destruct H3,H3. rewrite H4. rewrite Add_R_Suc; eauto.
    unfold PlusOne. assert( x ∈ a0 ). rewrite H4. appA2G.
    apply H1 in H5. rewrite H5. rewrite MKT7. rewrite <- H5.
    eqext. appA2H H6. destruct H7. appA2G. appA2G. right. appA2H H7.
    destruct H8. appA2H H8. destruct H9,H9. appA2G. exists x0.
    split; auto. appA2G. appA2G. exists x. split. appA2G. appA2H H8.
    apply H9. New (R_Add_in_R a x H H3). eauto.
    appA2H H6. destruct H7. appA2G. appA2H H7.
    destruct H8,H8. appA2H H8. destruct H10. appA2G. right.
    appA2G. left. appA2G. appA2G. right. appA2G. right. appA2H H10.
    New H3. appA2H H12. apply MKT19 in H12. apply H11 in H12.
    subst x0. appA2G.
  - assert( ∪ \{ λ v, (∃ u,((u ≺ a0) /\ (v = (a + u)))) \} =
              ∪ \{ λ v, (∃ u,((u ≺ a0) /\
                (v = (a ∪ \{ λ v,(∃ u',((u' ≺ u) /\ (v = (a + u')))) \}))))\} ).
    { eqext. appA2H H4. destruct H5,H5. appA2H H6. destruct H7,H7.
      appA2G. exists x. split; auto. appA2G. exists x0. split; auto.
      apply H1 in H7. rewrite <-  H7. auto.
      appA2H H4. destruct H5,H5. appA2H H6. destruct H7,H7.
      appA2G. exists x. split; auto. appA2G. exists x0. split; auto.
      apply H1 in H7. rewrite H7. auto. }
    rewrite Add_R_Lim; auto. rewrite H4. clear H4.
    eqext. appA2H H4. destruct H5,H5. appA2H H6. destruct H7,H7.
    appA2G. New H5. rewrite H8 in H9. appA2H H9. destruct H10. left. auto.
    appA2H H10. destruct H11,H11. right. appA2G. exists x1.
    split. eapply Ord_Num_trans; eauto. auto.
    appA2H H4. appA2G. destruct H5. exists a. split; auto.
    appA2G. exists Φ. split. eapply Φ_is_First_Ord; eauto.
    eqext. appA2G. appA2H H6. destruct H7; auto. appA2H H7. destruct H8,H8.
    apply MKT16 in H8. destruct H8.
    appA2H H5. destruct H6,H6. New H6.
    New (trans_Ord_Num a0 x H0 H6). eapply Lim_Ord_1 in H8; eauto.
    exists (a + PlusOne x). assert(x ∈ PlusOne x). appA2G.
    New H9. eapply Lem123 in H11.
    eapply (Add_R_PrOrder_a x (PlusOne x) a) in H10; eauto. split.
    rewrite H7; auto. appA2G. New R_Add_in_R; eauto.
Qed.


(**********************************************************************)
(* 相关示例 *)

(* 交换律不成立 *)

Lemma Add_ω_Property : ∀ m n, m ∈ ω -> n ∈ ω
  -> (PlusOne m) + n = PlusOne (m + n).
Proof.
  intros. generalize dependent n. New MKT138.
  New (trans_Ord_Num ω m H0 H).
  New (@ MKT134 m H). New (trans_Ord_Num ω (PlusOne m) H0 H2).
  apply Mathematical_Induction.
  - rewrite Add_R_Φ_r,Add_R_Φ_r; auto.
  - intros. New (trans_Ord_Num ω k H0 H4).
    rewrite Add_R_Suc,Add_R_Suc; auto.
    rewrite H5; auto.
Qed.

Fact Add_R_nocom : PlusOne Φ + ω <> ω + PlusOne Φ.
Proof.
  New Φ_is_Ord. New ω_is_Lim_Ord. New H0. destruct H1 as [H1 _].
  rewrite Add_R_Suc; eauto. rewrite Add_R_Φ_r; eauto.
  assert( PlusOne Φ + ω = ω ).
  { assert( H': Lim_Ord (PlusOne Φ + ω) /\ PlusOne Φ + ω <> Φ ).
    { New H. apply Lem123 in H2. assert( ω ≠ Φ ). red. intros.
      New MKT135a. rewrite H3 in H4. emf. eapply R_Add_5; eauto. }
    eapply MKT137.
    - red. intros. rewrite Add_R_Lim in H2; eauto.
      appA2H H2. destruct H3,H3. appA2H H4. destruct H5,H5.
      New (trans_Ord_Num ω x0 H1 H5).
      rewrite Add_ω_Property in H6; eauto. rewrite Add_R_Φ_l in H6.
      eapply MKT134 in H5. rewrite <- H6 in H5.
      eapply Ord_Num_trans; eauto. eapply (trans_Ord_Num ω); eauto.
      New Φ_is_Ord. apply Lem123. auto.
      red. intros. New MKT135a. rewrite H3 in H4. emf.
    - destruct H',H2. eapply Φ_is_First_Ord; eauto.
    - destruct H'. intros. New H2. destruct H5 as [H5 _].
      eapply Lim_Ord_1; eauto. }
  rewrite H2. red. intros. eapply MKT27 in H3 as [].
  assert( ω ∈ (PlusOne ω) ). appA2G. apply H4 in H5. NSym.
Qed.
