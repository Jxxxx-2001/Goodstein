(* 此版本未限制δ *)

Require Export Sum_Function.

Definition onTo F A B := Function F /\ dom(F) ∈ A /\ ran(F) ⊂ B.
Definition MaxinExp α β:= ∪ \{ λ v, α ^ v ≼ β \}.
Definition Monodc_f γ := Function γ
  /\ (∀ k1 k2, k1 ∈ dom(γ) /\ k2 ∈ dom(γ) /\ k1 ≺ k2 -> γ [k2] ≺ γ [k1]).

Definition f α γ δ := \{\ λ u v, u ∈ dom(γ) /\ v = α ^ γ[u] ⋅ δ[u] \}\.
Definition f_Φ x := \{\ λ u v, u = Φ /\ v = x \}\.

Lemma MiEisO : ∀ a b, Ordinal_Number a -> Ordinal_Number b
  -> PlusOne Φ ≺ a -> Ordinal_Number (MaxinExp a b).
Proof.
  intros. red. unfold MaxinExp. appA2G.
  - apply AxiomVI.
    assert( \{ λ v, a ^ v ≼ b \} ⊂ PlusOne b).
    { red. intros. appA2H H2. assert( Ordinal_Number (a ^ z) ).
      destruct H3. apply trans_Ord_Num in H3; auto.
      rewrite H3; auto. New H4. apply R_Exp_in_R' in H4; auto.
      New H0. apply Lem123 in H6.
      assert( a ^ z ≺ PlusOne b ). destruct H3.
      eapply (Ord_Num_trans _ b); eauto. appA2G. rewrite H3; appA2G.
      New (R_Exp_2 a z H H4 H1). destruct H8.
      eapply Ord_Num_trans; eauto. rewrite H8; auto. }
    eapply MKT33 in H2; eauto.
  - eapply MKT120. red. intros. appA2H H2.
    destruct H3. eapply trans_Ord_Num in H3; eauto.
    eapply R_Exp_in_R' in H3; eauto. subst b.
    apply R_Exp_in_R' in H0; auto.
Qed.

Lemma ONpreceq : ∀ a b c, Ordinal_Number a -> Ordinal_Number b
  -> a ^ c ≼ b -> Ordinal_Number c.
Proof.
  intros. destruct H1. eapply trans_Ord_Num in H1; eauto.
  eapply R_Exp_in_R' in H1; eauto.
  subst b. eapply R_Exp_in_R' in H0; eauto.
Qed.

Lemma CNF_1 : ∀ a b, Ordinal_Number a -> Ordinal_Number b
  -> PlusOne Φ ≺ a -> PlusOne Φ ≼ b
  -> PlusOne Φ ≼ a ^ (MaxinExp a b) /\ a ^ (MaxinExp a b) ≼ b.
Proof.
  intros. split.
  - TF( (MaxinExp a b) = Φ ). rewrite H3,Exp_R_Φ_r; auto. right. auto.
    New H1. eapply MiEisO in H4; eauto.
    apply Φ_is_First_Ord in H3; auto.
    eapply (Exp_R_PrOrder_a _ _ a) in H3; eauto.
    rewrite Exp_R_Φ_r in H3; auto. left; auto. apply Φ_is_Ord.
  - New (MiEisO a b H H0 H1). apply OrdNum_classic in H3. destruct H3.
    + destruct H3,H3. assert( x ∈ (MaxinExp a b) ). rewrite H4. appA2G.
      appA2H H5. rdeHex. appA2H H7. rewrite H4.
      assert( Ordinal_Number x0 ). eapply (ONpreceq a b); eauto.
      eapply R_Add_1 in H6; eauto. destruct H6.
      eapply (Exp_R_PrOrder_a _ _ a) in H6; eauto. left. red in H0. ONtrans_eq.
      apply Lem123; auto. subst x0; auto.
    + TF( (MaxinExp a b) = Φ ). rewrite H4. rewrite Exp_R_Φ_r; eauto.
      eapply MKT118; eauto. destruct H3.
      New (R_Exp_in_R _ _ H H3). appA2H H6; auto.
      appA2H H0; auto. red. intros.
      rewrite Exp_R_Lim in H5; eauto. appA2H H5. rdeHex.
      appA2H H7. rdeHex. appA2H H8. rdeHex. appA2H H11.
      subst x. assert( Ordinal_Number x1 ). eapply (ONpreceq a b); eauto.
      New (R_Exp_in_R a x1 H H9). assert( z ≺ a ^ x1 ). New H10.
      eapply trans_Ord_Num in H14; eauto.
      eapply (Exp_R_PrOrder_a x0 x1 a) in H10; eauto.
      eapply Ord_Num_trans; eauto. red in H0. ONtrans_eq.
Qed.

Lemma CNF_2 : ∀ a, a ∈ R
  -> dom(f_Φ a) = PlusOne Φ /\ onTo (f_Φ a) ω R /\ Monodc_f (f_Φ a).
Proof.
  intros. assert( ∀ x, x ∈ R -> Function (f_Φ x) /\ dom(f_Φ x) = PlusOne Φ ).
  { intros. split.
    - split. apply PisRel. intros. appA2H H1. appA2H H2. rdeHex.
      subst. rewrite <- H4 in H3. apply MKT49b in H1. deand.
      apply MKT55 in H3; deand; auto.
    - eqext. appA2H H1. rdeHex. appoA2H H2. deand. appA2G.
      New EnEm. apply MKT19 in H2. right. appA2G.
      appA2H H1. destruct H2. emf. appA2G. exists x. appoA2G.
      appA2H H2. New EnEm. apply MKT19 in H4. apply H3 in H4. subst; auto. }
  pose proof (H0 a H). deand. try repeat (split; auto).
  rewrite H2. eapply MKT134,MKT135a; eauto.
  red. intros. appA2H H3. rdeHex. appoA2H H4. deand. subst; auto.
  intros. deand. appA2H H4. rdeHex. appoA2H H6. deand. subst k2. red in H5. emf.
Qed.

Lemma CNF_3 : ∀ α γ δ, Ordinal_Number α -> PlusOne Φ ≺ α
  -> Function γ -> ran(γ) ⊂ R
  -> Function δ -> dom(δ) = dom(γ) -> ran(δ) ⊂ R
  -> Function (f α γ δ) /\ dom(f α γ δ) = dom(γ) /\ ran(f α γ δ) ⊂ R.
Proof.
  intros. repeat split. eapply PisRel.
  - intros. appoA2H H6. appoA2H H7. deand. subst; auto.
  - eqext. appA2H H6. rdeHex. appoA2H H7. deand. auto.
    appA2G. appA2H H6. rdeHex. exists (α ^ γ[z] ⋅ δ[z]). appoA2G.
    apply MKT49a; auto. assert( (α ^ γ [z] ⋅ δ [z]) ∈ R ).
    eapply R_Mult_in_R; eauto. eapply R_Exp_in_R; eauto. apply H2.
    eapply Property_dm,Property_dom; eauto. apply H5.
    eapply Property_dm; eauto. rewrite H4. eapply Property_dom; eauto.
    appA2H H8. auto. split. eapply Property_dom; eauto. auto.
  - red. intros. appA2H H6. rdeHex. appoA2H H7. deand. subst z.
    eapply R_Mult_in_R; eauto. eapply R_Exp_in_R; eauto. apply H2.
    eapply Property_dm; eauto. apply H5. eapply Property_dm; eauto.
    rewrite H4; auto.
Qed.

Lemma CNF_4 : ∀  α a b, Ordinal_Number α -> PlusOne Φ ≺ α
  -> a ∈ R -> b ∈ R
  -> Sum (f α (f_Φ a) (f_Φ b)) Φ = α ^ a ⋅ b.
Proof.
  intros. assert( (α ^ a ⋅ b) ∈ R ).
  { eapply R_Mult_in_R; try eapply R_Exp_in_R; eauto. }
  assert( ∀ a, a ∈ R -> (f_Φ a)[Φ] = a ).
  { intros. eqext. appA2H H5. apply H6. appA2G. appoA2G.
    appA2G. intros. appA2H H6. appoA2H H7. deand. subst y; auto. }
  pose proof (H4 a H1). pose proof (H4 b H2).
  pose proof (CNF_2 a H1) as [H7 [H8 _]].
  pose proof (CNF_2 b H2) as [H9 [H10 _]].
  assert( ∀ z, z ∈ dom(f_Φ a) -> z = Φ ).
  { intros. rewrite H7 in H11. appA2H H11. destruct H12. emf.
    New EnEm. appA2H H12. apply MKT19,H14 in H13. auto. }
  destruct H8,H10. deand.
  assert( Function (f α (f_Φ a) (f_Φ b))
    /\ dom(f α (f_Φ a) (f_Φ b)) = dom(f_Φ a)
    /\ ran(f α (f_Φ a) (f_Φ b)) ⊂ R ).
  { eapply CNF_3; eauto. rewrite H7,H9; auto. }
  eqext.
  - appA2H H17. apply H18. clear H18. appA2G.
    try repeat (split; deand; auto). rewrite H18; auto.
    intros. rewrite H23. eqext. appA2G. intros. appA2H H26. appoA2H H27.
    deand. rewrite H29,H5,H6. auto.
    appA2H H25. apply H26. appA2G. appoA2G.
    rewrite H5,H6,H7. split; auto. appA2G.
  - appA2G. intros. appA2H H18. rdeHex. clear H19 H20 H21.
    apply H22 in H16; auto. subst y.
    appA2G. intros. appA2H H16. appoA2H H19. deand. rewrite H21,H5,H6.
    auto. intros. rewrite H23,H7 in H19. appA2H H19.
    destruct H20. emf. eapply AxiomIV' in H19. appA2H H20.
    New EnEm. apply MKT19,H21 in H25.
    assert( n ∈ PlusOne n ). deand. appA2G. rewrite H25 in H26. emf.
Qed.

Theorem CNF : ∀ α β, Ordinal_Number α -> Ordinal_Number β
  -> PlusOne Φ ≺ α -> PlusOne Φ ≼ β
  -> ∃ γ δ n, n ∈ dom(γ) /\ onTo γ ω R /\ onTo δ ω R /\ dom(γ) = dom(δ)
  /\ Monodc_f γ /\ β = Sum (f α γ δ) n.
Proof.
  intros. generalize dependent β.
  eapply (R_Transfinite_Induction
  (fun x => PlusOne Φ ≼ x ->
      ∃ γ δ n, n ∈ dom(γ) /\ onTo γ ω R /\ onTo δ ω R /\ dom(γ) = dom(δ)
     /\ Monodc_f γ /\ x = Sum (f α γ δ) n)); eauto.
  intro β. intros. destruct H3.
  - (* 1 ≺ β *)
    pose proof (CNF_1 α β H H0 H1) as []. left. auto.
    assert( Ordinal_Number (α ^ MaxinExp α β) ).
    { destruct H5. eapply trans_Ord_Num; eauto. rewrite H5. auto. }
    destruct H5.
    + (* α ^ MaxinExp α β ∈ β *)
      New (Mult_R_PrOrder_c (α ^ MaxinExp α β) β H6 H0 H4 H5).
      destruct H7,H7. clear H8. deand.
      assert( (First x) ∈ R ).
      { unfold First. appA2H H7. rdeHex. subst x. rewrite Lemma50b; eauto.
        New H11. appA2H H11. pose proof (MKT44 H11) as [H14 _].
        rewrite H14; auto. }
      TF( Second x = Φ ).
      New (R_Mult_in_R _ _ H6 H10).
      rewrite H11,Add_R_Φ_r in H9; auto. clear H7 H8 H11 H12.
      (* γ := f_Φ (MaxinExp α β), δ := f_Φ (First x) *)
      exists (f_Φ (MaxinExp α β)), (f_Φ (First x)), Φ.
      New (CNF_2 (MaxinExp α β) (MiEisO α β H H0 H1)).
      New (CNF_2 (First x) H10).
      try repeat (split; deand; auto). rewrite H7; auto. appA2G.
      rewrite H7,H8; auto. New (CNF_4 _ _ _ H H1 (MiEisO _ _ H H0 H1) H10).
      rewrite H15; auto.

      assert( Second x ≺ β ). eapply Ord_Num_trans; eauto.
      assert( PlusOne Φ ≼ Second x ).
      { New (trans_Ord_Num _ _ H6 H8). New (Φ_is_First_Ord _ H13 H11).
        eapply R_Add_1; eauto. apply Φ_is_Ord. }
      apply H2 in H12; auto. destruct H12 as [γ [δ [n]]]. deand.

      rewrite H18 in H8,H9,H11. rename H8 into HH. rename H11 into HH'. clear H13 H18.
      set( f' a b := \{\ λ u v, u ∈ PlusOne dom(γ) /\
                 ((u = Φ /\ v = a) \/ (u ≠ Φ /\ v = b[∪u])) \}\ ).
      (* γ' := f' (MaxinExp α β) γ; δ' := f' (First x) δ. *)
      exists (f' (MaxinExp α β) γ), (f' (First x) δ), (PlusOne n).

      assert( L1: ∀ z, z ∈ PlusOne dom(γ) -> z ≠ Φ -> ∪ z ∈ dom(γ) ).
      { intros. destruct H14 as [H14[]].
        New (trans_Ord_Num _ _ MKT138 H13). New H13.
        eapply MKT134 in H13; eauto. New (Ord_Num_trans _ _ _ MKT138 H8 H13).
        eapply ω_Num_is_Suc_Ord in H21; eauto. destruct H21. deand.
        subst z. rewrite MKT124; auto.
        eapply (Add_R_PrOrder_b _ _ (PlusOne Φ)); eauto.
        eapply Lem123,Φ_is_Ord; eauto.
        try repeat rewrite Add_ω_Property,Add_R_Φ_l; eauto.
        assert( x0 ∈ PlusOne x0 ). appA2G.
        eapply (Ord_Num_trans x0 (PlusOne x0) ω MKT138); eauto.
        eapply (Ord_Num_trans (PlusOne x0) (PlusOne dom(γ)) ω MKT138); eauto. }
      assert( L2: ∀ a b, a ∈ R -> onTo b ω R -> dom(b) = dom(γ)
              -> dom(f' a b) = PlusOne dom(γ) /\ onTo (f' a b) ω R ).
      { intros. assert( dom(f' a b) = PlusOne dom(γ) ).
        { eqext. appA2H H18. rdeHex. appoA2H H19. deand. auto.
          appA2G. TF( z = Φ ). exists a. appoA2G. appA2H H18. appA2H H8.
          apply MKT49a; auto. exists b[∪z]. appoA2G.
          apply MKT49a; auto. appA2H H18. auto. exists R.
          destruct H11 as [H11[_ H20]]. eapply H20,Property_dm; eauto.
          rewrite H13. eapply L1; eauto. }
        split; auto. split. split. apply PisRel.
        intros. appA2H H19. appA2H H20.
        rdeHex. eapply MKT49b in H19,H20; eauto.
        eapply MKT55 in H21,H22; try deand; eauto. subst.
        try (destruct H24,H26; deand; subst; try contradiction; auto).
        destruct H11 as [H11[]]; auto.
        split. rewrite H18. eapply MKT134. rewrite <- H13. auto.
        red. intros. appA2H H21. rdeHex.
        appoA2H H22. deand. destruct H24; deand; subst; auto.
        apply H20,Property_dm; auto.
        rewrite H13. eapply L1; eauto. }
      assert( L3: ∀ z, z ∈ dom(γ) -> PlusOne z ∈ PlusOne dom(γ) ).
      { intros. destruct H14 as [H14[]]. New (trans_Ord_Num _ _ MKT138 H11).
        apply -> R_Add_2'; eauto. eapply trans_Ord_Num; eauto. }

      assert(dom(γ) = dom(γ)). auto. symmetry in H16.
      pose proof (L2 (MaxinExp α β) γ (MiEisO _ _ H H0 H1) H14 H8) as [].
      pose proof (L2 (First x) δ H10 H15 H16) as []. clear H8 L2.
      rewrite H11,H18. destruct H13 as [H13[]].
      split. auto. do 4 (split; auto).
    * split. auto. intros. deand. appA2H H21. appA2H H22. rdeHex.
      New (Property_Fun x1 _ k1 H13 H24). New (Property_Fun _ _ k2 H13 H25).
      rewrite <- H27. rewrite <- H26. clear H26 H27.
      appoA2H H24. appA2H H25. rdeHex. eapply MKT49b in H25.
      eapply MKT55 in H27; deand; eauto. subst x2 x3. destruct H29; deand.
      rewrite H27 in H23; red in H23; emf.
      assert( L: ∀ z, z ∈ PlusOne dom(γ) -> z ∈ ω ).
      { intros. rewrite H11 in H8. eapply (Ord_Num_trans _ _ _ MKT138); eauto. }
      destruct H17,H30; deand; subst.

      clear H11 H13 H8 H20 H18 H19. New (L _ H28).
      eapply ω_Num_is_Suc_Ord in H8 as []; eauto. deand; subst.
      rewrite MKT124; eauto. New H28. destruct H14 as [H14[]].
      assert( Ordinal_Number dom(γ) ).
      { eapply (trans_Ord_Num _ _ MKT138); eauto. }
      apply <- R_Add_2' in H11; eauto.
      eapply L1,Property_dm in H28; eauto. clear L1.
      rewrite MKT124 in H28; eauto. eapply (Exp_R_PrOrder_b _ _ α); eauto.
      apply H18; auto. eapply MiEisO; eauto.

      eapply (Ord_Num_trans' (α ^ γ [x0]) (Sum (f α γ δ) n) _ H6); eauto.
      assert( Φ ∈ dom(γ) ).
      { eapply Φ_is_First_Ord; eauto. red. intros. rewrite H20 in H12. emf. }
      assert( α ^ γ[Φ] ∈ R ).
      { eapply R_Exp_in_R; eauto. eapply H18,Property_dm; eauto. }
      assert( Sum (f α γ δ) Φ = α ^ γ[Φ] ⋅ δ[Φ] ).
      { destruct H15 as [H15[]]. assert( Ordinal_Number δ[Φ] ).
        { rewrite <- H16 in H20. eapply Property_dm,H33 in H20; eauto. }
        assert( L': α ^ γ [Φ] ⋅ δ [Φ] = (f α γ δ) [Φ] ).
        { eqext. appA2G. intros. appA2H H36. appoA2H H37. deand; subst; auto.
          appA2H H35. apply H36. clear H36. New (R_Mult_in_R _ _ H29 H34).
          appA2G. appoA2G. }
        eqext. appA2H H35. apply H36. clear H36. New (R_Mult_in_R _ _ H29 H34).
        appA2G. New (CNF_3 _ γ δ H H1 H14 H18 H15 H16 H33). deand. split; auto.
        split. rewrite H38; auto. split; auto. intros. rewrite H43.
        rewrite L'; auto. appA2G. intros. appA2H H36. deand.
        eapply CNF_f in H37 as [h'[H37 _]]; auto. deand. apply H40 in H37; auto.
        rewrite H37,H43. rewrite L' in H35; auto. }
      assert( L': Sum (f α γ δ) Φ ≠ Φ ).
      { admit. }
      assert( Sum (f α γ δ) Φ ≼ Sum (f α γ δ) n ).
      { admit. }
      assert( α ^ γ[Φ] ≼ α ^ γ[Φ] ⋅ δ[Φ] ).
      { assert( PlusOne Φ ≼ δ[Φ] ).
        { New (MKT26 δ[Φ]). assert( Ordinal_Number δ[Φ] ).
          { destruct H15 as [H15[]]. rewrite <- H16 in H20.
            eapply Property_dm,H36 in H20; eauto. }
          eapply (MKT118 Φ δ[Φ]) in H34; eauto. destruct H34.
          eapply R_Add_1; try apply Φ_is_Ord; eauto.
          rewrite <- H34 in H30. rewrite Mult_R_Φ_r in H30; eauto.
          contradiction. New Φ_is_Ord. appA2H H37; auto. appA2H H35; auto. }
        destruct H34. eapply (Mult_R_PrOrder_a _ _ _ _ _ H29) in H34; eauto.
        rewrite Mult_R_PlusOneΦ in H34; eauto. left; auto.
        eapply Property_dm,H18 in H20; eauto. New (R_Exp_3' (γ[Φ]) α H20 H H1).
        red. intros. rewrite H36 in H35. NSym. rewrite <- H34.
        right. rewrite Mult_R_PlusOneΦ; eauto. }
      assert( α ^ γ [x0] ≼ α ^ γ [Φ] ).
      { apply H18 in H28. New (R_Exp_in_R _ _ H H28).
        New (MKT26 x0). eapply (MKT118 Φ x0) in H36; eauto.
        destruct H36. left. eapply Exp_R_PrOrder_a; eauto.
        eapply Property_dm,H18 in H20; eauto. subst; right; auto.
        New Φ_is_Ord. appA2H H38; auto. appA2H H8; auto. }
      rewrite H30 in H33. New(trans_Ord_Num _ _ H6 HH). destruct H33.
      eapply Ord_Num_trans' in H33; eauto. left.
      eapply (Ord_Num_trans' _ _ _ H36 H35 H33); eauto.
      rewrite H33 in H34. destruct H34. left.
      eapply (Ord_Num_trans' _ _ _ H36 H35 H34); eauto.
      rewrite H34 in H35. auto.

      eapply H31; eauto. do 2 (split; try (eapply L1; eauto)).
      appA2G. exists k1. split; auto. New (L _ H26).
      eapply ω_Num_is_Suc_Ord in H29 as []; eauto. deand.
      rewrite H33. rewrite MKT124; eauto. appA2G.
    * assert( (f α (f' (MaxinExp α β) γ) (f' (First x) δ))[Φ]
        = α ^ MaxinExp α β ⋅ First x ).
      { assert( L: Φ ∈ PlusOne dom(γ) ).
        { destruct H14 as [_[H14 _]]. eapply Φ_is_First_Ord; eauto.
          eapply Lem123,(trans_Ord_Num _ _ MKT138); eauto.
          New (MKT135b _ H14). red. intros. rewrite H22 in H21. contradiction. }
        assert( ∀ a b, a ∈ R -> (f' a b)[Φ] = a ).
        { intros. eqext. appA2H H22. apply H23. appA2G. appoA2G.
          appA2G. intros. appA2H H23. appoA2H H24.
          deand. destruct H26; deand; try contradiction; try subst; auto. }
        New (H21 _ γ (MiEisO _ _ H H0 H1)). New (H21 _ δ H10).
        eqext. appA2H H24. apply H25. clear H25.
        New (R_Mult_in_R _ _ H6 H10). appA2G. appoA2G. split. rewrite H11. auto.
        rewrite H22,H23. auto. appA2G. intros. appA2H H25. appoA2H H26.
        deand. rewrite H28,H22,H23; auto. }
      assert( Sum (f α (f' (MaxinExp α β) γ) (f' (First x) δ)) (PlusOne n) =
            (f α (f' (MaxinExp α β) γ) (f' (First x) δ)) [Φ] + Sum (f α γ δ) n ).
      { destruct H19 as [H19[]].
        assert(dom( f' (First x) δ) = dom(f' (MaxinExp α β) γ)).
        rewrite H11. auto. New (CNF_3 _ (f' (MaxinExp α β) γ) (f' (First x) δ)
          H H1 H13 H20 H19 H24 H23). destruct H14 as [H14[]].
        destruct H15 as [H15[]]. New (CNF_3 _ γ δ H H1 H14 H27 H15 H16 H29).
        eapply (Sum_Lemma4 (f α (f' (MaxinExp α β) γ) (f' (First x) δ))
         (f α γ δ) n); deand; try rewrite H31; eauto.
        rewrite H33. auto. rewrite H33,H11; auto. intros.
        assert( ∀ a b n, n ∈ dom(b) -> dom(b) = dom(γ) -> onTo b ω R
         -> (f' a b)[PlusOne n] = b[n] ).
        { intros. assert( L: PlusOne n0 ≠ Φ /\ ∪ PlusOne n0 = n0 ).
          { rewrite H37 in H36. eapply (Ord_Num_trans _ _ _ MKT138) in H36; eauto.
            split. eapply MKT135b in H36; auto.
            eapply (trans_Ord_Num _ _ MKT138) in H36; eauto. eapply MKT124; auto. }
          eqext. appA2H H39. apply H40.
          assert (Ensemble b[n0]). exists R. destruct H38 as [H38[]].
          eapply H42,Property_dm; eauto. appA2G. appoA2G. split.
          rewrite H37 in H36; auto.
          right. deand; split; try rewrite H43; auto.
          appA2G. intros. appA2H H40. appoA2H H41. deand.
          destruct H43; deand. contradiction. rewrite H46,H45; auto. }
        assert( m ∈ dom(γ) ).
        { destruct H35. eapply Ord_Num_trans; eauto.
          eapply (trans_Ord_Num _ _ MKT138); eauto. subst; auto. }
        eqext. appA2G. intros. appA2H H39. appoA2H H40. deand. appA2H H38.
        apply H43. appA2G. appA2G. exists m,y. do 2 (split; auto).
        rewrite H42,(H36 (MaxinExp α β) γ m),(H36 (First x) δ m);
        try (split; auto); eauto. rewrite H16; auto.
        appA2H H38. apply H39. clear H39. New H37. rewrite <- H31 in H39.
        New H39. eapply Property_Value in H39;eauto. appoA2H H39.
        eapply MKT49b in H39. deand. appA2G. appoA2G.
        split. rewrite H11; auto.
        rewrite H42,(H36 (MaxinExp α β) γ m),(H36 (First x) δ m);
        try (split; auto); eauto. rewrite H16; auto. }
      rewrite H22,H21. auto.

    + (* α ^ MaxinExp α β = β *)
      (* γ := f_Φ (MaxinExp α β), δ := f_Φ (PlusOne Φ) *)
      exists (f_Φ (MaxinExp α β)), (f_Φ (PlusOne Φ)), Φ.
      assert( PlusOne Φ ∈ R ). eapply (trans_Ord_Num β _ H0 H3); eauto.
      New (CNF_2 (MaxinExp α β) (MiEisO _ _ H H0 H1)).
      assert( PlusOne Φ ∈ R ). eapply Lem123,Φ_is_Ord; eauto.
      New (CNF_2 (PlusOne Φ) H9). deand. rewrite H8,H10.
      try repeat (split; try appA2G; auto).
      New (CNF_4 _ _ _ H H1 (MiEisO _ _ H H0 H1) H7).
      rewrite H15,Mult_R_PlusOneΦ; auto.
  - (* γ := f_Φ Φ, δ := f_Φ (PlusOne Φ) *)
    exists (f_Φ Φ), (f_Φ (PlusOne Φ)), Φ.
    assert( PlusOne Φ ∈ R ). rewrite H3; auto. New (CNF_2 (PlusOne Φ) H4).
    New (CNF_2 Φ Φ_is_Ord). deand. rewrite H5,H6. try repeat (split; auto).
    appA2G. New (CNF_4 _ _ _ H H1 Φ_is_Ord H4).
    rewrite H11,Exp_R_Φ_r,Mult_R_PlusOneΦ; auto.
Admitted.
