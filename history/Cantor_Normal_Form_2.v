(* 此版本尝试写f_concat *)

Require Export Sum_Function.
Definition onTo F A B := Function F /\ dom(F) ∈ A /\ ran(F) ⊂ B.
Definition MaxinExp α β:= ∪ \{ λ v, α ^ v ≼ β \}.
Definition Monodc_f γ := Function γ
  /\ (∀ k1 k2, k1 ∈ dom(γ) /\ k2 ∈ dom(γ) /\ k1 ≺ k2 -> γ [k2] ≺ γ [k1]).

Definition f α γ δ := \{\ λ u v, u ∈ dom(γ) /\ v = α ^ γ[u] ⋅ δ[u] \}\.
Definition f_Φ x := \{\ λ u v, u = Φ /\ v = x \}\.
Definition f' a b := \{\ λ u v, u ∈ PlusOne dom(b) /\
                       ((u = Φ /\ v = a) \/ (u ≠ Φ /\ v = b[∪u])) \}\.

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
  - assert( L: ∀ c, a ^ c ≼ b -> Ordinal_Number c ).
    { intros. destruct H3. eapply trans_Ord_Num,R_Exp_in_R' in H3; eauto.
      subst b. eapply R_Exp_in_R' in H0; eauto. }
    New (MiEisO a b H H0 H1). apply OrdNum_classic in H3. destruct H3.
    + destruct H3,H3. assert( x ∈ (MaxinExp a b) ). rewrite H4. appA2G.
      appA2H H5. rdeHex. appA2H H7. rewrite H4.
      assert( Ordinal_Number x0 ). auto.
      eapply R_Add_1 in H6; eauto. destruct H6.
      eapply (Exp_R_PrOrder_a _ _ a) in H6; eauto. left. red in H0. ONtrans_eq.
      apply Lem123; auto. subst x0; auto.
    + TF( (MaxinExp a b) = Φ ). rewrite H4. rewrite Exp_R_Φ_r; eauto.
      eapply MKT118; eauto. destruct H3.
      New (R_Exp_in_R _ _ H H3). appA2H H6; auto.
      appA2H H0; auto. red. intros.
      rewrite Exp_R_Lim in H5; eauto. appA2H H5. rdeHex.
      appA2H H7. rdeHex. appA2H H8. rdeHex. appA2H H11.
      subst x. assert( Ordinal_Number x1 ). auto.
      New (R_Exp_in_R a x1 H H9). assert( z ≺ a ^ x1 ). New H10.
      eapply trans_Ord_Num in H14; eauto.
      eapply (Exp_R_PrOrder_a x0 x1 a) in H10; eauto.
      eapply Ord_Num_trans; eauto. red in H0. ONtrans_eq.
Qed.

Lemma CNF_2 : ∀ x, x ∈ R -> Function (f_Φ x) /\ dom(f_Φ x) = PlusOne Φ.
Proof.
  intros. split.
  - split. apply PisRel. intros. appA2H H0. appA2H H1. rdeHex.
    subst. rewrite <- H3 in H2. apply MKT49b in H0. deand.
    apply MKT55 in H2; deand; auto.
  - eqext. appA2H H0. rdeHex. appoA2H H1. deand. appA2G.
    New EnEm. apply MKT19 in H4. right. appA2G.
    appA2H H0. destruct H1. emf. appA2G. exists x. appoA2G.
    appA2H H1. New EnEm. apply MKT19 in H3. apply H2 in H3. subst; auto.
Qed.

Lemma CNF_3 : ∀ α β a b, Ordinal_Number α -> Ordinal_Number β
  -> PlusOne Φ ≺ α -> Ordinal_Number a -> Ordinal_Number b
  -> b ≠ Φ -> b ≺ α -> β = α ^ a ⋅ b
  -> onTo (f_Φ a) ω R /\ Monodc_f (f_Φ a)
  /\ OnTo (f_Φ b) dom(f_Φ a) α /\ (∀k : Class,(f_Φ b) [k] ≠ Φ)
  /\ β = Sum (f α (f_Φ a) (f_Φ b)) Φ.
Proof.
  intros. assert( L1: ∀ z x, Function (f_Φ x) -> z ∈ ran(f_Φ x) -> z = x ).
  { intros. appA2H H8. rdeHex. appoA2H H9. deand; auto. }
  pose proof (CNF_2 _ H2) as []. pose proof (CNF_2 _ H3) as [].
  try repeat (do 2 split; auto). split. rewrite H8. auto.
  red; intros. eapply L1 in H11; subst; eauto.
  split; auto. intros. deand. appA2H H12. rdeHex. appoA2H H14.
  deand. subst. red in H13. emf.
  rewrite H8,H10. split; auto. red; intros. eapply L1 in H11; subst; eauto.
  intros. TF( k ∈ dom(f_Φ b) ). appA2H H11. rdeHex. New H12.
  eapply Property_Fun in H12; eauto. eapply Property_ran,L1 in H13; eauto.
  subst. rewrite H13; auto. eapply MKT69a in H11. rewrite H11; auto.
  red; intros. New EnEm. μ_notset.
  assert( L2: ∀ x, x ∈ R -> (f_Φ x)[Φ] = x ).
  { intros. eqext. appA2H H12. apply H13. appA2G. appoA2G.
    appA2G. intros. appA2H H13. appoA2H H14. deand. subst y; auto. }
  assert( L3: dom(f α (f_Φ a) (f_Φ b)) = PlusOne Φ ).
  { eqext. appA2H H11. rdeHex. appoA2H H12. deand. rewrite H8 in H13. auto.
    appA2G. appA2H H11. destruct H12. emf. appA2H H12. New EnEm.
    apply MKT19,H13 in H14. subst z. exists (α ^ a ⋅ b). appoA2G.
    apply MKT49a; auto. exists R. eapply R_Mult_in_R; eauto.
    eapply R_Exp_in_R; eauto. split. rewrite H8. appA2G.
    eapply L2 in H2,H3. rewrite H2,H3. auto. }
  New H2. New H3. apply L2 in H11,H12. eqext.
  - appA2G. intros. appA2H H14. deand. apply H18 in H15; auto. clear H18.
    subst y. appA2G. intros. appA2H H15. appoA2H H18. deand.
    rewrite H11,H12 in H20. rewrite H20. rewrite <- H6; auto.
    intros. rewrite L3 in H19. New Φ_is_Ord.
    eapply R_Add_2' in H19; eauto. red in H19. emf. eapply Lem123 in H20.
    eapply trans_Ord_Num in H19; eauto. New H19.
    appA2H H22. eapply AxiomIV' in H22. deand. assert( n ∈ PlusOne n ). appA2G.
    eapply (trans_Ord_Num _ _ H19); eauto.
  - appA2H H13. apply H14. clear H14. appA2G.
    do 2 split. eapply PisRel. intros. appoA2H H14. appoA2H H15. deand.
    subst; auto. rewrite L3; auto. split. red. intros.
    appA2H H14. rdeHex. appoA2H H15. deand. subst z0.
    appA2H H16. rdeHex. appoA2H H17. deand. subst x. rewrite H11,H12.
    eapply R_Mult_in_R; eauto. eapply R_Exp_in_R; eauto.
    intros. rewrite H17. eqext. appA2G. intros. appA2H H20. appoA2H H21. deand.
    rewrite H11,H12 in H23. rewrite H23. rewrite <- H6; auto.
    appA2H H19. apply H20. appA2G. appoA2G. rewrite H8,H11,H12. split; auto.
    appA2G.
Qed.

Lemma CNF_4 : ∀ a b, a ∈ R -> onTo b ω R
  -> Function (f' a b) /\ dom(f' a b) = PlusOne dom(b) /\ ran(f' a b) ⊂ R.
Proof.
  intros. try repeat split. apply PisRel.
  - intros. appA2H H1. appA2H H2. rdeHex. eapply MKT49b in H1,H2; eauto.
    eapply MKT55 in H3,H4; try deand; eauto. subst.
    try (destruct H8,H6; deand; subst; try contradiction; auto).
  - eqext. appA2H H1. rdeHex. appoA2H H2. deand. auto.
    appA2G. TF( z = Φ ). exists a. appoA2G. appA2H H. appA2H H1.
    apply MKT49a; auto. exists b[∪z]. appoA2G.
    apply MKT49a; auto. appA2H H1. auto. eapply MKT19,MKT69b; eauto.
    admit.
  - red. intros. appA2H H1. rdeHex. appoA2H H2. deand.
    destruct H4; deand; subst; auto. destruct H0 as [H0 []].
    eapply H6,Property_dm; eauto. admit.
Admitted.

Lemma CNF_5 : ∀ α a b γ δ, onTo γ ω R -> OnTo δ dom(γ) α
  -> Ordinal_Number α -> Ordinal_Number a -> Ordinal_Number b
  -> onTo (f' a γ) ω R /\ OnTo (f' b δ) dom(f' a γ) α
  /\ (∀k : Class,(f' b δ) [k] ≠ Φ) /\ dom(f' a b) = PlusOne dom(b).
Admitted.

Lemma CNF_6 : ∀ α γ δ, Ordinal_Number α -> PlusOne Φ ≺ α
  -> onTo γ ω R -> onTo δ ω R
  -> onTo (f α γ δ) ω R.
Proof.
(*   intros. repeat split. eapply PisRel.
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
    rewrite H4; auto. *)
Admitted.

Theorem CNF : ∀ α β, Ordinal_Number α -> Ordinal_Number β
  -> PlusOne Φ ≺ α -> PlusOne Φ ≼ β
  -> ∃ γ δ n, onTo γ ω R /\ Monodc_f γ
  /\ OnTo δ dom(γ) α /\ ( ∀ k, δ[k] ≠ Φ )
  /\ n ∈ dom(γ) /\ β = Sum (f α γ δ) n.
Proof.
  intros. generalize dependent β.
  eapply (R_Transfinite_Induction
  (fun x => PlusOne Φ ≼ x ->
      ∃ γ δ n, onTo γ ω R /\ Monodc_f γ
    /\ OnTo δ dom(γ) α /\ ( ∀ k, δ[k] ≠ Φ )
    /\ n ∈ dom(γ) /\ x = Sum (f α γ δ) n)); eauto.
  intro β. intros. destruct H3.
  - (* 1 ≺ β *)
    pose proof (CNF_1 α β H H0 H1) as []. left. auto.
    assert( Ordinal_Number (α ^ MaxinExp α β) ).
    { destruct H5. eapply trans_Ord_Num; eauto. rewrite H5. auto. }
    New (MiEisO α β H H0 H1). destruct H5.
    + (* α ^ MaxinExp α β ∈ β *)
      New (Mult_R_PrOrder_c (α ^ MaxinExp α β) β H6 H0 H4 H5).
      destruct H8,H8. clear H9. deand.
      assert( First x ∈ R ).
      { unfold First. appA2H H8. rdeHex. subst x. rewrite Lemma50b; eauto.
        New H12. appA2H H12. pose proof (MKT44 H12) as [H15 _].
        rewrite H15; auto. }
      assert( L': First x ∈ α ).
      { New (Ord_Num_tri _ _ H11 H). New Φ_is_Ord. destruct H12; eauto.
        assert( α ^ MaxinExp α β ⋅ α ≼ β -> False ).
        { intros. assert (α ^ MaxinExp α β ⋅ α = α ^ MaxinExp α β ⋅ α ^ (PlusOne Φ)).
          rewrite Exp_R_PlusOneΦ_r; eauto. rewrite H15 in H14. New H13.
          apply Lem123 in H16. rewrite <- Exp_R_Distri in H14; eauto.
          rewrite Add_R_Suc,Add_R_Φ_r in H14; eauto.
          assert( (MaxinExp α β) ∈ (MaxinExp α β) ).
          { appA2G. exists (PlusOne(MaxinExp α β)). split. appA2G. appA2G. }
          NSym. }
        New (R_Mult_in_R _ _ H6 H). destruct H12. rewrite H12 in H10. elim H14.
        New Φ_is_First_Ord. TF( Second x = Φ ).
        rewrite H17,Add_R_Φ_r in H10; try eapply R_Mult_in_R; eauto.
        right. auto. New (trans_Ord_Num _ _ H6 H9).
        eapply H16 in H17; eauto.
        eapply (Add_R_PrOrder_a _ _ (α ^ MaxinExp α β ⋅ α)) in H17; eauto.
        rewrite Add_R_Φ_r in H17; try left; try rewrite <- H10 in H17; auto.
        New H12. eapply Mult_R_PrOrder_c in H16; try left; eauto.
        destruct H16 as [c[H16 _]]. deand. rewrite H18 in H10.
        New H17. apply trans_Ord_Num in H19; auto.
         assert( First c ≠ Φ ).
        { red. intros. rewrite H20,Mult_R_Φ_r,Add_R_Φ_l in H18; eauto.
          rewrite H18 in H12. eapply Ord_Num_antisym in H12; eauto. }
        assert( (First c) ∈ R ).
        { unfold First. appA2H H16. rdeHex. subst c.
          rewrite Lemma50b; eauto. New H22. appA2H H21.
          pose proof (MKT44 H21) as [H25 _]. rewrite H25; auto. }
        rewrite Mult_R_Distri in H10; try eapply R_Mult_in_R; eauto.
        rewrite <- Mult_R_Association in H10; eauto. elim H14.
        assert( (α ^ MaxinExp α β ⋅ α) ⋅ First c ≼ β ).
        { set( a' := α ^ MaxinExp α β ). rewrite H10. unfold a'.
          apply (R_Mult_in_R _ _ H6) in H19; eauto. apply trans_Ord_Num in H9; auto.
          apply (R_Mult_in_R _ _ H15) in H21; eauto. rewrite Add_R_Association; eauto.
          eapply R_Add_3',R_Add_in_R; eauto. }
        assert( α ^ MaxinExp α β ⋅ α ≼  (α ^ MaxinExp α β ⋅ α) ⋅ First c ) as [].
        { New (Φ_is_First_Ord _ H21 H20). New (R_Mult_in_R _ _ H6 H).
          eapply R_Add_1 in H23; try apply Φ_is_Ord; eauto. destruct H23.
          eapply (Mult_R_PrOrder _ _ _ _ _ H24) in H23; eauto.
          rewrite Mult_R_PlusOneΦ in H23; try left; auto. red. intros.
          apply (Mult_R_PrOrder_a _ _ _ (Lem123 _ H13) H H6) in H1; eauto.
          rewrite H26 in H1. red in H1. emf. red. intros.
          rewrite H27 in H9. red in H9. emf. rewrite <- H23.
          rewrite Mult_R_PlusOneΦ; try right; auto. }
        left. eapply Ord_Num_trans''; eauto. rewrite H23. auto. }
      TF( Second x = Φ ).
      * New (R_Mult_in_R _ _ H6 H11). rewrite H12,Add_R_Φ_r in H10; auto.
        clear H8 H9 H12 H13. exists (f_Φ (MaxinExp α β)), (f_Φ (First x)), Φ.
        New H. eapply (CNF_3 α β (MaxinExp α β) (First x)) in H8; eauto. deand.
        try repeat (split; auto). pose proof (CNF_2 _ H7) as [_].
        rewrite H15. appA2G. red. intros. rewrite H9,Mult_R_Φ_r in H10; eauto.
        rewrite H10 in H3. emf.
      * assert( Second x ≺ β ). eapply Ord_Num_trans; eauto.
        assert( PlusOne Φ ≼ Second x ).
        { New (trans_Ord_Num _ _ H6 H9). New (Φ_is_First_Ord _ H14 H12).
          eapply R_Add_1; eauto. apply Φ_is_Ord. }
        apply H2 in H13; auto. destruct H13 as [γ [δ [n]]]. deand.
        rewrite H19 in H9,H10,H12. clear H14 H19.
        (* γ' := f' (MaxinExp α β) γ; δ' := f' (First x) δ. *)
        exists (f' (MaxinExp α β) γ), (f' (First x) δ), (PlusOne n).

        New H13. eapply (CNF_5 α (MaxinExp α β) (First x) γ δ) in H14; eauto.
        assert( onTo δ ω R ). admit.
        eapply (CNF_6 α γ δ) in H19; eauto.
                deand. split; [auto |(split; [ |try repeat (split; auto)]) ].
        -- admit.
        -- eapply (CNF_4 _ γ) in H7 as [_ [H7]]; eauto. rewrite H7. admit.
        --
              assert( (f α (f' (MaxinExp α β) γ) (f' (First x) δ))[Φ]
                = α ^ MaxinExp α β ⋅ First x ).
              { assert( L: Φ ∈ PlusOne dom(γ) ).
                { eapply Φ_is_First_Ord; try eapply Lem123,
                   (trans_Ord_Num _ _ MKT138); eauto. admit. admit. }
                assert( ∀ a b, a ∈ R -> (f' a b)[Φ] = a ).
                { intros. eqext. appA2H H24. apply H25. appA2G. admit.
                  appA2G. intros. appA2H H25. appoA2H H26.
                  deand. destruct H28; deand; try contradiction; try subst; auto. }
                New (H23 _ γ (MiEisO _ _ H H0 H1)). New (H23 _ δ H11).
                eqext. appA2H H26. apply H27. clear H27.
                New (R_Mult_in_R _ _ H6 H11). appA2G. appoA2G. split. admit.
                rewrite H24,H25. auto. appA2G. intros. appA2H H27. appoA2H H28.
                deand. rewrite H30,H24,H25; auto. }
              assert( Sum (f α (f' (MaxinExp α β) γ) (f' (First x) δ)) (PlusOne n) =
                    (f α (f' (MaxinExp α β) γ) (f' (First x) δ)) [Φ] + Sum (f α γ δ) n ).
              { New H19. admit. }

(*  eapply (CNF_6 α (f' (MaxinExp α β) γ) (f' (First x) δ)) in H24;
         try rewrite H26; eauto. New H. assert( L: ran(δ) ⊂ R ).
        { red. intros. apply H21 in H31. eapply trans_Ord_Num; eauto. }
        eapply (CNF_6 α γ δ) in H30; eauto.
        eapply (Sum_Lemma4 (f α (f' (MaxinExp α β) γ) (f' (First x) δ))
         (f α γ δ) n); deand; try rewrite H31; try rewrite H33,H26; eauto.
        intros. assert( ∀ a b n, n ∈ dom(γ) -> OnTo b dom(γ) R
         -> (f' a b)[PlusOne n] = b[n] ).
        { intros. assert( L'': PlusOne n0 ≠ Φ /\ ∪ PlusOne n0 = n0 ).
          { eapply (Ord_Num_trans _ _ _ MKT138) in H36; eauto.
            assert( n0 ∈ PlusOne n0 ). appA2G. split. red. intros.
            rewrite H39 in H38. emf. eapply MKT124; eauto.
            eapply (trans_Ord_Num _ _ MKT138) in H36; eauto. }
          eqext. appA2H H38. apply H39. assert (Ensemble b[n0]).
          exists R. destruct H37 as [H37[]]. eapply H41,Property_dm; eauto.
          rewrite H40; auto. appA2G. appoA2G. split. auto.
          right. deand; split; try rewrite H42; auto.
          appA2G. intros. appA2H H39. appoA2H H40. deand.
          destruct H42; deand. contradiction. rewrite H45,H44; auto. }
        assert( m ∈ dom(γ) ).
        { destruct H35. eapply Ord_Num_trans; eauto.
          eapply (trans_Ord_Num _ _ MKT138); eauto. subst; auto. }
        eqext. appA2G. intros. appA2H H39. appoA2H H40. deand. appA2H H38.
        apply H43. appA2G. appA2G. exists m,y. do 2 (split; auto).
        rewrite H42,(H36 (MaxinExp α β) γ m),(H36 (First x) δ m);
        try (split; auto); eauto. appA2H H38. apply H39. clear H39.
        New H37. rewrite <- H31 in H39. New H39.
        eapply Property_Value in H39; eauto. appoA2H H39. eapply MKT49b in H39.
        deand. appA2G. appoA2G. split. rewrite H26. auto.
        rewrite H42,(H36 (MaxinExp α β) γ m),(H36 (First x) δ m);
        try (split; auto); eauto. } *)
      rewrite H24,H23. auto.
    + (* α ^ MaxinExp α β = β *)
      (* γ := f_Φ (MaxinExp α β), δ := f_Φ (PlusOne Φ) *)
      exists (f_Φ (MaxinExp α β)), (f_Φ (PlusOne Φ)), Φ.
      symmetry in H5. rewrite <- (Mult_R_PlusOneΦ _ H6) in H5.
      eapply CNF_3 in H5; eauto. deand.
      try repeat (split; auto). pose proof (CNF_2 _ H7) as [_].
      rewrite H12. appA2G. eapply (trans_Ord_Num _ _ H0); eauto.
      red. intros. assert( Φ ∈ PlusOne Φ ). appA2G. rewrite H8 in H9. NSym.
  - (* γ := f_Φ Φ, δ := f_Φ (PlusOne Φ) *)
    exists (f_Φ Φ), (f_Φ (PlusOne Φ)), Φ. New Φ_is_Ord.
    assert( α ^ Φ ⋅ (PlusOne Φ) = PlusOne Φ ).
    { rewrite Exp_R_Φ_r,Mult_R_PlusOneΦ; try eapply Lem123; auto. }
    rewrite <- H5 in H3. symmetry in H3. clear H5.
    eapply CNF_3 in H3; eauto. deand.
    try repeat (split; auto). pose proof (CNF_2 _ H4) as [_].
    rewrite H9. appA2G. eapply Lem123; eauto.
    red. intros. assert( Φ ∈ PlusOne Φ ). appA2G. rewrite H5 in H6. NSym.
Admitted.