Require Export OrdinalNum.Sum_Function.

(* 
   定义说明:
   onTo F A B: 函数 F 从 A 映射到 B。
   MaxinExp α β: 给定底数 α 和数值 β，最大的指数 v 使得 α^v ≤ β。
   Monodc_f: 单调递减函数 (Monotonically Decreasing)。
   f: 构造序列项的函数，每一项为 α^{γ[u]} * δ[u]。
   f_Φ: 单点函数，将 Φ 映射为 x。
*)

Definition onTo F A B : Prop := Function F /\ dom(F) ∈ A /\ ran(F) ⊂ B.

Definition MaxinExp α β := ∪ \{ λ v, α ^ v ≼ β \}.

Definition Monodc_f γ :=  Function γ /\
  (∀ k1 k2, k1 ∈ dom(γ) /\ k2 ∈ dom(γ) /\ k1 ≺ k2 -> γ[k2] ≺ γ[k1]).

Definition f α γ δ := \{\ λ u v, u ∈ dom(γ) /\ v = α ^ γ[u] ⋅ δ[u] \}\.

Definition f_Φ x := \{\ λ u v, u = Φ /\ v = x \}\.

(* ========================= 辅助引理 ========================= *)

(* 引理: MaxinExp 是一个序数 *)
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

(* 引理: 如果 a^c ≤ b，则 c 是序数 *)
Lemma ONpreceq : ∀ a b c, Ordinal_Number a -> Ordinal_Number b -> a ^ c ≼ b
  -> Ordinal_Number c.
Proof.
  intros. destruct H1. eapply trans_Ord_Num in H1; eauto.
  eapply R_Exp_in_R' in H1; eauto. subst b. eapply R_Exp_in_R' in H0; eauto.
Qed.

(* 引理 CNF_1: MaxinExp 的性质，确保 a^Max ≤ b *)
Lemma CNF_1 : ∀ a b, Ordinal_Number a -> Ordinal_Number b -> PlusOne Φ ≺ a
  -> PlusOne Φ ≼ b -> PlusOne Φ ≼ a ^ (MaxinExp a b) /\ a ^ (MaxinExp a b) ≼ b.
Proof.
  intros. split.
  - TF ((MaxinExp a b) = Φ). 
    + rewrite H3, Exp_R_Φ_r; auto. right. auto.
    + New H1. eapply MiEisO in H4; eauto. apply Φ_is_First_Ord in H3; auto.
      eapply (Exp_R_PrOrder_a _ _ a) in H3; eauto.
      rewrite Exp_R_Φ_r in H3; auto. left; auto. apply Φ_is_Ord.
  - New (MiEisO a b H H0 H1). apply OrdNum_classic in H3. destruct H3.
    + destruct H3, H3. assert (x ∈ (MaxinExp a b)). { rewrite H4. appA2G. }
      appA2H H5. rdeHex. appA2H H7. rewrite H4.
      assert (Ordinal_Number x0). { eapply (ONpreceq a b); eauto. }
      eapply R_Add_1 in H6; eauto. destruct H6.
      eapply (Exp_R_PrOrder_a _ _ a) in H6; eauto. left. red in H0. ONtrans_eq.
      apply Lem123; auto. subst x0; auto.
    + TF ((MaxinExp a b) = Φ).
      * rewrite H4. rewrite Exp_R_Φ_r; eauto.
      * eapply MKT118; eauto. destruct H3. New (R_Exp_in_R _ _ H H3).
        appA2H H6; auto. appA2H H0; auto. red. intros.
        rewrite Exp_R_Lim in H5; eauto. appA2H H5. rdeHex. appA2H H7. rdeHex.
        appA2H H8. rdeHex. appA2H H11. subst x. assert( Ordinal_Number x1 ).
        eapply (ONpreceq a b); eauto. New (R_Exp_in_R a x1 H H9).
        assert( z ≺ a ^ x1 ). New H10. eapply trans_Ord_Num in H14; eauto.
        eapply (Exp_R_PrOrder_a x0 x1 a) in H10; eauto.
        eapply Ord_Num_trans; eauto. red in H0. ONtrans_eq.
Qed.

(* 引理 CNF_2: 单点函数的性质 *)
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

(* 引理 CNF_3: 有限情况下的分解 *)
Lemma CNF_3 : ∀ α β a b, Ordinal_Number α -> Ordinal_Number β
  -> PlusOne Φ ≺ α -> Ordinal_Number a -> Ordinal_Number b
  -> b ≠ Φ -> b ≺ α -> β = α ^ a ⋅ b
  -> onTo (f_Φ a) ω R /\ Monodc_f (f_Φ a) /\ OnTo (f_Φ b) (dom(f_Φ a)) α
  /\ (∀ k : Class, (f_Φ b)[k] ≠ Φ) /\ β = Sum (f α (f_Φ a) (f_Φ b)) Φ.
Proof.
  intros. assert (L1: ∀ z x, Function (f_Φ x) -> z ∈ ran(f_Φ x) -> z = x).
  { intros. appA2H H8. rdeHex. appoA2H H9. deand; auto. }

  pose proof (CNF_2 _ H2) as []. pose proof (CNF_2 _ H3) as [].
  try repeat (do 2 split; auto). split. rewrite H8. auto.
  red; intros. eapply L1 in H11; subst; eauto.
  split; auto. intros. deand. appA2H H12. rdeHex. appoA2H H14.
  deand. subst. red in H13. emf.
  rewrite H8, H10. split; auto. red; intros. eapply L1 in H11; subst; eauto.
  intros. TF (k ∈ dom(f_Φ b)). appA2H H11. rdeHex. New H12.
  eapply Property_Fun in H12; eauto. eapply Property_ran, L1 in H13; eauto.
  subst. rewrite H13; auto. eapply MKT69a in H11. rewrite H11; auto.
  red; intros. New EnEm. μ_notset.
  
  assert (L2: ∀ x, x ∈ R -> (f_Φ x)[Φ] = x).
  { intros. eqext. appA2H H12. apply H13. appA2G. appoA2G.
    appA2G. intros. appA2H H13. appoA2H H14. deand. subst y; auto. }
  
  assert (L3: dom(f α (f_Φ a) (f_Φ b)) = PlusOne Φ).
  { eqext. appA2H H11. rdeHex. appoA2H H12. deand. rewrite H8 in H13. auto.
    appA2G. appA2H H11. destruct H12. emf. appA2H H12. New EnEm.
    apply MKT19, H13 in H14. subst z. exists (α ^ a ⋅ b). appoA2G.
    apply MKT49a; auto. exists R. eapply R_Mult_in_R; eauto.
    eapply R_Exp_in_R; eauto. split. rewrite H8. appA2G.
    eapply L2 in H2, H3. rewrite H2, H3. auto. }
    
  New H2. New H3. apply L2 in H11, H12. eqext.
  - appA2G. intros. appA2H H14. deand. apply H18 in H15; auto. clear H18.
    subst y. appA2G. intros. appA2H H15. appoA2H H18. deand.
    rewrite H11, H12 in H20. rewrite H20. rewrite <- H6; auto.
    intros. rewrite L3 in H19. New Φ_is_Ord.
    eapply R_Add_2' in H19; eauto. red in H19. emf. eapply Lem123 in H20.
    eapply trans_Ord_Num in H19; eauto. New H19.
    appA2H H22. eapply AxiomIV' in H22. deand. assert (n ∈ PlusOne n). appA2G.
    eapply (trans_Ord_Num _ _ H19); eauto.
  - appA2H H13. apply H14. clear H14. appA2G.
    do 2 split. eapply PisRel. intros. appoA2H H14. appoA2H H15. deand.
    subst; auto. rewrite L3; auto. split. red. intros.
    appA2H H14. rdeHex. appoA2H H15. deand. subst z0.
    appA2H H16. rdeHex. appoA2H H17. deand. subst x. rewrite H11, H12.
    eapply R_Mult_in_R; eauto. eapply R_Exp_in_R; eauto.
    intros. rewrite H17. eqext. appA2G. intros. appA2H H20. appoA2H H21. deand.
    rewrite H11, H12 in H23. rewrite H23. rewrite <- H6; auto.
    appA2H H19. apply H20. appA2G. appoA2G. rewrite H8, H11, H12. split; auto.
    appA2G.
Qed.

(* 引理 CNF_4: 序列函数 f 的基本性质 *)
Lemma CNF_4 : ∀ α γ δ, Ordinal_Number α -> PlusOne Φ ≺ α
  -> Function γ -> ran(γ) ⊂ R -> Function δ -> dom(δ) = dom(γ) -> ran(δ) ⊂ R
  -> Function (f α γ δ) /\ dom(f α γ δ) = dom(γ) /\ ran(f α γ δ) ⊂ R.
Proof.
  intros. repeat split. eapply PisRel.
  - intros. appoA2H H6. appoA2H H7. deand. subst; auto.
  - eqext. appA2H H6. rdeHex. appoA2H H7. deand. auto.
    appA2G. appA2H H6. rdeHex. exists (α ^ γ[z] ⋅ δ[z]). appoA2G.
    apply MKT49a; auto. assert ((α ^ γ[z] ⋅ δ[z]) ∈ R).
    eapply R_Mult_in_R; eauto. eapply R_Exp_in_R; eauto. apply H2.
    eapply Property_dm, Property_dom; eauto. apply H5.
    eapply Property_dm; eauto. rewrite H4. eapply Property_dom; eauto.
    appA2H H8. auto. split. eapply Property_dom; eauto. auto.
  - red. intros. appA2H H6. rdeHex. appoA2H H7. deand. subst z.
    eapply R_Mult_in_R; eauto. eapply R_Exp_in_R; eauto. apply H2.
    eapply Property_dm; eauto. apply H5. eapply Property_dm; eauto.
    rewrite H4; auto.
Qed.

(* ================================================================= *)
(*                    Cantor Normal Form (主定理)                    *)
(* ================================================================= *)

Theorem CNF : ∀ α β, Ordinal_Number α -> Ordinal_Number β
  -> PlusOne Φ ≺ α -> PlusOne Φ ≼ β
  -> ∃ γ δ n, onTo γ ω R /\ Monodc_f γ /\ OnTo δ (dom(γ)) α /\ (∀ k, δ[k] ≠ Φ)
  /\ n ∈ dom(γ) /\ β = Sum (f α γ δ) n.
Proof.
  intros. generalize dependent β.
  (* 使用超限归纳法对 β 进行证明 *)
  eapply (R_Transfinite_Induction
    (fun x => PlusOne Φ ≼ x ->
      ∃ γ δ n, onTo γ ω R /\ Monodc_f γ /\ 
      OnTo δ (dom(γ)) α /\ (∀ k, δ[k] ≠ Φ) /\ 
      n ∈ dom(γ) /\ x = Sum (f α γ δ) n)); eauto.
      
  intro β. intros. destruct H3.
  - (* Case: 1 ≺ β *)
    pose proof (CNF_1 α β H H0 H1) as []. left. auto.
    assert (Ordinal_Number (α ^ MaxinExp α β)).
    { destruct H5. eapply trans_Ord_Num; eauto. rewrite H5. auto. }
    
    New (MiEisO α β H H0 H1). destruct H5.
    + (* Case: α ^ MaxinExp α β ∈ β (即存在余数) *)
      New (Mult_R_PrOrder_c (α ^ MaxinExp α β) β H6 H0 H4 H5).
      destruct H8, H8. clear H9. deand.

      (* 定义系数 (First x) 和余数 (Second x) *)
      assert (First x ∈ R).
      { unfold First. appA2H H8. rdeHex. subst x. rewrite Lemma50b; eauto.
        New H12. appA2H H12. pose proof (MKT44 H12) as [H15 _].
        rewrite H15; auto. }

      assert (L': First x ∈ α).
      { (* 证明系数小于底数 α *)
        New (Ord_Num_tri _ _ H11 H). New Φ_is_Ord. destruct H12; eauto.
        assert (α ^ MaxinExp α β ⋅ α ≼ β -> False).
        { intros. assert (α ^ MaxinExp α β ⋅ α = α ^ MaxinExp α β ⋅ α ^ (PlusOne Φ)).
          rewrite Exp_R_PlusOneΦ_r; eauto. rewrite H15 in H14. New H13.
          apply Lem123 in H16. rewrite <- Exp_R_Distri in H14; eauto.
          rewrite Add_R_Suc, Add_R_Φ_r in H14; eauto.
          assert ((MaxinExp α β) ∈ (MaxinExp α β)).
          { appA2G. exists (PlusOne (MaxinExp α β)). split. appA2G. appA2G. }
          NSym. }
        New (R_Mult_in_R _ _ H6 H). destruct H12. rewrite H12 in H10. elim H14.
        New Φ_is_First_Ord. TF (Second x = Φ).
        - rewrite H17, Add_R_Φ_r in H10; try eapply R_Mult_in_R; eauto.
          right. auto.
        - New (trans_Ord_Num _ _ H6 H9).
          eapply H16 in H17; eauto.
          eapply (Add_R_PrOrder_a _ _ (α ^ MaxinExp α β ⋅ α)) in H17; eauto.
          rewrite Add_R_Φ_r in H17; try left; try rewrite <- H10 in H17; auto.
        - New H12. eapply Mult_R_PrOrder_c in H16; try left; eauto.
          destruct H16 as [c[H16 _]]. deand. rewrite H18 in H10.
          New H17. apply trans_Ord_Num in H19; auto.
          assert (First c ≠ Φ).
          { red. intros. rewrite H20, Mult_R_Φ_r, Add_R_Φ_l in H18; eauto.
            rewrite H18 in H12. eapply Ord_Num_antisym in H12; eauto. }
          assert ((First c) ∈ R).
          { unfold First. appA2H H16. rdeHex. subst c.
            rewrite Lemma50b; eauto. New H22. appA2H H21.
            pose proof (MKT44 H21) as [H25 _]. rewrite H25; auto. }
          rewrite Mult_R_Distri in H10; try eapply R_Mult_in_R; eauto.
          rewrite <- Mult_R_Association in H10; eauto. elim H14.
          assert ((α ^ MaxinExp α β ⋅ α) ⋅ First c ≼ β).
          { set (a' := α ^ MaxinExp α β). rewrite H10. unfold a'.
            apply (R_Mult_in_R _ _ H6) in H19; eauto. apply trans_Ord_Num in H9; auto.
            apply (R_Mult_in_R _ _ H15) in H21; eauto. rewrite Add_R_Association; eauto.
            eapply R_Add_3', R_Add_in_R; eauto. }
          assert (α ^ MaxinExp α β ⋅ α ≼ (α ^ MaxinExp α β ⋅ α) ⋅ First c) as [].
          { New (Φ_is_First_Ord _ H21 H20). New (R_Mult_in_R _ _ H6 H).
            eapply R_Add_1 in H23; try apply Φ_is_Ord; eauto. destruct H23.
            eapply (Mult_R_PrOrder _ _ _ _ _ H24) in H23; eauto.
            rewrite Mult_R_PlusOneΦ in H23; try left; auto. red. intros.
            apply (Mult_R_PrOrder_a _ _ _ (Lem123 _ H13) H H6) in H1; eauto.
            rewrite H26 in H1. red in H1. emf. red. intros.
            rewrite H27 in H9. red in H9. emf. rewrite <- H23.
            rewrite Mult_R_PlusOneΦ; try right; auto. }
          left. eapply Ord_Num_trans''; eauto. rewrite H23. auto. }
      TF (Second x = Φ).
      * (* 恰好整除的情况 *)
        New (R_Mult_in_R _ _ H6 H11). rewrite H12, Add_R_Φ_r in H10; auto.
        clear H8 H9 H12 H13. exists (f_Φ (MaxinExp α β)), (f_Φ (First x)), Φ.
        New H. eapply (CNF_3 α β (MaxinExp α β) (First x)) in H8; eauto. deand.
        try repeat (split; auto). pose proof (CNF_2 _ H7) as [_].
        rewrite H15. appA2G. red. intros. rewrite H9, Mult_R_Φ_r in H10; eauto.
        rewrite H10 in H3. emf.
      * (* 有非零余数的情况: 利用归纳假设 *)
        assert (Second x ≺ β). eapply Ord_Num_trans; eauto.
        assert (PlusOne Φ ≼ Second x).
        { New (trans_Ord_Num _ _ H6 H9). New (Φ_is_First_Ord _ H14 H12).
          eapply R_Add_1; eauto. apply Φ_is_Ord. }
        apply H2 in H13; auto. destruct H13 as [γ [δ [n]]]. deand.
        rewrite H19 in H9, H10, H12. clear H14 H19.

        (* 构造新的序列函数，将首项与归纳结果拼接 *)
        set (f' a b := \{\ λ u v, u ∈ PlusOne (dom(γ)) /\
                   ((u = Φ /\ v = a) \/ (u ≠ Φ /\ v = b[∪u])) \}\).
        (* γ' := f' (MaxinExp α β) γ; δ' := f' (First x) δ. *)
        exists (f' (MaxinExp α β) γ), (f' (First x) δ), (PlusOne n).

        (* 证明新构造的函数满足CNF条件 *)
        destruct H13 as [H13[]]. destruct H16 as [H16[]].
        assert (L1: ∀ z, z ∈ PlusOne (dom(γ)) -> z ≠ Φ -> ∪ z ∈ dom(γ)).
        { intros. New (trans_Ord_Num _ _ MKT138 H14). New H14.
          eapply MKT134 in H25; eauto. New (Ord_Num_trans _ _ _ MKT138 H22 H25).
          eapply ω_Num_is_Suc_Ord in H26; eauto. destruct H26. deand.
          subst z. rewrite MKT124; auto. eapply R_Add_2'; eauto. }
        assert (L2: ∀ a b, a ∈ R -> b = γ \/ b = δ -> 
                Function (f' a b) /\ dom(f' a b) = PlusOne (dom(γ)) /\ ran(f' a b) ⊂ R).
        { intros. split. split. apply PisRel. intros.
          appA2H H24. appA2H H25. rdeHex. eapply MKT49b in H24, H25; eauto.
          eapply MKT55 in H26, H27; try deand; eauto. subst.
          try (destruct H29, H31; deand; subst; try contradiction; auto).
          split. eqext. appA2H H24. rdeHex. appoA2H H25. deand. auto.
          appA2G. TF (z = Φ). exists a. appoA2G. appA2H H24. appA2H H22.
          apply MKT49a; auto. exists b[∪z]. appoA2G.
          apply MKT49a; auto. appA2H H24. auto. eapply MKT19, MKT69b; eauto.
          apply L1 in H24; eauto. destruct H23. rewrite H23; eauto.
          rewrite H23, H20; eauto. red. intros. appA2H H24. rdeHex. appoA2H H25.
          deand. destruct H27; deand; subst; auto. apply L1 in H26; auto.
          destruct H23; rewrite H23. apply H19, Property_dm; auto.
          rewrite <- H20 in H26. apply Property_dm, H21 in H26; auto.
          eapply (trans_Ord_Num _ _ H); eauto. }

        (* 辅助引理 L3: 域的后继性质 *)
        assert (L3: ∀ z, z ∈ dom(γ) -> PlusOne z ∈ PlusOne (dom(γ))).
        { intros. New (trans_Ord_Num _ _ MKT138 H14).
          apply -> R_Add_2'; eauto. eapply trans_Ord_Num; eauto. }

        (* 应用 L2 获得新构造函数的性质 *)
        New H7. eapply (L2 (MaxinExp α β) γ) in H22; eauto.
        New H11. eapply (L2 (First x) δ) in H23; eauto.
        (* 展开性质并在上下文中清理 *)
        try repeat (deand; split; try repeat (split; try rewrite H26; auto)).
        (* --- 证明部分 1: 单调性 (Monodc_f) --- *)
        intros. deand. pose proof H29 as H'.
        rewrite <- H26 in H28, H29. 
        (* 证明新的 γ' 是单调递减的 *)
        (* 分类讨论 k1, k2 的情况 (是否为 Φ) *)
        appA2H H29. rdeHex. New H31.
        appoA2H H32. destruct H33. destruct H34; deand. 
        (* Case: k1 = Φ (不可能，因为 k1 < k2 且 k2=Φ 的情况已被排除或隐含) *)
        rewrite H34 in H30. red in H30. emf. 
        (* 提取函数值 *)
        eapply Property_Fun in H31; eauto. rewrite <- H31.
        rewrite H35. clear x0 H31 H32 H35. 
        appA2H H28. rdeHex. New H31.
        eapply Property_Fun in H31; eauto. rewrite <- H31. clear H31.
        appoA2H H32. deand. destruct H35; deand; subst.

        (* Case: k1 = Φ, k2 ≠ Φ (比较首项指数与余数首项指数) *)
        apply L1, Property_dm, H19 in H33; eauto.
        eapply (Exp_R_PrOrder_b _ _ α); eauto.
        eapply (Ord_Num_trans' (α ^ γ [∪ k2]) (Sum (f α γ δ) n) _ H6); eauto.

        assert (Φ ∈ dom(γ)).
        { eapply Φ_is_First_Ord; eauto. eapply (trans_Ord_Num _ _ MKT138); eauto.
          red. intros. rewrite H35 in H18. emf. }

        assert (α ^ γ[Φ] ∈ R).
        { eapply R_Exp_in_R; eauto. eapply H19, Property_dm; eauto. }

        assert (Ordinal_Number δ[Φ]).
        { rewrite <- H20 in H35. eapply Property_dm, H21, trans_Ord_Num in H35; eauto. }

        (* 证明余数的首项等于 Sum(Φ) *)
        assert (Sum (f α γ δ) Φ = α ^ γ[Φ] ⋅ δ[Φ]).
        { assert (α ^ γ [Φ] ⋅ δ [Φ] = (f α γ δ) [Φ]).
          { eqext. appA2G. intros. appA2H H39. appoA2H H40. deand; subst; auto.
            appA2H H38. apply H39. clear H39. New (R_Mult_in_R _ _ H36 H37).
            appA2G. appoA2G. }
          eqext. appA2H H39. apply H40. clear H40. New (R_Mult_in_R _ _ H36 H37).
          appA2G. New H20. eapply (CNF_4 _ γ δ H H1 H13 H19 H16) in H41.
          deand; split; auto. split. rewrite H42; auto. split; auto.
          intros. rewrite H47. auto. red. intros. apply H21 in H42.
          eapply (trans_Ord_Num _ _ H) in H42; eauto.
          appA2G. intros. appA2H H40. deand.
          eapply CNF_f in H41 as [h'[H41 _]]; auto. deand.
          apply H44 in H41; auto.
          rewrite H41, H47. rewrite H38 in H39; auto. }
          
        assert (Sum (f α γ δ) Φ ≠ Φ).
        { red. intros. specialize (H17 Φ). New H35. rewrite <- H20 in H40.
          eapply Property_dm, H21, trans_Ord_Num, Φ_is_First_Ord in H40; eauto.
          eapply (Mult_R_PrOrder_a _ _ _ _ H37 H36) in H40; eauto.
          rewrite <- H38 in H40. rewrite H39 in H40. red in H40. emf.
          red. intros. eapply Property_dm, H19 in H35; eauto.
          New (R_Exp_3' _ _ H35 H H1). rewrite H41 in H42. NSym. }
          
        assert (Sum (f α γ δ) Φ ≼ Sum (f α γ δ) n).
        { TF (n = Φ). subst. right; auto.
          set (g := \{\ λ u v, u ∈ ∪ dom(f α γ δ) /\ v = (f α γ δ)[PlusOne u] \}\).
          assert (n ∈ ω). eapply (Ord_Num_trans _ _ _ MKT138 H18 H14); eauto.
          eapply ω_Num_is_Suc_Ord in H41 as [x0[]]; eauto. deand.
          rewrite H42. New H. eapply (CNF_4 α γ δ) in H43 as [H43 []]; eauto.
          
          assert (L_tmp: ∀ z, z ∈ ∪ dom(f α γ δ) -> (f α γ δ)[PlusOne z] ∈ R).
          { intros. appA2H H46. rdeHex. assert (x1 ∈ R).
            rewrite H44 in H48. eapply (Ord_Num_trans _ _ _ MKT138) in H48; eauto.
            eapply (trans_Ord_Num _ _ MKT138); eauto. New H47.
            eapply R_Add_1 in H47; try eapply (trans_Ord_Num x1 z); eauto.
            eapply (Ord_Num_trans' _ _ dom(f α γ δ)) in H47; eauto.
            apply H45, Property_dm; eauto. rewrite H44.
            eapply (trans_Ord_Num _ _ MKT138); eauto. }
          assert (x0 ∈ dom(g)).
          { appA2G. exists (f α γ δ) [PlusOne x0]. appA2H H41. New H18.
            rewrite <- H44 in H47. rewrite H42 in H47.
            eapply Property_dm in H47; eauto. appoA2G.
            split; auto. appA2G. exists n. split. rewrite H42. appA2G.
            rewrite H44. auto. }
          assert (dom(g) = ∪ dom(f α γ δ)).
          { eqext. appA2H H47. rdeHex. appoA2H H48. deand; auto.
            appA2G. exists (f α γ δ) [PlusOne z]. New H47.
            New H47. apply L_tmp in H48. appA2H H48. appA2H H49. rdeHex. appoA2G. }

          assert (Function g).
          { split. eapply PisRel. intros. appA2H H48. appA2H H49.
            rdeHex. eapply MKT49b in H48, H49; eauto.
            eapply MKT55 in H50, H51; try deand; eauto. subst; auto. }

          assert (dom(g) ∈ ω).
          { New H14. eapply ω_Num_is_Suc_Ord in H49 as [x1[]].
            assert (x1 ∈ dom(γ)). rewrite H50. appA2G.
            rewrite H47, H44, H50, MKT124; eauto.
            eapply (Ord_Num_trans _ _ _ MKT138); eauto. red. intros.
            rewrite H50 in H35. emf. }

          assert (ran(g) ⊂ R).
          { red. intros. appA2H H50. rdeHex.
            appoA2H H51. deand. subst. eapply L_tmp; eauto. }
            
          New H43. eapply ((Sum_Lemma4 (f α γ δ)) g x0) in H51; eauto.
          rewrite H51. assert (α ^ γ [Φ] ⋅ δ [Φ] = (f α γ δ) [Φ]).
          { eqext. appA2G. intros. appA2H H53. appoA2H H54.
            deand; rewrite H56; auto. appA2H H52. apply H53.
            New (R_Mult_in_R _ _ H36 H37). appA2G. appoA2G. }
          rewrite H38. rewrite <- H52. eapply R_Add_3'; eauto.
          eapply R_Mult_in_R; eauto. rewrite <- H42 in H51.
          assert (Sum (f α γ δ) n ∈ R).
          { rewrite H10 in H0. eapply R_Add_in_R' in H0; eauto.
            eapply R_Mult_in_R; eauto. }
          rewrite H51 in H53. eapply R_Add_in_R' in H53; eauto.
          rewrite <- H52. eapply R_Mult_in_R; eauto.
          rewrite H44; auto. rewrite H44. rewrite <- H42. auto.
          intros. assert (m ∈ dom(g)).
          { destruct H52; try rewrite H52; auto.
            eapply Ord_Num_trans; eauto.
            eapply (trans_Ord_Num _ _ MKT138); eauto. }
          appA2H H53. rdeHex. New H54. eapply Property_Fun in H54; eauto.
          appoA2H H55. deand. subst; auto. red. intros.
          apply H21 in H44. eapply trans_Ord_Num; eauto. }

        (* 建立指数的大小关系 *)
        assert (α ^ γ[Φ] ≼ α ^ γ[Φ] ⋅ δ[Φ]).
        { assert (PlusOne Φ ≼ δ[Φ]).
          { New (MKT26 δ[Φ]). eapply (MKT118 Φ δ[Φ]) in H41; eauto. destruct H41.
            eapply R_Add_1; try apply Φ_is_Ord; eauto.
            rewrite <- H41 in H38. rewrite Mult_R_Φ_r in H38; eauto.
            contradiction. New Φ_is_Ord. appA2H H43; auto. appA2H H37; auto. }
          destruct H41. eapply (Mult_R_PrOrder_a _ _ _ _ _ H36) in H41; eauto.
          rewrite Mult_R_PlusOneΦ in H41; eauto. left; auto.
          red. intros. rewrite H42, Mult_R_Φ_l in H38. contradiction. auto.
          rewrite <- H41. right. rewrite Mult_R_PlusOneΦ; eauto. }

        assert (α ^ γ [∪ k2] ≼ α ^ γ [Φ]).
        { New H'. eapply (Ord_Num_trans _ _ ω) in H42; try eapply MKT138; eauto.
          eapply ω_Num_is_Suc_Ord in H42; eauto. destruct H42. deand. subst.
          New H42. apply MKT124 in H42. rewrite H42. rewrite H42 in H33.
          New Φ_is_Ord. eapply R_Add_1 in H30; try eapply Lem123; eauto.
          destruct H30. eapply R_Add_2' in H30; eauto. destruct H15.
          left. apply (Exp_R_PrOrder_a _ _ α), H45; eauto.
          apply H19, Property_dm; auto. try repeat (split; auto).
          eapply R_Add_2'; eauto. eapply (trans_Ord_Num _ _ MKT138); eauto.
          rewrite <- H30 in H42. rewrite MKT124 in H42; eauto. rewrite H42.
          right; auto. eapply MKT134; eauto. }

        rewrite H38 in H40. New (trans_Ord_Num _ _ H6 H9). destruct H40.
        eapply Ord_Num_trans' in H40; eauto. left.
        eapply (Ord_Num_trans' _ _ _ H43 H42 H40); eauto.
        rewrite H40 in H41. destruct H41. left.
        eapply (Ord_Num_trans' _ _ _ H43 H42 H41); eauto.
        rewrite H41 in H42. auto.

        (* Case: k1 ≠ Φ, k2 ≠ Φ (递归使用 γ 的单调性) *)
        destruct H15. eapply H36; eauto. do 2 (split; try (eapply L1; eauto)).
        appA2G. exists k1. split; auto. New (MKT134 H14).
        New (Ord_Num_trans _ _ _ MKT138 H32 H37); eauto.
        eapply ω_Num_is_Suc_Ord in H38 as []; eauto. deand. subst.
        rewrite MKT124; eauto. appA2G.
        red. intros. appA2H H28. rdeHex. appoA2H H29. destruct H30.
        destruct H31; deand; subst. auto.
        apply L1 in H30; auto. apply H21, Property_dm; try rewrite H20; auto.

        (* --- 证明部分 2: δ 的性质与求和等式 --- *)
        intros. 
        (* 证明 δ[k] ≠ Φ *)
        TF (k ∈ dom(f' (First x) δ)).
        appA2H H28. rdeHex. New H29. eapply Property_Fun in H30; eauto.
        appoA2H H29. deand. rewrite <- H30. destruct H32; deand; subst; auto.
        red. intros. rewrite H32 in H10. rewrite Mult_R_Φ_r, Add_R_Φ_l in H10; auto.
        rewrite <- H10 in H9. eapply Ord_Num_antisym in H9; auto.
        eapply (trans_Ord_Num _ _ _ H9); eauto.
        eapply MKT69a in H28; eauto. rewrite H28.
        red. intros. New EnEm. μ_notset.

        (* 证明首项为 Leading Term *)
        assert ((f α (f' (MaxinExp α β) γ) (f' (First x) δ))[Φ]
          = α ^ MaxinExp α β ⋅ First x).
        { assert (L_dom: Φ ∈ PlusOne (dom(γ))).
          { eapply Φ_is_First_Ord; try eapply Lem123,
             (trans_Ord_Num _ _ MKT138); eauto. New (MKT135b _ H14).
            red. intros. rewrite H29 in H28. contradiction. }
          assert (∀ a b, a ∈ R -> (f' a b)[Φ] = a).
          { intros. eqext. appA2H H29. apply H30. appA2G. appoA2G.
            appA2G. intros. appA2H H30. appoA2H H31.
            deand. destruct H33; deand; try contradiction; try subst; auto. }
          New (H28 _ γ (MiEisO _ _ H H0 H1)). New (H28 _ δ H11).
          eqext. appA2H H31. apply H32. clear H32.
          New (R_Mult_in_R _ _ H6 H11). appA2G. appoA2G. split. rewrite H26. auto.
          rewrite H29, H30. auto. appA2G. intros. appA2H H32. appoA2H H33.
          deand. rewrite H35, H29, H30; auto. }

        (* --- 最终验证求和等式 --- *)
        assert (Sum (f α (f' (MaxinExp α β) γ) (f' (First x) δ)) (PlusOne n) =
              (f α (f' (MaxinExp α β) γ) (f' (First x) δ)) [Φ] + Sum (f α γ δ) n).
        { New H25. eapply (CNF_4 α (f' (MaxinExp α β) γ) (f' (First x) δ)) in H29;
           try rewrite H26; eauto. New H. assert (L_ran: ran(δ) ⊂ R).
          { red. intros. apply H21 in H31. eapply trans_Ord_Num; eauto. }
          eapply (CNF_4 α γ δ) in H30; eauto.

          (* 使用 Sum_Lemma4 分解求和 *)
          eapply (Sum_Lemma4 (f α (f' (MaxinExp α β) γ) (f' (First x) δ))
           (f α γ δ) n); deand; try rewrite H31; try rewrite H33, H26; eauto.
           
          (* 证明位移性质 *)
          intros. assert (∀ a b n, n ∈ dom(γ) -> OnTo b (dom(γ)) R
           -> (f' a b)[PlusOne n] = b[n]).
          { intros. assert (L_suc: PlusOne n0 ≠ Φ /\ ∪ PlusOne n0 = n0).
            { eapply (Ord_Num_trans _ _ _ MKT138) in H36; eauto.
              assert (n0 ∈ PlusOne n0). appA2G. split. red. intros.
              rewrite H39 in H38. emf. eapply MKT124; eauto.
              eapply (trans_Ord_Num _ _ MKT138) in H36; eauto. }
            eqext. appA2H H38. apply H39. assert (Ensemble b[n0]).
            exists R. destruct H37 as [H37[]]. eapply H41, Property_dm; eauto.
            rewrite H40; auto. appA2G. appoA2G. split. auto.
            right. deand; split; try rewrite H42; auto.
            appA2G. intros. appA2H H39. appoA2H H40. deand.
            destruct H42; deand. contradiction. rewrite H45, H44; auto. }
            
          assert (m ∈ dom(γ)).
          { destruct H35. eapply Ord_Num_trans; eauto.
            eapply (trans_Ord_Num _ _ MKT138); eauto. subst; auto. }
            
          eqext. appA2G. intros. appA2H H39. appoA2H H40. deand. appA2H H38.
          apply H43. appA2G. appA2G. exists m, y. do 2 (split; auto).
          rewrite H42, (H36 (MaxinExp α β) γ m), (H36 (First x) δ m);
          try (split; auto); eauto. appA2H H38. apply H39. clear H39.
          New H37. rewrite <- H31 in H39. New H39.
          eapply Property_Value in H39; eauto. appoA2H H39. eapply MKT49b in H39.
          deand. appA2G. appoA2G. split. rewrite H26. auto.
          rewrite H42, (H36 (MaxinExp α β) γ m), (H36 (First x) δ m);
          try (split; auto); eauto. }
          
        (* 结合等式完成证明 *)
        rewrite H29, H28. auto.

    + (* Case: α ^ MaxinExp α β = β (本身就是幂次) *)
      exists (f_Φ (MaxinExp α β)), (f_Φ (PlusOne Φ)), Φ.
      symmetry in H5. rewrite <- (Mult_R_PlusOneΦ _ H6) in H5.
      eapply CNF_3 in H5; eauto. deand.
      try repeat (split; auto). pose proof (CNF_2 _ H7) as [_].
      rewrite H12. appA2G. eapply (trans_Ord_Num _ _ H0); eauto.
      red. intros. assert (Φ ∈ PlusOne Φ). appA2G. rewrite H8 in H9. NSym.

  - (* Case: β = Φ 或 最小情况 *)
    exists (f_Φ Φ), (f_Φ (PlusOne Φ)), Φ. New Φ_is_Ord.
    assert (α ^ Φ ⋅ (PlusOne Φ) = PlusOne Φ).
    { rewrite Exp_R_Φ_r, Mult_R_PlusOneΦ; try eapply Lem123; auto. }
    rewrite <- H5 in H3. symmetry in H3. clear H5.
    eapply CNF_3 in H3; eauto. deand.
    try repeat (split; auto). pose proof (CNF_2 _ H4) as [_].
    rewrite H9. appA2G. eapply Lem123; eauto.
    red. intros. assert (Φ ∈ PlusOne Φ). appA2G. rewrite H5 in H6. NSym.

(* 解决 Unshelve 留下的目标 *)
Unshelve.
New Φ_is_Ord. eapply Lem123 in H25. auto. auto.
eapply Φ_is_Ord. eapply trans_Ord_Num; eauto. auto. auto.
Qed.