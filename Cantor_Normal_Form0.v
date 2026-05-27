(* 此版本f_shift_r *)

Require Export OrdinalNum.Sum_Function.

(*
   定义说明:
   onTo F A B: 函数 F 从 A 映射到 B。
   MaxinExp α β: 给定底数 α 和数值 β，最大的指数 v 使得 α^v ≤ β。
   Monodc_f: 单调递减函数 (Monotonically Decreasing)。
   f: 构造序列项的函数，每一项为 α^{γ[u]} * δ[u]。
   f_Φ: 单点函数，将 Φ 映射为 x。
   f_shift_r a b 将 Φ 映射为 a，将非 Φ 的 u 映射为 b[u-1]。
*)

Definition onTo F A B := 
  Function F /\ dom(F) ∈ A /\ ran(F) ⊂ B.

Definition MaxinExp α β := ∪ \{ λ v, α ^ v ≼ β \}.

Definition Monodc_f γ := Function γ /\ 
  (∀ k1 k2, k1 ∈ dom(γ) /\ k2 ∈ dom(γ) /\ k1 ≺ k2 -> γ[k2] ≺ γ[k1]).

Definition f α γ δ := \{\ λ u v, u ∈ dom(γ) /\ v = α ^ γ[u] ⋅ δ[u] \}\.

Definition f_Φ x := \{\ λ u v, u = Φ /\ v = x \}\.

Definition f_shift_r f a :=
  \{\ λ u v, u ∈ PlusOne (dom(f)) /\
             ((u = Φ /\ v = a) \/ (u ≠ Φ /\ v = f[∪u])) \}\.

(* ========================= 辅助引理 ========================= *)

Fact com_f_value : ∀ α γ δ, Ordinal_Number α -> PlusOne Φ ≺ α
  -> Function γ -> dom(γ) ∈ ω -> ran(γ) ⊂ R
  -> Function δ -> dom(δ) = dom(γ) -> ran(δ) ⊂ R
  -> (∀ n, n ∈ dom(γ) -> (f α γ δ)[n] = α ^ γ[n] ⋅ δ[n]).
Proof.
  intros. eqext. appA2H H8. apply H9. assert( Ensemble (α ^ γ [n] ⋅ δ [n]) ).
  { exists R. eapply R_Mult_in_R. eapply R_Exp_in_R; eauto.
    apply H3,Property_dm; auto. apply H6,Property_dm; auto. rewrite H5; auto. }
  appA2G. appoA2G. appA2G. intros. appA2H H9. appoA2H H10. destruct H11.
  subst y. auto.
Qed.

Fact cap_pre : ∀ x z, x ∈ ω -> z ∈ PlusOne x -> z ≠ Φ -> ∪ z ∈ x.
Proof.
  intros. New MKT138. pose proof (trans_Ord_Num _ _ H2 H).
  assert( z ∈ ω -> ∪ z ∈x ).
  { intros. eapply ω_Num_is_Suc_Ord in H4 as [z'[]]; eauto. subst z.
    rewrite MKT124; auto. eapply R_Add_2'; eauto. }
  apply H4. eapply R_Add_1 in H as []; eauto.
  eapply Ord_Num_trans in H; eauto. New ω_is_Lim_Ord. destruct H5.
  elim H6. exists x. auto.
Qed.

Fact shift_dom : ∀ f a, Ordinal_Number a -> dom(f) ∈ ω
  -> dom(f_shift_r f a) = PlusOne dom(f).
Proof.
  intros. eqext. appA2H H1. destruct H2. appoA2H H2. destruct H3. auto.
  appA2G. TF( z = Φ ). exists a. appoA2G. eapply MKT49a; eauto.
  exists f0[∪z]. appoA2G. eapply MKT49a; eauto. eapply MKT19,MKT69b.
  eapply cap_pre; eauto.
Qed.

Fact shift_fun : ∀ f a, Ordinal_Number a
  -> Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> Function (f_shift_r f a) /\ dom(f_shift_r f a) ∈ ω /\ ran(f_shift_r f a) ⊂ R.
Proof.
  intros. repeat split. eapply PisRel.
  - intros. appoA2H H3. appoA2H H4. destruct H5,H6.
    destruct H7,H8; deand; try contradiction; try subst; auto.
  - rewrite shift_dom; eauto.
  - red. intros. appA2H H3. rdeHex. appoA2H H4. deand.
    destruct H6; deand; subst; auto. apply H2,Property_dm; auto.
    eapply cap_pre; eauto.
Qed.

Lemma shift_value : ∀ F k a, Ordinal_Number dom(F)
  -> (f_shift_r F a)[PlusOne k] = F[k].
Proof.
  intros. eqext.
  - TF((k) ∈ dom(F)). appA2H H0. apply H2. New H1.
    apply MKT69b in H3; auto.
    appA2G. assert( Ensemble (PlusOne k) ).
    eapply AxiomIV; eauto.
    appoA2G. split. apply -> R_Add_2'; eauto.
    eapply trans_Ord_Num; eauto. right. split.
    red. intro. assert( k ∈ (PlusOne k) ). appA2G.
    rewrite H5 in H6. emf. rewrite MKT124; auto.
    eapply trans_Ord_Num; eauto. apply MKT69a in H1.
    rewrite H1. appA2H H0. auto.
  - appA2G. intros. appA2H H1. appoA2H H2. destruct H3.
    assert( k ∈ (PlusOne k) ).
    { appA2H H3. eapply AxiomIV' in H3 as []. appA2G. }
    destruct H4; deand. rewrite H4 in H5. emf.
    rewrite MKT124 in H6; auto. subst y; auto. appA2H H3.
    destruct H7. eapply trans_Ord_Num in H7; eauto.
    eapply trans_Ord_Num; eauto. appA2H H7. New H. appA2H H.
    apply MKT19,H8 in H. rewrite H in H5. eapply trans_Ord_Num; eauto.
Qed.

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
Lemma ONpreceq : ∀ a b c, 
  Ordinal_Number a -> Ordinal_Number b -> a ^ c ≼ b -> Ordinal_Number c.
Proof.
  intros. destruct H1. eapply trans_Ord_Num in H1; eauto.
  eapply R_Exp_in_R' in H1; eauto. subst b. eapply R_Exp_in_R' in H0; eauto.
Qed.

(* 引理 CNF_1: MaxinExp 的性质，确保 a^Max ≤ b *)
Lemma CNF_1 : ∀ a b, 
  Ordinal_Number a -> Ordinal_Number b -> 
  PlusOne Φ ≺ a -> PlusOne Φ ≼ b -> 
  PlusOne Φ ≼ a ^ (MaxinExp a b) /\ a ^ (MaxinExp a b) ≼ b.
Proof.
  intros. split.
  - TF ((MaxinExp a b) = Φ). 
    + rewrite H3, Exp_R_Φ_r; auto. right. auto.
    + New H1. eapply MiEisO in H4; eauto.
      apply Φ_is_First_Ord in H3; auto.
      eapply (Exp_R_PrOrder_a _ _ a) in H3; eauto.
      rewrite Exp_R_Φ_r in H3; auto. left; auto. apply Φ_is_Ord.
  - New (MiEisO a b H H0 H1). apply OrdNum_classic in H3. destruct H3.
    + destruct H3, H3. 
      assert (x ∈ (MaxinExp a b)). { rewrite H4. appA2G. }
      appA2H H5. rdeHex. appA2H H7. rewrite H4.
      assert (Ordinal_Number x0). { eapply (ONpreceq a b); eauto. }
      eapply R_Add_1 in H6; eauto. destruct H6.
      eapply (Exp_R_PrOrder_a _ _ a) in H6; eauto. 
      left. red in H0. ONtrans_eq.
      apply Lem123; auto. subst x0; auto.
    + TF ((MaxinExp a b) = Φ).
      * rewrite H4. rewrite Exp_R_Φ_r; eauto.
      * eapply MKT118; eauto. destruct H3.
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

(* 引理 CNF_3: 序列函数 f 的基本性质 *)
Lemma CNF_3 : ∀ α γ δ, 
  Ordinal_Number α -> PlusOne Φ ≺ α -> 
  Function γ -> ran(γ) ⊂ R -> 
  Function δ -> dom(δ) = dom(γ) -> ran(δ) ⊂ R -> 
  Function (f α γ δ) /\ dom(f α γ δ) = dom(γ) /\ ran(f α γ δ) ⊂ R.
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

(* 引理 CNF_4: 有限情况下的分解 *)
Lemma CNF_4 : ∀ α β a b, 
  Ordinal_Number α -> Ordinal_Number β -> PlusOne Φ ≺ α -> 
  Ordinal_Number a -> Ordinal_Number b -> 
  b ≠ Φ -> b ≺ α -> β = α ^ a ⋅ b -> 
  onTo (f_Φ a) ω R /\ Monodc_f (f_Φ a) /\ 
  OnTo (f_Φ b) (dom(f_Φ a)) α /\ (∀ k : Class, (f_Φ b)[k] ≠ Φ) /\ 
  β = Sum (f α (f_Φ a) (f_Φ b)) Φ.
Proof.
  intros.
  assert( L1: ∀ x, Function (f_Φ x) -> Ordinal_Number x -> ran(f_Φ x) ⊂ R ).
  { intros. red; intros. appA2H H9. rdeHex. appoA2H H10. deand; subst; auto. }
  pose proof (CNF_2 _ H2) as []. pose proof (CNF_2 _ H3) as [].
  New (L1 _ H7 H2). New (L1 _ H9 H3). clear L1.
  unfold onTo,OnTo,Monodc_f. rewrite H8,H10. try repeat (split; auto).
  - intros. deand. New EnEm. apply MKT19 in H16. appA2H H14. destruct H17. emf.
    appA2H H17. apply H18 in H16. subst. red in H15. emf.
  - red; intros. appA2H H13. rdeHex. appoA2H H14. deand; subst. auto.
  - intros. TF (k ∈ dom(f_Φ b)). appA2H H13. rdeHex. New H14.
    eapply Property_Fun in H15; eauto. appoA2H H14.
    deand; subst x; rewrite <- H15; auto.
    eapply MKT69a in H13. rewrite H13; auto. red; intros. New EnEm. μ_notset.
  - New H. eapply (CNF_3 α (f_Φ a) (f_Φ b)) in H13 as [H13[]]; eauto.
    rewrite Sum_Lemma2; eauto.
    * assert(L1: ∀ x, Ordinal_Number x -> (f_Φ x) [Φ] = x).
      { intros. eqext. appA2H H17. apply H18. appA2G. appoA2G.
        appA2G. intros. appA2H H18. appoA2H H19. deand. subst y; auto. }
      New (L1 _ H2). New (L1 _ H3). rewrite com_f_value; eauto;
        try rewrite H8; auto. rewrite H16,H17. auto. appA2G.
    * rewrite H14,H8. eapply MKT134,MKT135a.
    * rewrite H8,H10; auto.
Qed.

Lemma shift_Sum : ∀ α γ δ n a b, Ordinal_Number α -> PlusOne Φ ≺ α
  -> Ordinal_Number a -> Ordinal_Number b
  -> Function γ -> dom(γ) ∈ ω -> ran(γ) ⊂ R
  -> Function δ -> dom(δ) = dom(γ) -> ran(δ) ⊂ R -> n ∈ dom(γ)
  -> Sum (f α (f_shift_r γ a) (f_shift_r δ b)) (PlusOne n) =
     α ^ a ⋅ b + Sum (f α γ δ) n.
Proof.
  intros. New H. eapply (CNF_3 α γ δ) in H10 as [H10[]]; eauto.
  New H3. eapply (shift_fun γ _ H1) in H13 as [H13[]]; eauto.
  New H4. rewrite <- H7 in H16.
  eapply (shift_fun δ _ H2) in H16 as [H16[]]; eauto. New H13.
  assert( H': dom(f_shift_r γ a) = dom(f_shift_r δ b) ).
  { New (shift_dom γ a H1 H4). rewrite <- H7 in H4.
    eapply (shift_dom δ b H2) in H4. rewrite H4,H20,H7; auto. }
  eapply (CNF_3 α (f_shift_r γ a) (f_shift_r δ b)) in H19 as [H19[]]; eauto.
  assert( H'': α ^ a ⋅ b = (f α (f_shift_r γ a) (f_shift_r δ b))[Φ] ).
  { assert( Φ ∈ dom(γ) ).
    { apply Φ_is_First_Ord. eapply (trans_Ord_Num _ _ MKT138); eauto.
      red. intro. rewrite H22 in H9. emf. }
    rewrite com_f_value; eauto.
    assert( ∀ γ' a', Φ ∈ dom(γ') -> Ensemble a' -> (f_shift_r γ' a')[Φ] = a' ).
    { intros. eqext. appA2H H25. apply H26. appA2G. appoA2G. split; auto.
      appA2G. appA2G. intros. appA2H H26. appoA2H H27.
      destruct H28 as [H28[]]; deand; try contradiction; subst; auto. }
      New H22. eapply (H23 γ a) in H24; eauto. New H22. rewrite <- H7 in H25.
      eapply (H23 δ b) in H25; eauto. rewrite H24,H25; auto.
      New H1. eapply (shift_dom γ a) in H23; eauto. rewrite H23. appA2G. }
  rewrite H''. eapply Sum_Lemma4; try rewrite H20; try rewrite H11; eauto.
  rewrite shift_dom; auto. eapply (trans_Ord_Num _ _ MKT138) in H4; eauto.
  apply -> R_Add_2'; eauto. eapply trans_Ord_Num; eauto.
  intros. assert( m ∈ dom(γ) ).
  { destruct H22; subst; auto. eapply Ord_Num_trans; eauto.
    eapply (trans_Ord_Num _ _ MKT138); eauto. }
  rewrite (com_f_value α (f_shift_r γ a) (f_shift_r δ b)); eauto.
  New H4. eapply (trans_Ord_Num _ _ MKT138) in H4; eauto.
  New (shift_value γ m a H4). rewrite <- H7 in H4.
  New (shift_value δ m b H4). rewrite H25,H26. eapply com_f_value; eauto.
  New (shift_dom γ a H1 H4). rewrite H24.
  eapply (trans_Ord_Num _ _ MKT138) in H4; eauto.
  apply -> R_Add_2'; auto. apply trans_Ord_Num in H23; auto.
Qed.

(* 单调性证明 *)
Lemma shift_Monodc : ∀ f a, a ∈ R -> onTo f ω R -> Monodc_f f -> f[Φ] ≺ a
  -> let F := f_shift_r f a in Monodc_f F.
Proof.
  intros. destruct H0 as [H0[]]. assert( Function F ).
  { New H0. eapply (shift_fun f0 a) in H5 as [H5[]]; eauto. }
  split; auto. intros. deand.
  appA2H H7. rdeHex. New H9. eapply Property_Fun in H10; auto.
  appA2H H9. rdeHex. eapply MKT49b in H9 as [_ H9].
  eapply MKT55 in H11 as []; eauto. subst x0 x x1.
  destruct H13; deand. rewrite H10 in H8. red in H8. emf.
  appA2H H6. rdeHex. New H13. eapply Property_Fun in H14; auto.
  appA2H H13. rdeHex. eapply MKT49b in H13 as [_ H13].
  eapply MKT55 in H15 as []; eauto. subst x0 x x1. destruct H1.
  New H12. eapply (cap_pre dom(f0) k2) in H15; eauto.
  destruct H17; deand; rewrite H18,H11.
  - assert( Φ ∈ dom(f0) ).
    { eapply Φ_is_First_Ord. eapply (trans_Ord_Num _ _ MKT138); eauto.
      red. intros. rewrite H19 in H15. emf. }
    assert( f0[∪k2] ≼ f0[Φ] ). New (MKT26 (∪k2)).
    apply -> MKT118 in H20; eauto. destruct H20. left. eapply H14; eauto.
    right. rewrite H20; auto. eapply (trans_Ord_Num _ _ MKT138) in H3; eauto.
    eapply trans_Ord_Num in H15; eauto. appA2H H15; auto.
    New Φ_is_Ord. appA2H H21. auto. destruct H20.
    eapply Ord_Num_trans; eauto. rewrite H20; auto.
  - New H3. eapply (cap_pre dom(f0) k1) in H19; eauto. eapply H14; eauto.
    do 2 (split; auto). appA2G. exists k1. split; auto. New (MKT134 H3).
    New (Ord_Num_trans _ _ _ MKT138 H16 H20); eauto.
    eapply (cap_pre k1 k1) in H21; eauto. appA2G.
Qed.

Lemma Sum_Monodc : ∀ α γ δ n, Ordinal_Number α -> PlusOne Φ ≺ α
  -> onTo γ ω R -> OnTo δ (dom(γ)) α -> n ∈ dom(γ) -> Sum (f α γ δ) n ∈ R
  -> α ^ γ [Φ] ⋅ δ [Φ] ≼ Sum (f α γ δ) n.
Proof.
  intros. destruct H1 as [H1[]]. destruct H2 as [H2[]].
  assert (Φ ∈ dom(γ)).
  { eapply Φ_is_First_Ord; eauto. eapply (trans_Ord_Num _ _ MKT138); eauto.
    red. intros. rewrite H9 in H3. emf. }
  assert( ran(δ) ⊂ R ).
  { red. intros. apply H8 in H10. apply (trans_Ord_Num _ _ H); auto. }
  assert( α ^ γ [Φ] ⋅ δ [Φ] ∈ R ).
  { eapply R_Mult_in_R. eapply R_Exp_in_R; eauto.
    eapply H6, Property_dm; eauto. rewrite <- H7 in H9.
    eapply H10, Property_dm; eauto. }
  assert( (f α γ δ)[Φ] = α ^ γ[Φ] ⋅ δ[Φ] ).
  { eqext. appA2H H12. apply H13. appA2G. appoA2G. appA2G. intros.
    appA2H H13. appoA2H H14. deand; subst; auto. }
  TF (n = Φ). subst. right. eqext. appA2G. intros. appA2H H14. deand.
  eapply CNF_f in H15 as [h'[H15 _]]; auto. deand. apply H18 in H15; auto.
  rewrite H15,H21,H12. auto. appA2H H13. apply H14. appA2G. clear H14.
  New H. eapply (CNF_3 α γ δ) in H14 as [H14 []]; eauto. rewrite H15.
  do 3 (split; auto). intros. rewrite H20,H12; auto.

  set (g := \{\ λ u v, u ∈ ∪ dom(f α γ δ) /\ v = (f α γ δ)[PlusOne u] \}\).
  assert (n ∈ ω). eapply (Ord_Num_trans _ _ _ MKT138 H3 H5); eauto.
  eapply ω_Num_is_Suc_Ord in H14 as [x[]]; eauto.
  rewrite H15. New H. eapply (CNF_3 α γ δ) in H16 as [H16 []]; eauto.
  assert( x ∈ dom(g) ).
  { appA2G. exists (f α γ δ)[PlusOne x]. appA2H H14. New H3.
    rewrite <- H17 in H20. rewrite H15 in H20.
    eapply Property_dm in H20; eauto. appoA2G. split; auto. appA2G.
    exists n. split. rewrite H15. appA2G. rewrite H17. auto. }
  assert( ∀ z, z ∈ ∪ dom(f α γ δ) -> (f α γ δ)[PlusOne z] ∈ R ).
  { intros. appA2H H20. rdeHex. eapply (trans_Ord_Num _ _ MKT138) in H5; eauto.
    assert( x0 ∈ R ). rewrite H17 in H22. eapply (trans_Ord_Num _ _ H5); eauto.
    New H21. eapply R_Add_1 in H21; try eapply (trans_Ord_Num x0 z); eauto.
    eapply (Ord_Num_trans' _ _ dom(f α γ δ)) in H22; eauto.
    apply H18,Property_dm; eauto. rewrite H17. auto. }
  assert( dom(g) = ∪dom(f α γ δ) ).
  { eqext. appA2H H21. rdeHex. appoA2H H22. deand; auto. appA2G.
    exists (f α γ δ)[PlusOne z]. New H21. apply H20 in H21. appA2G.
    eapply MKT49a; eauto. }
  assert( Function g ).
  { split. eapply PisRel. intros. appA2H H22. appA2H H23. rdeHex.
    eapply MKT49b in H22,H23; eauto. eapply MKT55 in H24,H25;
    try deand; eauto. subst; auto. }
  assert( dom(g) ∈ ω ).
  { New H5. eapply ω_Num_is_Suc_Ord in H23 as [x1[]]. assert( x1 ∈ dom(γ) ).
    rewrite H24. appA2G. rewrite H21,H17,H24,MKT124; eauto.
    eapply (Ord_Num_trans _ _ _ MKT138); eauto. intro. rewrite H24 in H3. emf. }
  assert( ran(g) ⊂ R ).
  { red. intros. appA2H H24. rdeHex. appoA2H H25. deand. subst. eapply H20; eauto. }

  New H22. eapply ((Sum_Lemma4 (f α γ δ)) g x) in H25;
   try rewrite H17; try rewrite <- H15; eauto. rewrite <- H15 in H25.
  rewrite H12 in H25. rewrite H25. eapply R_Add_3'; eauto.
  rewrite H25 in H4. eapply R_Add_in_R' in H4; eauto.
  intros. assert (m ∈ dom(g)).
  { destruct H26; try rewrite H26; auto. eapply Ord_Num_trans; eauto.
    eapply (trans_Ord_Num _ _ MKT138); eauto. }
  appA2H H27. rdeHex. New H28. eapply Property_Fun in H28; eauto.
  appoA2H H29. deand. subst; auto.
Qed.


(* Lemma Sum_Monodc : ∀ α γ δ n, Ordinal_Number α -> PlusOne Φ ≺ α
  -> onTo γ ω R -> OnTo δ (dom(γ)) α -> n ∈ dom(γ) -> Sum (f α γ δ) n ∈ R
  -> Sum (f α γ δ) Φ ≼ Sum (f α γ δ) n.
Proof.
  intros. TF (n = Φ). subst. right; auto.
  set (g := \{\ λ u v, u ∈ ∪ dom(f α γ δ) /\ v = (f α γ δ)[PlusOne u] \}\).
  destruct H1 as [H1[]]. destruct H2 as [H2[]].
  assert (n ∈ ω). eapply (Ord_Num_trans _ _ _ MKT138 H3 H6); eauto.
  eapply ω_Num_is_Suc_Ord in H10 as [x[]]; eauto.
  rewrite H11. New H. assert( H_0: ran(δ) ⊂ R ).
  { red. intros. apply H9 in H13. apply (trans_Ord_Num _ _ H); auto. }
  eapply (CNF_3 α γ δ) in H12 as [H12 []]; eauto.

  assert( H_1: x ∈ dom(g) ).
  { appA2G. exists (f α γ δ)[PlusOne x]. appA2H H10. New H3.
    rewrite <- H13 in H16. rewrite H11 in H16.
    eapply Property_dm in H16; eauto. appoA2G. split; auto. appA2G.
    exists n. split. rewrite H11. appA2G. rewrite H13. auto. }
  assert( H_2: ∀ z, z ∈ ∪ dom(f α γ δ) -> (f α γ δ)[PlusOne z] ∈ R ).
  { intros. appA2H H15. rdeHex. eapply (trans_Ord_Num _ _ MKT138) in H6; eauto.
    assert( x0 ∈ R ). rewrite H13 in H17. eapply (trans_Ord_Num _ _ H6); eauto.
    New H16. eapply R_Add_1 in H19; try eapply (trans_Ord_Num x0 z); eauto.
    eapply (Ord_Num_trans' _ _ dom(f α γ δ)) in H19; eauto.
    apply H14, Property_dm; eauto. rewrite H13. auto. }
  assert( H_3: dom(g) = ∪dom(f α γ δ) ).
  { eqext. appA2H H15. rdeHex. appoA2H H16. deand; auto. appA2G.
    exists (f α γ δ)[PlusOne z]. New H15. apply H_2 in H15. appA2G.
    eapply MKT49a; eauto. }

  assert( Function g ).
  { split. eapply PisRel. intros. appA2H H15. appA2H H16. rdeHex.
    eapply MKT49b in H15,H16; eauto.
    eapply MKT55 in H17,H18; try deand; eauto. subst; auto. }
  assert( dom(g) ∈ ω ).
  { New H6. eapply ω_Num_is_Suc_Ord in H16 as [x1[]]. assert( x1 ∈ dom(γ) ).
    rewrite H17. appA2G. rewrite H_3,H13,H17,MKT124; eauto.
    eapply (Ord_Num_trans _ _ _ MKT138); eauto.
    red. intro. rewrite H17 in H3. emf. }
  assert( ran(g) ⊂ R ).
  { red. intros. appA2H H17. rdeHex. appoA2H H18. deand. subst. eapply H_2; eauto. }

  New H12. eapply ((Sum_Lemma4 (f α γ δ)) g x) in H18;
   try rewrite H13; try rewrite <- H11; eauto. rewrite H11,H18.

  assert (Φ ∈ dom(γ)).
  { eapply Φ_is_First_Ord; eauto. eapply (trans_Ord_Num _ _ MKT138); eauto.
    red. intros. rewrite H19 in H3. emf. }
  assert( α ^ γ [Φ] ⋅ δ [Φ] ∈ R ).
  { eapply R_Mult_in_R. eapply R_Exp_in_R; eauto.
    eapply H7, Property_dm; eauto. rewrite <- H8 in H19.
    eapply H_0, Property_dm; eauto. }
  assert( (f α γ δ)[Φ] = α ^ γ[Φ] ⋅ δ[Φ] ).
  { eqext. appA2H H21. apply H22. appA2G. appoA2G. appA2G. intros.
    appA2H H22. appoA2H H23. deand; subst; auto. }
  assert (Sum (f α γ δ) Φ = α ^ γ[Φ] ⋅ δ[Φ]).
  { eqext. appA2H H22. apply H23. clear H23. appA2G. rewrite H13.
    do 3 (split; auto). intros. rewrite H26. auto. appA2G. intros.
    appA2H H23. deand. eapply CNF_f in H24 as [h'[H24 _]]; auto. deand.
    apply H27 in H24; auto. rewrite H24,H30,H21. auto. }
  rewrite H21,H22. eapply R_Add_3'; eauto.
  rewrite <- H11 in H18. rewrite H18,H21 in H4.
  eapply R_Add_in_R' in H4; eauto. intros. assert (m ∈ dom(g)).
  { destruct H19; try rewrite H19; auto. eapply Ord_Num_trans; eauto.
    eapply (trans_Ord_Num _ _ MKT138); eauto. }
  appA2H H20. rdeHex. New H21. eapply Property_Fun in H21; eauto.
  appoA2H H22. deand. subst; auto.
Qed.
 *)
Lemma CNF_6 : ∀ α β γ δ n a b, Ordinal_Number α -> PlusOne Φ ≺ α
  -> Ordinal_Number a -> Ordinal_Number b -> b ≺ α -> b ≠ Φ
  -> onTo γ ω R -> OnTo δ (dom(γ)) α -> (∀ k, δ [k] ≠ Φ) -> n ∈ dom(γ)
  -> β = α ^ a ⋅ b + Sum (f α γ δ) n
  -> onTo (f_shift_r γ a) ω R
  /\ OnTo (f_shift_r δ b) dom(f_shift_r γ a) α
  /\ (∀k : Class,(f_shift_r δ b) [k] ≠ Φ)
  /\ PlusOne n ∈ dom( f_shift_r γ a)
  /\ β = Sum (f α (f_shift_r γ a) (f_shift_r δ b)) (PlusOne n).
Proof.
  intros. destruct H5 as [H5[]]. destruct H6 as [H6[]].
  New H1. eapply (shift_dom γ a) in H14; eauto.
  New H10. rewrite <- H12 in H15. assert( ran( δ) ⊂ R ).
  { red. intros. apply H13 in H16. eapply (trans_Ord_Num _ _ _ H16); eauto. }
  eapply (shift_fun δ b) in H15 as [H15[]]; eauto.
  split; [| split; [| split; [| split]]].
  - red. eapply shift_fun; eauto.
  - red. split; auto. split. rewrite <- H12 in H10.
    eapply shift_dom in H10; eauto. rewrite H10,H14,H12; split; auto.
    red. intros. appA2H H19. rdeHex. appA2H H20. rdeHex.
    eapply MKT49b in H20 as [H20 _]. eapply MKT55 in H21 as []; eauto.
    subst x1. destruct H23; deand; subst z; auto. apply H13.
    eapply Property_dm; eauto. eapply cap_pre; eauto. rewrite H12; auto.
  - red. intros. TF( k ∈ dom(f_shift_r δ b) ). eapply Property_dm in H20; eauto.
    appA2H H20. rdeHex. appoA2H H21. destruct H22.
    destruct H23; deand; rewrite H24 in H19; try contradiction.
    specialize H7 with (∪x). contradiction. apply MKT69a in H20.
    New Φ_is_Ord. appA2H H21. μ_notset.
  - rewrite H14. eapply (trans_Ord_Num _ _ MKT138) in H10; eauto.
    apply -> R_Add_2'; eauto. eapply trans_Ord_Num; eauto.
  - rewrite shift_Sum; eauto. Unshelve. auto.
Qed.

(* ================================================================= *)
(*                    Cantor Normal Form (主定理)                    *)
(* ================================================================= *)

Theorem CNF : ∀ α β, Ordinal_Number α -> Ordinal_Number β
  -> PlusOne Φ ≺ α -> PlusOne Φ ≼ β
  -> ∃ γ δ n, onTo γ ω R /\ Monodc_f γ /\ OnTo δ (dom(γ)) α
     /\ (∀ k, δ[k] ≠ Φ) /\ n ∈ dom(γ) /\ β = Sum (f α γ δ) n.
Proof.
  intros. generalize dependent β.
  (* 使用超限归纳法对 β 进行证明 *)
  eapply (R_Transfinite_Induction
    (fun x => PlusOne Φ ≼ x ->
      ∃ γ δ n, onTo γ ω R /\ Monodc_f γ /\ OnTo δ (dom(γ)) α
     /\ (∀ k, δ[k] ≠ Φ) /\ n ∈ dom(γ) /\ x = Sum (f α γ δ) n)); eauto.
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
        - rewrite H17, Add_R_Φ_r in H10; try eapply R_Mult_in_R; try right; eauto.
        - New (trans_Ord_Num _ _ H6 H9). eapply H16 in H17; eauto.
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
        New H. eapply (CNF_4 α β (MaxinExp α β) (First x)) in H8; eauto. deand.
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
        exists (f_shift_r γ (MaxinExp α β)), (f_shift_r δ (First x)), (PlusOne n).
        New H. eapply (CNF_6 _ _ _ _ _ (MaxinExp α β) (First x)) in H14; eauto.
        deand. do 2 (split; auto). eapply shift_Monodc; eauto.
        assert (Φ ∈ dom(γ)).
        { eapply Φ_is_First_Ord; eauto. destruct H13 as [H13[]].
          eapply (trans_Ord_Num _ _ MKT138); eauto. intro. rewrite H23 in H18. emf. }
        assert (Ordinal_Number γ[Φ]).
        { destruct H13 as [H13[]]. apply H25,Property_dm; eauto. }
        eapply (Exp_R_PrOrder_b _ _ α),(Ord_Num_trans' _ (Sum (f α γ δ) n) _); eauto.
        assert (α ^ γ[Φ] ≼ α ^ γ[Φ] ⋅ δ[Φ]).
        { eapply R_Mult_1; eauto. eapply R_Exp_in_R; eauto. destruct H16 as [H16[]].
          rewrite <- H25 in H23. apply Property_dm,H26 in H23; eauto.
          eapply (trans_Ord_Num _ _ H); eauto. }
        eapply trans_Ord_Num in H9; eauto. New H.
        eapply (Sum_Monodc _ γ δ n) in H26 as []; eauto.
        left; eapply Ord_Num_trans'; eauto. rewrite <- H26; auto.
        red. intro. rewrite H19,Mult_R_Φ_r,Add_R_Φ_l in H10; auto.
        rewrite <- H10 in H9. eapply Ord_Num_antisym in H5; eauto.
        eapply trans_Ord_Num in H9; eauto.

    + (* Case: α ^ MaxinExp α β = β (本身就是幂次) *)
      exists (f_Φ (MaxinExp α β)), (f_Φ (PlusOne Φ)), Φ.
      symmetry in H5. rewrite <- (Mult_R_PlusOneΦ _ H6) in H5.
      eapply CNF_4 in H5; eauto. deand.
      try repeat (split; auto). pose proof (CNF_2 _ H7) as [_].
      rewrite H12. appA2G. eapply (trans_Ord_Num _ _ H0); eauto.
      red. intros. assert (Φ ∈ PlusOne Φ). appA2G. rewrite H8 in H9. NSym.

  - (* Case: β = Φ 或 最小情况 *)
    exists (f_Φ Φ), (f_Φ (PlusOne Φ)), Φ. New Φ_is_Ord.
    assert (α ^ Φ ⋅ (PlusOne Φ) = PlusOne Φ).
    { rewrite Exp_R_Φ_r, Mult_R_PlusOneΦ; try eapply Lem123; auto. }
    rewrite <- H5 in H3. symmetry in H3. clear H5.
    eapply CNF_4 in H3; eauto. deand.
    try repeat (split; auto). pose proof (CNF_2 _ H4) as [_].
    rewrite H9. appA2G. eapply Lem123; eauto.
    red. intros. assert (Φ ∈ PlusOne Φ). appA2G. rewrite H5 in H6. NSym.

(* 解决 Unshelve 留下的目标 *)
Unshelve.
New Φ_is_Ord. eapply Lem123 in H25. auto. auto.
Qed.