(* 此版本修改结论 *)

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

Fact shift_fun : ∀ f a n, Ordinal_Number a -> n ∈ ω
  -> Function f -> dom(f) = PlusOne n -> ran(f) ⊂ R
  -> Function (f_shift_r f a) /\ dom(f_shift_r f a) = PlusOne (PlusOne n)
  /\ ran(f_shift_r f a) ⊂ R.
Proof.
  intros. repeat split. eapply PisRel.
  - intros. appoA2H H4. appoA2H H5. destruct H6,H7.
    destruct H8,H9; deand; try contradiction; try subst; auto.
  - rewrite shift_dom,H2; eauto. rewrite H2. eapply MKT134; eauto.
  - red. intros. appA2H H4. rdeHex. appoA2H H5. deand.
    destruct H7; deand; subst; auto. apply H3,Property_dm; auto.
    eapply cap_pre; eauto. rewrite H2; eapply MKT134; eauto.
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
  OnTo (f_Φ a) (PlusOne Φ) R /\ Monodc_f (f_Φ a) /\ 
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
  -> Ordinal_Number a -> Ordinal_Number b -> n ∈ ω
  -> OnTo γ (PlusOne n) R -> OnTo δ dom(γ) α
  -> Sum (f α (f_shift_r γ a) (f_shift_r δ b)) (PlusOne n) =
     α ^ a ⋅ b + Sum (f α γ δ) n.
Proof.
  intros. destruct H4 as [H4[]]. destruct H5 as [H5[]].
  assert( dom(γ) ∈ ω ). rewrite H6. eapply MKT134; eauto.
  assert( ran(δ) ⊂ R ). red. intros. eapply (trans_Ord_Num α),H9; eauto.
  New H. eapply (CNF_3 α γ δ) in H12 as [H12[]]; eauto.
  New H3. eapply (shift_fun γ _ _ H1) in H15 as [H15[]]; eauto.
  New H5. eapply (shift_fun δ _ n H2) in H18 as [H18[]]; eauto.
  New H. eapply (CNF_3 α (f_shift_r γ a) (f_shift_r δ b)) in H21 as [H21[]];
  try rewrite H16,H19; try rewrite H8; eauto.
  assert( α ^ a ⋅ b = (f α (f_shift_r γ a) (f_shift_r δ b))[Φ] ).
  { New H. assert( Φ ∈ PlusOne n ). eapply Φ_is_First_Ord; eauto. rewrite <- H6.
    eapply (trans_Ord_Num _ _ MKT138); eauto. apply MKT135b in H3. auto.
    eapply (com_f_value α (f_shift_r γ a) (f_shift_r δ b))
     with (n:=Φ) in H24; try rewrite H16; eauto. rewrite H24.
    assert( ∀ γ' a', Φ ∈ dom(γ') -> Ensemble a' -> (f_shift_r γ' a')[Φ] = a' ).
    { intros. eqext. appA2H H28. apply H29. appA2G. appoA2G. split; auto.
      appA2G. appA2G. intros. appA2H H29. appoA2H H30.
      destruct H31 as [H31[]]; deand; try contradiction; subst; auto. }
    rewrite <- H6 in H25. New H25. rewrite <- H8 in H27. appA2H H1. appA2H H2.
    eapply (H26 _ a) in H25; eauto. eapply (H26 _ b) in H27; eauto.
    rewrite H25,H27; auto. appA2G. }
  rewrite H24. eapply Sum_Lemma4; try rewrite H22; try rewrite H16;
  try rewrite H13; eauto. rewrite H6. appA2G. appA2G. right. appA2G.
  intros. assert( m ∈ dom(γ) ).
  { destruct H25; subst; auto. rewrite H6. eapply (Ord_Num_trans _ _); eauto.
    rewrite <- H6. eapply (trans_Ord_Num _ _ MKT138); eauto. appA2G.
    rewrite H6. appA2G. }
  New H10. eapply (trans_Ord_Num _ _ MKT138) in H10; eauto.
  rewrite (com_f_value α (f_shift_r γ a) (f_shift_r δ b)); try rewrite H16; eauto.
  New (shift_value γ m a H10). rewrite <- H8 in H10. New (shift_value δ m b H10).
  rewrite H28,H29. eapply com_f_value; eauto. rewrite <- H6.
  apply -> R_Add_2'; auto. eapply trans_Ord_Num; eauto. rewrite H8; auto.
Qed.

(* 单调性证明 *)
Lemma shift_Monodc : ∀ f a n, a ∈ R -> n ∈ ω -> OnTo f (PlusOne n) R
  -> Monodc_f f -> f[Φ] ≺ a
  -> let F := f_shift_r f a in Monodc_f F.
Proof.
  intros. destruct H1 as [H1[]]. assert( Function F ).
  { New H1. eapply (shift_fun f0 a) in H6 as [H6[]]; eauto. }
  split; auto. intros. deand.
  appA2H H8. rdeHex. New H10. eapply Property_Fun in H11; auto.
  appA2H H10. rdeHex. eapply MKT49b in H10 as [_ H10].
  eapply MKT55 in H12 as []; eauto. subst x0 x x1.
  destruct H14; deand. rewrite H11 in H9. red in H9. emf.
  appA2H H7. rdeHex. New H14. eapply Property_Fun in H15; auto.
  appA2H H14. rdeHex. eapply MKT49b in H14 as [_ H14].
  eapply MKT55 in H16 as []; eauto. subst x0 x x1. destruct H2.
  New H13. assert( dom(f0) ∈ ω ). rewrite H4. eapply MKT134; eauto.
  eapply (cap_pre dom(f0) k2) in H16; eauto.
  destruct H18; deand; rewrite H20,H12.
  - eapply (trans_Ord_Num _ _ MKT138) in H19; eauto. assert( Φ ∈ dom(f0) ).
    { eapply Φ_is_First_Ord. auto. red. intros. assert( n ∈ dom(f0) ).
      rewrite H4. appA2G. rewrite H21 in H22. emf. }
    assert( f0[∪k2] ≼ f0[Φ] ). New (MKT26 (∪k2)).
    apply -> MKT118 in H22; eauto. destruct H22. left. eapply H15; eauto.
    right. rewrite H22; auto. eapply trans_Ord_Num in H16; eauto.
    appA2H H16; auto. New Φ_is_Ord. appA2H H23. auto. destruct H22.
    eapply Ord_Num_trans; eauto. rewrite H22; auto.
  - New H19. eapply (cap_pre dom(f0) k1) in H19; eauto. eapply H15; eauto.
    do 2 (split; auto). appA2G. exists k1. split; auto. eapply cap_pre; eauto.
    New (MKT134 H21). New (Ord_Num_trans _ _ _ MKT138 H17 H22); eauto. appA2G.
Qed.

Lemma Sum_Monodc : ∀ α γ δ n, Ordinal_Number α -> PlusOne Φ ≺ α
  -> n ∈ ω -> OnTo γ (PlusOne n) R -> OnTo δ (dom(γ)) α
  -> Sum (f α γ δ) n ∈ R -> α ^ γ [Φ] ⋅ δ [Φ] ≼ Sum (f α γ δ) n.
Proof.
  intros. destruct H2 as [H2[]]. destruct H3 as [H3[]].
  assert( dom(γ) ∈ ω ). rewrite H5. apply MKT134. auto.
  assert( dom(γ) ≠ Φ ). apply MKT135b in H1. rewrite H5. red. intros. elim H1. auto.
  assert( Φ ∈ dom(γ) ). { eapply Φ_is_First_Ord; eauto.
   eapply (trans_Ord_Num _ _ MKT138); eauto. } assert( ran(δ) ⊂ R ).
  { red. intros. apply H8 in H12. apply (trans_Ord_Num _ _ H); auto. }
  assert( α ^ γ [Φ] ⋅ δ [Φ] ∈ R ).
  { eapply R_Mult_in_R. eapply R_Exp_in_R; eauto. eapply H6, Property_dm; eauto.
    rewrite <- H7 in H11. eapply H12,Property_dm; eauto. }
  assert( (f α γ δ)[Φ] = α ^ γ[Φ] ⋅ δ[Φ] ). { eapply com_f_value; eauto. }
  New H. eapply (CNF_3 α γ δ) in H15 as [H15 []]; eauto.
  TF (n = Φ). subst. right. rewrite Sum_Lemma2; eauto. rewrite H16; auto.

  set (g := \{\ λ u v, u ∈ ∪ dom(f α γ δ) /\ v = (f α γ δ)[PlusOne u] \}\).
  New H1. eapply ω_Num_is_Suc_Ord in H19 as [x[]]; eauto.
  rewrite H20. assert( ∀ z, z ∈ ∪ dom(f α γ δ) -> (f α γ δ)[PlusOne z] ∈ R ).
  { intros. appA2H H21. rdeHex. eapply (trans_Ord_Num _ _ MKT138) in H9; eauto.
    rewrite <- H16 in H9. New H23. eapply trans_Ord_Num in H23; eauto.
    eapply R_Add_1 in H22; try eapply (trans_Ord_Num x0 z); eauto.
    eapply (Ord_Num_trans' _ _ dom(f α γ δ)) in H22; eauto.
    apply H17,Property_dm; eauto. }
  assert( dom(g) = ∪dom(f α γ δ) ).
  { eqext. appA2H H22. rdeHex. appoA2H H23. deand; auto. appA2G.
    exists (f α γ δ)[PlusOne z]. New H22. apply H21 in H22. appA2G.
    eapply MKT49a; eauto. } assert( x ∈ dom(g) ).
  { rewrite H22,H16,H5,MKT124. rewrite H20. appA2G.
    eapply (trans_Ord_Num _ _ MKT138); eauto. } assert( Function g ).
  { split. eapply PisRel. intros. appA2H H24. appA2H H25. rdeHex.
    eapply MKT49b in H24,H25; eauto. eapply MKT55 in H26,H27;
    try deand; eauto. subst; auto. }
  assert( dom(g) ∈ ω ).
  { New H9. eapply ω_Num_is_Suc_Ord in H25 as [x1[]]. assert( x1 ∈ dom(γ) ).
    rewrite H26. appA2G. rewrite H22,H16,H26,MKT124; eauto.
    eapply (Ord_Num_trans _ _ _ MKT138); eauto. auto. }
  assert( ran(g) ⊂ R ).
  { red. intros. appA2H H26. rdeHex. appoA2H H27. deand. subst. eapply H21; eauto. }

  New H24. eapply ((Sum_Lemma4 (f α γ δ)) g x) in H27;
   try rewrite H16; try rewrite <- H14; eauto. rewrite H14 in H27.
  rewrite H14,H27. eapply R_Add_3'; eauto. rewrite <- H20 in H27. rewrite H27 in H4.
  eapply R_Add_in_R' in H4; eauto. rewrite <- H20. rewrite H5. appA2G.
  intros. assert (m ∈ dom(g)).
  { destruct H28; try rewrite H28; auto. eapply Ord_Num_trans; eauto.
    eapply (trans_Ord_Num _ _ MKT138); eauto. }
  appA2H H29. rdeHex. New H30. eapply Property_Fun in H30; eauto.
  appoA2H H31. deand. subst; auto.
Qed.

Lemma CNF_6 : ∀ α β γ δ n a b, Ordinal_Number α -> PlusOne Φ ≺ α
  -> Ordinal_Number a -> Ordinal_Number b -> b ≺ α -> b ≠ Φ -> n ∈ ω
  -> OnTo γ (PlusOne n) R -> OnTo δ (dom(γ)) α -> (∀ k, δ [k] ≠ Φ)
  -> β = α ^ a ⋅ b + Sum (f α γ δ) n
  -> OnTo (f_shift_r γ a) (PlusOne (PlusOne n)) R
  /\ OnTo (f_shift_r δ b) dom(f_shift_r γ a) α
  /\ (∀k : Class,(f_shift_r δ b) [k] ≠ Φ)
  /\ PlusOne n ∈ dom( f_shift_r γ a)
  /\ β = Sum (f α (f_shift_r γ a) (f_shift_r δ b)) (PlusOne n).
Proof.
  intros. destruct H6 as [H6[]]. destruct H7 as [H7[]].
  assert( dom(γ) ∈ ω ). rewrite H10. apply MKT134. auto.
  New H1. eapply (shift_fun γ a n) in H15 as [H15[]]; eauto.
  New H14. rewrite <- H12 in H18. assert( ran( δ) ⊂ R ).
  { red. intros. apply H13 in H19. eapply (trans_Ord_Num _ _ _ H19); eauto. }
  New H2. eapply (shift_fun δ b n) in H20 as [H20[]]; try rewrite H12; eauto.
  try repeat (split; auto); try rewrite H16; auto.
  - red. intros. appA2H H23. rdeHex. appoA2H H24. destruct H25.
    destruct H26; deand; subst; eauto. apply H13,Property_dm; eauto.
    eapply cap_pre; eauto.
  - red. intros. TF( k ∈ dom(f_shift_r δ b) ). eapply Property_dm in H24; eauto.
    appA2H H24. rdeHex. appoA2H H25. destruct H26.
    destruct H27; deand; rewrite H28 in H23; try contradiction.
    specialize H8 with (∪x). contradiction. apply MKT69a in H24.
    New Φ_is_Ord. appA2H H25. μ_notset.
  - appA2G. right. appA2G.
  - rewrite shift_Sum; try split; eauto. Unshelve. auto.
Qed.

(* ================================================================= *)
(*                    Cantor Normal Form (主定理)                    *)
(* ================================================================= *)

Theorem CNF : ∀ α β, Ordinal_Number α -> Ordinal_Number β
  -> PlusOne Φ ≺ α -> PlusOne Φ ≼ β
  -> ∃ γ δ n, n ∈ ω /\ OnTo γ (PlusOne n) R /\ Monodc_f γ /\ OnTo δ (dom(γ)) α
     /\ (∀ k, δ[k] ≠ Φ) /\ β = Sum (f α γ δ) n.
Proof.
  intros. generalize dependent β.
  (* 使用超限归纳法对 β 进行证明 *)
  eapply (R_Transfinite_Induction
    (fun x => PlusOne Φ ≼ x ->
      ∃ γ δ n, n ∈ ω /\ OnTo γ (PlusOne n) R /\ Monodc_f γ /\ OnTo δ (dom(γ)) α
     /\ (∀ k, δ[k] ≠ Φ) /\ x = Sum (f α γ δ) n)); eauto.
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
        New H12. appA2H H12. pose proof (MKT44 H12) as [H15 _]. rewrite H15; auto. }
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
        New H. eapply (CNF_4 α β (MaxinExp α β) (First x)) in H8; eauto.
        red. intros. rewrite H9,Mult_R_Φ_r in H10; eauto. rewrite H10 in H3. emf.
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
        split; auto. deand. do 2 (split; auto). eapply shift_Monodc; eauto.

        assert (Φ ∈ dom(γ)).
        { destruct H15 as [H15[]]. eapply Φ_is_First_Ord; eauto. rewrite H23.
          eapply Lem123,(trans_Ord_Num _ _ MKT138); eauto.
          rewrite H23. intro. apply MKT135 in H13. elim H13. auto. }
        assert (Ordinal_Number (γ[Φ]) ). destruct H15 as [H15[]].
        eapply Property_dm,H25 in H23; eauto.
        eapply (Exp_R_PrOrder_b _ _ α),(Ord_Num_trans' _ (Sum (f α γ δ) n) _); eauto.
        assert (α ^ γ[Φ] ≼ α ^ γ[Φ] ⋅ δ[Φ]).
        { eapply R_Mult_1; eauto. eapply R_Exp_in_R; eauto. destruct H17 as [H17[]].
          rewrite <- H25 in H23. eapply Property_dm,H26 in H23; eauto.
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
      eapply CNF_4 in H5; eauto. eapply Lem123,Φ_is_Ord; eauto.
      intro. assert (Φ ∈ PlusOne Φ). appA2G. rewrite H8 in H9. NSym.

  - (* Case: β = Φ 或 最小情况 *)
    exists (f_Φ Φ), (f_Φ (PlusOne Φ)), Φ. New Φ_is_Ord.
    assert (α ^ Φ ⋅ (PlusOne Φ) = PlusOne Φ).
    { rewrite Exp_R_Φ_r, Mult_R_PlusOneΦ; try eapply Lem123; auto. }
    rewrite <- H5 in H3. symmetry in H3. clear H5.
    eapply CNF_4 in H3; eauto. eapply Lem123; eauto.
    intro. assert (Φ ∈ PlusOne Φ). appA2G. rewrite H5 in H6. NSym.

(* 解决 Unshelve 留下的目标 *)
Unshelve. eapply Lem123,Φ_is_Ord; eauto. auto.
Qed.