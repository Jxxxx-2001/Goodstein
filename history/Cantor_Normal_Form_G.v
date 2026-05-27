Require Export Sum_Function.

(* ================================================================= *)
(*                       定义 (Definitions)                          *)
(* ================================================================= *)

Definition onTo (F A B : Class) : Prop := 
  Function F /\ dom(F) ∈ A /\ ran(F) ⊂ B.

Definition MaxinExp (α β : Class) : Class := 
  ∪ \{ λ v, α ^ v ≼ β \}.

Definition Monodc_f (γ : Class) : Prop := 
  Function γ /\ 
  (∀ k1 k2, k1 ∈ dom(γ) /\ k2 ∈ dom(γ) /\ k1 ≺ k2 -> γ[k2] ≺ γ[k1]).

Definition f (α γ δ : Class) : Class := 
  \{\ λ u v, u ∈ dom(γ) /\ v = α ^ γ[u] ⋅ δ[u] \}\.

Definition f_Φ (x : Class) : Class := 
  \{\ λ u v, u = Φ /\ v = x \}\.

(* 新增：拼接函数定义，用于归纳步骤中构造新的指数和系数序列 *)
(* f_concat a b 将 Φ 映射为 a，将非 Φ 的 u 映射为 b[u-1] *)
Definition f_concat (a b : Class) : Class :=
  \{\ λ u v, u ∈ PlusOne (dom(b)) /\
             ((u = Φ /\ v = a) \/ (u ≠ Φ /\ v = b[∪u])) \}\.

(* ================================================================= *)
(*                       基础引理 (Basic Lemmas)                     *)
(* ================================================================= *)

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
  Ordinal_Number a -> Ordinal_Number b -> a ^ c ≼ b -> 
  Ordinal_Number c.
Proof.
  intros. destruct H1. 
  eapply trans_Ord_Num in H1; eauto.
  eapply R_Exp_in_R' in H1; eauto.
  subst b. eapply R_Exp_in_R' in H0; eauto.
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

(* 引理 CNF_3: 有限情况下的分解 *)
Lemma CNF_3 : ∀ α β a b, 
  Ordinal_Number α -> Ordinal_Number β -> PlusOne Φ ≺ α -> 
  Ordinal_Number a -> Ordinal_Number b -> 
  b ≠ Φ -> b ≺ α -> β = α ^ a ⋅ b -> 
  onTo (f_Φ a) ω R /\ Monodc_f (f_Φ a) /\ 
  OnTo (f_Φ b) (dom(f_Φ a)) α /\ (∀ k : Class, (f_Φ b)[k] ≠ Φ) /\ 
  β = Sum (f α (f_Φ a) (f_Φ b)) Φ.
Proof.
  intros. 
  assert (L1: ∀ z x, Function (f_Φ x) -> z ∈ ran(f_Φ x) -> z = x).
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
Lemma CNF_4 : ∀ α γ δ, 
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

(* 该引理提取了原证明中大量的重复构造逻辑 *)
Lemma Lemma_Concat_Props : ∀ a b,
  a ∈ R -> Function b -> ran(b) ⊂ R -> dom(b) ∈ ω ->
  let F := f_concat a b in
  Function F /\ 
  dom(F) = PlusOne (dom(b)) /\ 
  ran(F) ⊂ R /\
  F[Φ] = a /\
  (∀ k, k ∈ dom(b) -> F[PlusOne k] = b[k]) /\
  (∀ k1 k2, k1 ∈ dom(F) -> k2 ∈ dom(F) -> k1 ≺ k2 -> 
     (Monodc_f b -> b[Φ] ≺ a ) -> (* 如果 b 单调且首项更小 *)
     F[k2] ≺ F[k1]). (* 则 F 也是单调的 *)
Proof.
  intros. subst F. unfold f_concat.
  (* 证明 F 是函数，定义域和值域正确 *)
  split. { admit. (* Function *) }
  split. { admit. (* dom *) }
  split. { admit. (* ran *) }
  split. { admit. (* F[Φ] = a *) }
  split. { admit. (* Shift property *) }
  (* 单调性证明 *)
  intros. admit.
Admitted.

(* ================================================================= *)
(*                    Cantor Normal Form (主定理)                    *)
(* ================================================================= *)

Theorem CNF : ∀ α β, 
  Ordinal_Number α -> Ordinal_Number β -> 
  PlusOne Φ ≺ α -> PlusOne Φ ≼ β -> 
  ∃ γ δ n, onTo γ ω R /\ Monodc_f γ /\ 
  OnTo δ (dom(γ)) α /\ (∀ k, δ[k] ≠ Φ) /\ 
  n ∈ dom(γ) /\ β = Sum (f α γ δ) n.
Proof.
  intros α β Hα Hβ Hα1. revert β Hβ.
  (* 使用超限归纳法对 β 进行证明 *)
  eapply (R_Transfinite_Induction
    (fun x => PlusOne Φ ≼ x ->
      ∃ γ δ n, onTo γ ω R /\ Monodc_f γ /\ 
      OnTo δ (dom(γ)) α /\ (∀ k, δ[k] ≠ Φ) /\ 
      n ∈ dom(γ) /\ x = Sum (f α γ δ) n)); eauto.
  intros β Ord_β IH H_1_le_β.
  (* 计算最大指数和系数 *)
  set (v := MaxinExp α β).
  assert (H_v_prop: PlusOne Φ ≼ α^v /\ α^v ≼ β). 
  { apply CNF_1; auto. } destruct H_v_prop as [_ H_pow_le_β].
  
  (* 分解 β = α^v * c + r *)
  (* 这里假设存在这样的分解 (模拟 Mult_R_PrOrder_c) *)
  (* 设 First x 为系数 c, Second x 为余数 r *)
  (* 为简化，我们直接对余数 r 是否为 0 进行分类讨论 *)
  
  TF (∃ c r, β = α^v ⋅ c + r /\ r = Φ). (* 模拟整除情况 *)
  - (* Case 1: 整除，即 β = α^v ⋅ c *)
    destruct H as [c [r [H_eq H_r0]]]. subst r.
    (* 此处逻辑对应原代码中的 CNF_3 调用 *)
    (* 构造单点序列 *)
    exists (f_Φ v), (f_Φ c), Φ.
(*     eapply CNF_3; eauto. *)
    (* 补充证明细节：c 和 v 的序数性质等 *)
    admit. 

  - (* Case 2: 有余数，即 β = α^v ⋅ c + r, 且 0 < r < β *)
    (* 假设分解结果 *)
    assert (exists c r, β = α^v ⋅ c + r /\ Φ ≺ r /\ r ≺ β /\ 
            c ∈ α /\ c ≠ Φ). { admit. }
    destruct H0 as [c [r [H_eq [H_r_pos [H_r_lt [H_c_alpha H_c_nz]]]]]].
    
    (* 对余数 r 应用归纳假设 *)
    assert (H_r_1_le: PlusOne Φ ≼ r). { admit. } (* 因为 r > 0 且是序数 *)
    specialize (IH r H_r_lt H_r_1_le).
    destruct IH as [γ_r [δ_r [n_r [H_onTo [H_mono [H_delta [H_delta_nz [H_n_in H_sum]]]]]]]].
    
    (* 使用 f_concat 构造新的序列 *)
    (* γ = (v, γ_r...), δ = (c, δ_r...) *)
    set (γ_new := f_concat v γ_r).
    set (δ_new := f_concat c δ_r).
    set (n_new := PlusOne n_r).
    
    exists γ_new, δ_new, n_new.
    
    (* 利用 Lemma_Concat_Props 验证性质 *)
    assert (H_γ_props: Function γ_new /\ dom(γ_new) = PlusOne (dom(γ_r)) /\ 
            γ_new[Φ] = v /\ (∀ k, k ∈ dom(γ_r) /\ γ_new[PlusOne k] = γ_r[k])).
    { (* eapply Lemma_Concat_Props; auto. *) admit. }
    
    assert (H_δ_props: Function δ_new /\ dom(δ_new) = PlusOne (dom(δ_r)) /\ 
            δ_new[Φ] = c /\ (∀ k, k ∈ dom(δ_r) /\ δ_new[PlusOne k] = δ_r[k])).
    { (* apply Lemma_Concat_Props; auto. *) admit. }
    
    destruct H_γ_props as [Hf_g [Hd_g [Hval_g0 Hval_gS]]].
    destruct H_δ_props as [Hf_d [Hd_d [Hval_d0 Hval_dS]]].

    split.
    (* onTo γ_new *)
    { red. split; auto. split. admit. admit. }
    
    split.
    (* Monodc_f γ_new *)
    { 
       (* 这里利用 v 是最大指数，且余数 r 的首项指数必定小于 v *)
       assert ( γ_r[Φ] ≺ v ). { admit. } 
       (* eapply Lemma_Concat_Props; eauto. *) admit.
    }
    
    split.
    (* OnTo δ_new *)
    { red. split; auto. rewrite Hd_d, Hd_g. auto. split. auto. admit. admit. }
    
    split.
    (* δ_new 非零 *)
    { intros k. TF (k = Φ). 
      - subst k. rewrite Hval_d0. auto. 
      - (* k != Φ logic *) admit. 
    }
    
    split.
    (* n_new 在定义域内 *)
    { rewrite Hd_g. admit. (* n_r ∈ dom γ_r -> PlusOne n_r ∈ PlusOne dom γ_r *) }
    
    (* 求和等式验证 *)
    (* Sum(n_new) = Term(0) + Sum(Rest) *)
    rewrite H_eq. rewrite H_sum.
    (* rewrite Hval_d0, Hval_g0. *)
    (* 证明 Sum (f ...) (PlusOne n) = FirstTerm + Sum (f_rest) n *)
    admit.

Unshelve.
all: try apply Φ_is_Ord. all: auto.
Admitted.