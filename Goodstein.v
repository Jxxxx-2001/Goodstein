Require Export OrdinalNum.Cantor_Normal_Form1.

Notation One := (PlusOne Φ).
Notation Two := (PlusOne (PlusOne Φ)).
Definition natural_num n := n ∈ ω.
Definition get_t n m := MaxinExp n m.

(* ω 的元素都是序数 *)
Lemma nat_Ord : ∀ n, natural_num n -> Ordinal_Number n.
Proof.
  intros. New MKT138. eapply trans_Ord_Num; eauto.
Qed.

(* 由 Two ≼ n 得 One ≺ n （即 PlusOne Φ ≺ n） *)
Lemma Two_le_One_lt : ∀ n, natural_num n -> Two ≼ n -> One ≺ n.
Proof.
  intros. assert (One ∈ Two). { appA2G. }
  eapply Ord_Num_trans''; eauto. apply nat_Ord; auto.
Qed.

(* 最大指数 t = MaxinExp n m 是自然数 *)
Lemma MaxinExp_in_ω : ∀ n m, natural_num n -> natural_num m -> n ≼ m -> Two ≼ n
  -> MaxinExp n m ∈ ω.
Proof.
  intros. New (nat_Ord _ H). New (nat_Ord _ H0).
  New (Two_le_One_lt _ H H2).
  assert (One ≼ m). { left. eapply Ord_Num_trans''; eauto. }
  New (CNF_1 n m H3 H4 H5 H6). destruct H7.
  New (MiEisO n m H3 H4 H5).
  New (R_Exp_2 n (MaxinExp n m) H3 H9 H5).
  (* t ≼ n^t ≼ m, 且 m ∈ ω, ω 传递 *)
  assert (MaxinExp n m ≼ m).
  { destruct H10.
    - left. eapply Ord_Num_trans''; eauto.
    - rewrite H10. auto. }
  destruct H11.
  - New MKT138. appA2H H12. destruct H13. eapply H14; eauto.
  - rewrite H11; auto.
Qed.

(* MaxinExp 的极大性：n^(t+1) ≻ m，即不存在比 t 更大的指数使 n^v ≼ m。
   反设 n^(PlusOne t) ≼ m，则 PlusOne t ∈ {v | n^v ≼ m}，
   由 MKT32 得 PlusOne t ⊂ ∪{...} = MaxinExp n m = t，
   而 t ∈ PlusOne t，故 t ∈ t，矛盾。 *)
Lemma MaxinExp_maximal : ∀ n m, natural_num n -> natural_num m -> n ≼ m -> Two ≼ n
  -> m ≺ n ^ (PlusOne (MaxinExp n m)).
Proof.
  intros. New (nat_Ord _ H). New (nat_Ord _ H0).
  New (Two_le_One_lt _ H H2). New (MaxinExp_in_ω _ _ H H0 H1 H2).
  New (MiEisO n m H3 H4 H5).
  assert (Ordinal_Number (PlusOne (MaxinExp n m))). { apply Lem123; auto. }
  New (R_Exp_in_R n (PlusOne (MaxinExp n m)) H3 H8).
  (* 三分律：要么 m ≺ n^(t+1)，要么 n^(t+1) ≼ m *)
  New (Ord_Num_tri m (n ^ (PlusOne (MaxinExp n m))) H4 H9).
  assert (Hens: Ensemble (PlusOne (MaxinExp n m))).
  { New (MKT134 H6). exists ω; auto. }
  destruct H10 as [H10 | [H10 | H10]]; auto.
  - (* m = n^(t+1)：导出矛盾 *)
    exfalso.
    assert (Hle: n ^ (PlusOne (MaxinExp n m)) ≼ m). { right; auto. }
    assert (PlusOne (MaxinExp n m) ∈ \{ λ v, n ^ v ≼ m \}).
    { apply AxiomII; split; [exact Hens | exact Hle]. }
    apply MKT32 in H11 as [H11 _].
    assert (MaxinExp n m ∈ PlusOne (MaxinExp n m)). { appA2G. }
    apply H11 in H12. change (MaxinExp n m ∈ MaxinExp n m) in H12. NSym.
  - (* n^(t+1) ≺ m：导出矛盾 *)
    exfalso.
    assert (Hle: n ^ (PlusOne (MaxinExp n m)) ≼ m). { left; auto. }
    assert (PlusOne (MaxinExp n m) ∈ \{ λ v, n ^ v ≼ m \}).
    { apply AxiomII; split; [exact Hens | exact Hle]. }
    apply MKT32 in H11 as [H11 _].
    assert (MaxinExp n m ∈ PlusOne (MaxinExp n m)). { appA2G. }
    apply H11 in H12. change (MaxinExp n m ∈ MaxinExp n m) in H12. NSym.
Qed.

(* 最大指数 t ≥ 1：因为 n^1 = n ≼ m，故 1 ∈ {v | n^v ≼ m}，
   于是 One ⊂ MaxinExp，即 Φ ∈ MaxinExp，对自然数得 One ≼ MaxinExp。 *)
Lemma MaxinExp_ge_One : ∀ n m, natural_num n -> natural_num m -> n ≼ m -> Two ≼ n
  -> One ≼ MaxinExp n m.
Proof.
  intros. New (nat_Ord _ H). New (nat_Ord _ H0).
  assert (Hens1: Ensemble (PlusOne Φ)).
  { New (MKT134 MKT135a). exists ω; auto. }
  assert (n ^ (PlusOne Φ) ≼ m).
  { rewrite Exp_R_PlusOneΦ_r; auto. }
  assert (PlusOne Φ ∈ \{ λ v, n ^ v ≼ m \}).
  { apply AxiomII; split; [exact Hens1 | exact H5]. }
  apply MKT32 in H6 as [H6 _].
  assert (Φ ∈ PlusOne Φ). { appA2G. }
  apply H6 in H7. change (Φ ∈ MaxinExp n m) in H7.
  New (Two_le_One_lt _ H H2). New (MiEisO n m H3 H4 H8).
  apply R_Add_1; auto. apply Φ_is_Ord.
Qed.

(* 除法分解的唯一性：若 a·k+b = a·k'+b' 且 b,b' ≺ a，则 k=k' 且 b=b'。
   核心用 Mult_Union'：k ≺ k' ⟹ a·k+b ≺ a·k'，矛盾。 *)
Lemma cnf_decomp_unique : ∀ a k b k' b',
  Ordinal_Number a -> Ordinal_Number k -> Ordinal_Number b
  -> Ordinal_Number k' -> Ordinal_Number b'
  -> b ≺ a -> b' ≺ a
  -> a ⋅ k + b = a ⋅ k' + b'
  -> k = k' /\ b = b'.
Proof.
  intros a k b k' b' Ha Hk Hb Hk' Hb' Hba Hb'a Heq.
  assert (k = k').
  { New (Ord_Num_tri k k' Hk Hk').
    destruct H as [H | [H | H]]; auto.
    - (* k ≺ k'：a·k+b ≺ a·k' ≼ a·k'+b' = m，与 Heq 矛盾 *)
      exfalso. New (Mult_Union' a k b k' Ha Hk' H Hba).
      rewrite Heq in H0.
      New (R_Mult_in_R a k' Ha Hk').
      assert (a ⋅ k' ≼ a ⋅ k' + b'). { eapply R_Add_3'; eauto. }
      destruct H2.
      + New (Ord_Num_trans _ _ _ (R_Add_in_R _ _ H1 Hb') H0 H2). NSym.
      + rewrite <- H2 in H0. NSym.
    - (* k' ≺ k：对称 *)
      exfalso. New (Mult_Union' a k' b' k Ha Hk H Hb'a).
      rewrite <- Heq in H0.
      New (R_Mult_in_R a k Ha Hk).
      assert (a ⋅ k ≼ a ⋅ k + b). { eapply R_Add_3'; eauto. }
      destruct H2.
      + New (Ord_Num_trans _ _ _ (R_Add_in_R _ _ H1 Hb) H0 H2). NSym.
      + rewrite <- H2 in H0. NSym. }
  split; auto. subst k'.
  eapply (Add_R_Cancellation b b' (a ⋅ k)); eauto.
  eapply R_Mult_in_R; eauto.
Qed.

(* 阶段 0 占位 *)

(* 底-n 分解（地基引理，阶段 1 填证）：
   对底数 n ≥ 2、数值 m ≥ n，存在唯一的 c = [k, b]，使得
     m = n^t ⋅ k + b,  其中 t = get_t n m = MaxinExp n m,
     1 ≤ k < n,  b < n^t,  t ≥ 1。
   注意乘法顺序取 n^t ⋅ k（底在左、系数在右），与项目 CNF 约定 α^γ ⋅ δ 一致，
   也与 Mult_R_PrOrder_c 的产出 b = a ⋅ (First c) + (Second c) 直接对应。 *)
Lemma cnf_m : ∀ n m, natural_num n -> natural_num m -> n ≼ m -> Two ≼ n
  -> exists! c, c ∈ (ω × ω)
  /\ let k := (First c) in
     let b := (Second c) in
      m = n ^ (get_t n m) ⋅ k + b
  /\ One ≼ k /\ k ≺ n /\ b ≺ n ^ (get_t n m) /\ One ≼ (get_t n m).
Proof.
  intros n m Hn Hm Hnm Hn2. unfold get_t.
  set (t := MaxinExp n m).
  New (nat_Ord _ Hn). New (nat_Ord _ Hm).
  New (Two_le_One_lt _ Hn Hn2).
  assert (Hm1: One ≼ m). { left. eapply Ord_Num_trans''; eauto. }
  New (CNF_1 n m H H0 H1 Hm1). destruct H2 as [Hnt1 Hntm].
  New (MaxinExp_in_ω _ _ Hn Hm Hnm Hn2). fold t in H2.
  New (MaxinExp_maximal _ _ Hn Hm Hnm Hn2). fold t in H3.
  New (MaxinExp_ge_One _ _ Hn Hm Hnm Hn2). fold t in H4.
  New (MiEisO n m H H0 H1). fold t in H5.
  New (R_Exp_in_R n t H H5).        (* n^t ∈ R *)
  (* n^t ∈ ω *)
  assert (Hntω: n ^ t ∈ ω). { apply ω_Exp_in_ω; auto. }
  (* One ∈ ω 与 Φ ∈ ω *)
  New MKT135a. New (MKT134 MKT135a).
  assert (HΦO: Φ ≺ One). { appA2G. }
  assert (HΦnt: Φ ≺ n ^ t). { eapply Ord_Num_trans''; eauto. }
  (* 统一构造见证 [k,b] 与其满足的全部性质，分两种情况 *)
  assert (Hexists: ∃ k b, k ∈ ω /\ b ∈ ω /\ m = n ^ t ⋅ k + b
    /\ One ≼ k /\ k ≺ n /\ b ≺ n ^ t).
  { destruct Hntm as [Hlt | Heq].
    - (* n^t ≺ m：用 Mult_R_PrOrder_c 提取商 k 与余数 b *)
      New (Mult_R_PrOrder_c (n ^ t) m H6 H0 Hnt1 Hlt).
      destruct H9 as [c [[Hc [Hb_lt Hmeq]] _]].
      (* 将 c 展开为有序对 [u,v] *)
      appA2H Hc. rdeHex. subst c.
      rename x into u. rename x0 into v.
      assert (Hu: Ordinal_Number u) by auto.
      assert (Hv: Ordinal_Number v) by auto.
      assert (HenU: Ensemble u) by (exists R; auto).
      assert (HenV: Ensemble v) by (exists R; auto).
      rewrite MKT54a in Hmeq; auto.
      rewrite MKT54b in Hb_lt, Hmeq; auto.
      (* v ∈ ω：v ≺ n^t ∈ ω，用 Integer 的遗传性 MKT132 *)
      assert (Hvω: v ∈ ω).
      { appA2H Hntω. appA2G. eapply MKT132; eauto. }
      (* n^t ≠ Φ *)
      assert (Hnt_ne: n ^ t <> Φ). { red; intros HE. rewrite HE in HΦnt. NSym. }
      (* u ≼ n^t·u ≼ m，得 u ∈ ω *)
      assert (Hu_le: u ≼ n ^ t ⋅ u). { apply R_Mult_2; auto. }
      assert (Hntu_R: n ^ t ⋅ u ∈ R). { apply R_Mult_in_R; auto. }
      assert (Hntu_le_m: n ^ t ⋅ u ≼ m).
      { rewrite Hmeq. apply R_Add_3'; auto. }
      assert (Hu_le_m: u ≼ m).
      { destruct Hu_le as [Ha|Ha]; destruct Hntu_le_m as [Hb|Hb].
        - left. eapply (Ord_Num_trans u (n ^ t ⋅ u) m); eauto.
        - left. rewrite <- Hb; auto.
        - left. rewrite Ha; auto.
        - right. rewrite Ha, Hb; auto. }
      assert (Huω: u ∈ ω).
      { destruct Hu_le_m as [Hum | Hum].
        - apply AxiomII; split; [exact HenU|].
          appA2H Hm. eapply MKT132; eauto.
        - subst u; auto. }
      exists u, v. split; [exact Huω|]. split; [exact Hvω|].
      split; [exact Hmeq|].
      (* One ≼ u：若 u=Φ 则 m=v≺n^t≼m 矛盾 *)
      assert (Hu1: One ≼ u).
      { TF (u = Φ).
        - exfalso. subst u.
          rewrite (Mult_R_Φ_r (n ^ t) H6) in Hmeq.
          rewrite (Add_R_Φ_l v Hv) in Hmeq.
          (* Hmeq : m = v, Hlt : n^t ≺ m, Hb_lt : v ≺ n^t *)
          rewrite <- Hmeq in Hb_lt.
          New (Ord_Num_trans (n ^ t) m (n ^ t) H6 Hlt Hb_lt).
          elim (MKT101 (n ^ t)). red in H10. exact H10.
        - apply R_Add_1; auto. apply Φ_is_Ord. apply Φ_is_First_Ord; auto. }
      split; [exact Hu1|].
      (* u ≺ n：若 n ≼ u 则 n^(t+1) ≼ n^t·u ≼ m，与极大性矛盾 *)
      assert (Hu_n: u ≺ n).
      { pose proof (Ord_Num_tri u n Hu H) as Htri.
        (* 统一处理 n ≼ u 导致的矛盾：n^t·u ≥ n^t·n = n^(t+1) > m *)
        assert (Hcontra: n ≼ u -> False).
        { intros Hnu.
          (* n^t·n ≼ n^t·u *)
          assert (Hmono: n ^ t ⋅ n ≼ n ^ t ⋅ u).
          { destruct Hnu as [Hnu | Hnu].
            - left. apply Mult_R_PrOrder_a; auto.
            - right. rewrite Hnu; auto. }
          (* n^t·n = n^(t+1) *)
          assert (Hsuc: n ^ t ⋅ n = n ^ (PlusOne t)).
          { rewrite Exp_R_Suc; auto. }
          rewrite Hsuc in Hmono.
          (* n^(t+1) ≼ n^t·u ≼ m，与 H3 : m ≺ n^(t+1) 矛盾 *)
          assert (Hge: n ^ (PlusOne t) ≼ m).
          { destruct Hmono as [Ha|Ha]; destruct Hntu_le_m as [Hb|Hb].
            - left. eapply Ord_Num_trans; eauto.
            - left. rewrite <- Hb; auto.
            - left. rewrite Ha; auto.
            - right. rewrite Ha, Hb; auto. }
          destruct Hge as [Hge|Hge].
          - (* n^(t+1) ≺ m 且 m ≺ n^(t+1) (H3)，trans 得 m ≺ m *)
            New (Ord_Num_trans m (n ^ (PlusOne t)) m H0 H3 Hge).
            elim (MKT101 m). red in H10; exact H10.
          - rewrite Hge in H3. elim (MKT101 m). red in H3; exact H3. }
        destruct Htri as [Hun | [Hun | Hun]]; auto.
        - exfalso. apply Hcontra. right; auto.
        - exfalso. apply Hcontra. left; auto. }
      split; [exact Hu_n | exact Hb_lt].
    - (* n^t = m：取 k=1, b=0 *)
      exists One, Φ. split; [auto|]. split; [auto|].
      assert (Heqm: m = n ^ t ⋅ One + Φ).
      { rewrite Mult_R_PlusOneΦ; [|exact H6].
        rewrite Add_R_Φ_r; [symmetry; exact Heq | exact H6]. }
      split; [exact Heqm|]. split; [right; auto|]. split; [auto|]. auto. }
  (* 组装 exists! c：取 c = [k,b]，唯一性用 cnf_decomp_unique *)
  destruct Hexists as [k [b [Hkω [Hbω [Hmeq [Hk1 [Hkn Hblt]]]]]]].
  assert (Henk: Ensemble k) by (exists ω; auto).
  assert (Henb: Ensemble b) by (exists ω; auto).
  assert (Hok: Ordinal_Number k) by (apply nat_Ord; auto).
  assert (Hob: Ordinal_Number b) by (apply nat_Ord; auto).
  exists ([k, b]). split.
  - (* 满足性质 *)
    split; [appA2G; appoA2G|].
    rewrite (MKT54a k b Henk Henb), (MKT54b k b Henk Henb).
    split; [exact Hmeq|]. split; [exact Hk1|]. split; [exact Hkn|].
    split; [exact Hblt | exact H4].
  - (* 唯一性 *)
    intros c' Hc'. destruct Hc' as [Hc'mem Hc'props].
    cbv zeta in Hc'props.
    apply AxiomII in Hc'mem as [Hen' [k' [b' [Hk'ω [Hb'ω Hpair]]]]].
    subst c'. rename Hc'props into Hcp.
    assert (Henk': Ensemble k') by (exists ω; auto).
    assert (Henb': Ensemble b') by (exists ω; auto).
    rewrite (MKT54a k' b' Henk' Henb'), (MKT54b k' b' Henk' Henb') in Hcp.
    destruct Hcp as [Hmeq' [Hk1' [Hkn' [Hblt' _]]]].
    assert (Hok': Ordinal_Number k') by (apply nat_Ord; auto).
    assert (Hob': Ordinal_Number b') by (apply nat_Ord; auto).
    (* m = n^t·k+b = n^t·k'+b'，且 b,b' ≺ n^t *)
    rewrite Hmeq in Hmeq'.
    pose proof (cnf_decomp_unique (n ^ t) k b k' b'
      H6 Hok Hob Hok' Hob' Hblt Hblt' Hmeq') as [Hkk Hbb].
    subst k' b'. auto.
Qed.

(* ===== 阶段 2：提取算子 get_k / get_b 及分解方程 ===== *)

(* 确定描述（definite description）：在 cnf_m 的前提下，满足分解性质的有序对 c
   是唯一的，故 \{ λ c, P c \} 是单点集 [c0]，∩ 把它取回 c0（惯用法见 Sum）。
   谓词体须与 cnf_m 陈述中 exists! 的矩阵逐字一致。 *)
Definition cnf_wit n m := ∩ \{ λ c, c ∈ (ω × ω)
  /\ let k := (First c) in
     let b := (Second c) in
      m = n ^ (get_t n m) ⋅ k + b
  /\ One ≼ k /\ k ≺ n /\ b ≺ n ^ (get_t n m) /\ One ≼ (get_t n m) \}.

(* 系数 k 与余项 b *)
Definition get_k n m := First (cnf_wit n m).
Definition get_b n m := Second (cnf_wit n m).

(* cnf_wit 取回 cnf_m 的唯一见证 c0 *)
Lemma cnf_wit_eq : ∀ n m, natural_num n -> natural_num m -> n ≼ m -> Two ≼ n
  -> exists c0, cnf_wit n m = c0
  /\ (c0 ∈ (ω × ω)
      /\ let k := (First c0) in let b := (Second c0) in
         m = n ^ (get_t n m) ⋅ k + b
      /\ One ≼ k /\ k ≺ n /\ b ≺ n ^ (get_t n m) /\ One ≼ (get_t n m)).
Proof.
  intros n m Hn Hm Hnm Hn2.
  New (cnf_m n m Hn Hm Hnm Hn2). destruct H as [c0 [HP0 Huniq]].
  exists c0. split; [|exact HP0].
  assert (Hen0: Ensemble c0).
  { destruct HP0 as [Hmem _]. exists (ω × ω); auto. }
  unfold cnf_wit.
  match goal with |- ∩ ?S = _ => set (P := S) end.
  assert (Hsing: P = [c0]).
  { unfold P. eqext.
    - apply AxiomII in H as [Henz Hpz].
      apply MKT41; auto. symmetry. apply Huniq. exact Hpz.
    - apply MKT41 in H; auto. subst z.
      apply AxiomII. split; auto. }
  rewrite Hsing. apply MKT44 in Hen0 as [HI _]. exact HI.
Qed.

(* 分解方程与各约束，直接落在 get_k / get_b 上（阶段 2 主结论） *)
Lemma cnf_spec : ∀ n m, natural_num n -> natural_num m -> n ≼ m -> Two ≼ n
  -> m = n ^ (get_t n m) ⋅ (get_k n m) + (get_b n m)
  /\ One ≼ (get_k n m) /\ (get_k n m) ≺ n
  /\ (get_b n m) ≺ n ^ (get_t n m) /\ One ≼ (get_t n m)
  /\ (get_k n m) ∈ ω /\ (get_b n m) ∈ ω.
Proof.
  intros n m Hn Hm Hnm Hn2.
  New (cnf_wit_eq n m Hn Hm Hnm Hn2).
  destruct H as [c0 [Hwit [Hmem Hrest]]].
  cbv zeta in Hrest. destruct Hrest as [Hmeq [Hk1 [Hkn [Hblt Ht1]]]].
  (* get_k/get_b 展开为 First/Second (cnf_wit) = First/Second c0 *)
  unfold get_k, get_b. rewrite Hwit.
  (* 拆 c0 ∈ ω×ω 为 [u,v]（Hcpair: c0 = [u,v]，其余为 u,v ∈ ω） *)
  apply AxiomII in Hmem as [Hen0 [u [v [Hcpair [Huω Hvω]]]]].
  assert (Henu: Ensemble u) by (exists ω; auto).
  assert (Henv: Ensemble v) by (exists ω; auto).
  (* 用 Hcpair 改写而非 subst（subst 会把 cnf_wit n m 还原，撤销上一步 rewrite） *)
  rewrite Hcpair in Hmeq, Hk1, Hkn, Hblt |- *.
  rewrite (MKT54a u v Henu Henv) in Hmeq, Hk1, Hkn |- *.
  rewrite (MKT54b u v Henu Henv) in Hmeq, Hblt |- *.
  split; [exact Hmeq|]. split; [exact Hk1|]. split; [exact Hkn|].
  split; [exact Hblt|]. split; [exact Ht1|]. split; auto.
Qed.

(* ===== 阶段 3：换底算子 Sn 的 MKT128 定义与递归方程 ===== *)

(* 步进函数 G_Sn n（仿 G f 的三路结构）：
   - dom(u) ∉ ω        → μ
   - dom(u) ∈ ω, m < n → m
   - dom(u) ∈ ω, m ≥ n → (n+1)^{u[t]} · k + u[b] *)
Definition G_Sn n := \{\ λ u v,
  ( dom(u) ∉ ω /\ v = μ )
  \/ ( dom(u) ∈ ω /\ dom(u) ≺ n /\ v = dom(u) )
  \/ ( dom(u) ∈ ω /\ n ≼ dom(u) /\
       v = (PlusOne n) ^ u[get_t n (dom(u))]
           ⋅ (get_k n (dom(u))) + u[get_b n (dom(u))] ) \}\.

(* G_Sn n 是函数 *)
Lemma G_Sn_fun : ∀ n, Function (G_Sn n).
Proof.
  intros n. split. eapply PisRel.
  intros x y1 y2 Hy1 Hy2.
  appoA2H Hy1. appoA2H Hy2.
  (* appoA2H 消耗 Hy1/Hy2，产生 H/H1=Ensemble，H0=P x y1，H2=P x y2 *)
  destruct H0 as [[Ha1 Hb1]|[[Ha1 [Hb1 Hc1]]|[Ha1 [Hb1 Hc1]]]].
  - destruct H2 as [[Ha2 Hb2]|[[Ha2 [Hb2 Hc2]]|[Ha2 [Hb2 Hc2]]]];
    subst; auto; contradiction.
  - destruct H2 as [[Ha2 Hb2]|[[Ha2 [Hb2 Hc2]]|[Ha2 [Hb2 Hc2]]]];
    subst; auto; try contradiction.
    destruct Hb2 as [Hg|Hg].
    + New (Ord_Num_trans _ _ _ (nat_Ord _ Ha1) Hb1 Hg). NSym.
    + subst. red in Hb1. NSym.
  - destruct H2 as [[Ha2 Hb2]|[[Ha2 [Hb2 Hc2]]|[Ha2 [Hb2 Hc2]]]];
    subst; auto; try contradiction.
    destruct Hb1 as [Hg|Hg].
    + New (Ord_Num_trans _ _ _ (nat_Ord _ Ha1) Hb2 Hg). NSym.
    + subst. red in Hb2. NSym.
Qed.

(* 仿 G'：m ≺ n 时的递归方程 h[m] = m *)
Lemma G_Sn' : ∀ n h m,
  Function h -> Ordinal dom(h) -> m ∈ ω -> m ≺ n -> m ∈ dom(h)
  -> (∀ x, Ordinal_Number x -> h[x] = (G_Sn n)[h|(x)])
  -> h[m] = m.
Proof.
  intros n h m Hfun Hord Hm Hlt Hdom Heq.
  assert (Hom : Ordinal_Number m) by (apply nat_Ord; auto).
  assert (Hens_m : Ensemble m) by (exists ω; auto).
  rewrite Heq; auto.
  pose proof (Property_res_dom h m Hfun Hord Hdom) as [Hres_ens Hdomres].
  assert (Hmem : [h|(m), m] ∈ G_Sn n).
  { apply AxiomII'. split; [apply MKT49a; auto|].
    right. left. rewrite Hdomres. auto. }
  pose proof Property_Fun m (G_Sn n) (h|(m)) (G_Sn_fun n) Hmem.
  symmetry; auto.
Qed.

(* 仿 G''：n ≼ m 时的递归方程；t,b 严格落在 m 内，h[t]、h[b] 落在 ω 内
   （局部前提，匹配强归纳：t,b < m 时归纳假设给出 h[t],h[b] ∈ ω），
   k=get_k n m ∈ ω、n ∈ ω 作为前提，保证换底值仍是自然数 *)
Lemma G_Sn'' : ∀ n h m,
  Function h -> Ordinal dom(h) -> m ∈ ω -> n ≼ m -> m ∈ dom(h)
  -> get_t n m ∈ m -> get_b n m ∈ m
  -> h[get_t n m] ∈ ω -> h[get_b n m] ∈ ω -> get_k n m ∈ ω -> n ∈ ω
  -> (∀ x, Ordinal_Number x -> h[x] = (G_Sn n)[h|(x)])
  -> h[m] = (PlusOne n) ^ h[get_t n m] ⋅ (get_k n m) + h[get_b n m].
Proof.
  intros n h m Hfun Hord Hm Hge Hdom Ht_in Hb_in Hht_ω Hhb_ω Hk_ω Hn_ω Heq.
  assert (Hom : Ordinal_Number m) by (apply nat_Ord; auto).
  assert (Hens_m : Ensemble m) by (exists ω; auto).
  rewrite Heq; auto.
  pose proof (Property_res_dom h m Hfun Hord Hdom) as [Hres_ens Hdomres].
  pose proof (Property_res h m (get_t n m) Hfun Hord Hdom Ht_in) as [Hrt _].
  pose proof (Property_res h m (get_b n m) Hfun Hord Hdom Hb_in) as [Hrb _].
  set (v := (PlusOne n) ^ (h|(m))[get_t n (dom(h|(m)))]
            ⋅ (get_k n (dom(h|(m)))) + (h|(m))[get_b n (dom(h|(m)))]).
  assert (Hv_eq : v = (PlusOne n) ^ h[get_t n m] ⋅ (get_k n m) + h[get_b n m]).
  { unfold v. rewrite Hdomres, Hrt, Hrb. auto. }
  assert (Hv_ω : v ∈ ω).
  { rewrite Hv_eq. apply ω_Add_in_ω; auto.
    apply ω_Mult_in_ω; auto. apply ω_Exp_in_ω; auto. }
  assert (Hv_ens : Ensemble v) by (exists ω; auto).
  assert (Hmem : [h|(m), v] ∈ G_Sn n).
  { apply AxiomII'. split; [apply MKT49a; auto|].
    right. right. rewrite Hdomres. unfold v. rewrite Hdomres. auto. }
  pose proof Property_Fun v (G_Sn n) (h|(m)) (G_Sn_fun n) Hmem as Heqv.
  rewrite <- Heqv, Hv_eq. auto.
Qed.

(* 辅助：t ≺ n^t（严格），用于证 get_t n m ∈ m *)
Lemma Exp_gt_exp : ∀ n t, natural_num n -> Two ≼ n -> t ∈ ω -> t ≺ n ^ t.
Proof.
  intros n t Hn Hn2 Ht.
  New (nat_Ord _ Hn). New (Two_le_One_lt _ Hn Hn2).
  generalize dependent t.
  apply Mathematical_Induction.
  - rewrite Exp_R_Φ_r; auto. appA2G.
  - intros k Hk IH.
    assert (Hok : Ordinal_Number k) by (apply nat_Ord; auto).
    assert (Hnk : Ordinal_Number (n ^ k)) by (apply R_Exp_in_R; auto).
    assert (Hon1 : Ordinal_Number (n ^ (PlusOne k))).
    { apply R_Exp_in_R; auto. apply Lem123; auto. }
    pose proof (R_Add_1 (n^k) k Hnk Hok IH) as Hle.
    pose proof (R_Exp_3 k n Hok H H0) as Hlt.
    eapply Ord_Num_trans'; eauto.
Qed.

(* get_t n m ≺ m：t ≼ n^t ≼ m，且 t ≺ n^t 严格 *)
Lemma cnf_t_lt_m : ∀ n m, natural_num n -> natural_num m -> n ≼ m -> Two ≼ n
  -> get_t n m ∈ m.
Proof.
  intros n m Hn Hm Hnm Hn2. unfold get_t.
  New (nat_Ord _ Hn). New (nat_Ord _ Hm). New (Two_le_One_lt _ Hn Hn2).
  assert (Hm1: One ≼ m). { left. eapply Ord_Num_trans''; eauto. }
  New (CNF_1 n m H H0 H1 Hm1). destruct H2 as [_ Hntm].
  New (MaxinExp_in_ω _ _ Hn Hm Hnm Hn2).
  (* t ≺ n^t ≼ m *)
  New (Exp_gt_exp n (MaxinExp n m) Hn Hn2 H2).
  eapply Ord_Num_trans''; eauto.
Qed.

(* get_b n m ≺ m：b ≺ n^t ≼ m *)
Lemma cnf_b_lt_m : ∀ n m, natural_num n -> natural_num m -> n ≼ m -> Two ≼ n
  -> get_b n m ∈ m.
Proof.
  intros n m Hn Hm Hnm Hn2.
  New (nat_Ord _ Hn). New (nat_Ord _ Hm). New (Two_le_One_lt _ Hn Hn2).
  assert (Hm1: One ≼ m). { left. eapply Ord_Num_trans''; eauto. }
  New (CNF_1 n m H H0 H1 Hm1). destruct H2 as [_ Hntm].
  New (cnf_spec n m Hn Hm Hnm Hn2).
  destruct H2 as [_ [_ [_ [Hblt _]]]].
  eapply Ord_Num_trans''; eauto.
Qed.
(* ===== 阶段 3 续：换底算子 Sn 的定义与主性质 ===== *)

Lemma Sn_aux : ∀ n, natural_num n -> Two ≼ n ->
  ∀ h, Function h -> Ordinal dom(h)
  -> (∀ x, Ordinal_Number x -> h[x] = (G_Sn n)[h|(x)])
  -> ∀ m, m ∈ ω -> m ∈ dom(h) /\ h[m] ∈ ω.
Proof.
  intros n Hn Hn2 h Hfun Hord Heq.
  New (nat_Ord _ Hn). New (Two_le_One_lt _ Hn Hn2).
  rename H into Hon. rename H0 into Hn1.
  assert (Hstep : ∀ k, k ∈ ω -> (∀ j, j ≺ k -> (j ∈ dom(h) /\ h[j] ∈ ω))
    -> (k ∈ dom(h) /\ h[k] ∈ ω)).
  { intros k Hk IH.
    assert (Hok : Ordinal_Number k) by (apply nat_Ord; auto).
    assert (Hsub : k ⊂ dom(h)) by (red; intros j Hj; apply IH; auto).
    assert (Hdomr : dom(h|(k)) = k) by (rewrite MKT126b; auto; apply MKT30; auto).
    assert (Hfr : Function (h|(k))) by (apply MKT126a; auto).
    assert (Henr : Ensemble (h|(k))).
    { apply MKT75; auto. rewrite Hdomr. exists ω; auto. }
    assert (Hens_k : Ensemble k) by (exists ω; auto).
    New (Heq k Hok).   (* H : h[k] = (G_Sn n)[h|(k)] *)
    assert (Hcase : k ≺ n \/ n ≼ k).
    { destruct (Ord_Num_tri k n Hok Hon) as [Hc|[Hc|Hc]]; auto.
      - right; right; auto.
      - right; left; auto. }
    destruct Hcase as [Hlt | Hge].
    - (* k ≺ n *)
      assert (Hmem : [h|(k), k] ∈ G_Sn n).
      { apply AxiomII'. split; [apply MKT49a; auto|].
        right. left. rewrite Hdomr. auto. }
      pose proof Property_Fun k (G_Sn n) (h|(k)) (G_Sn_fun n) Hmem as Hval.
      rewrite H, <- Hval. split; auto.
      apply MKT69b', MKT19. rewrite H, <- Hval; auto.
    - (* n ≼ k *)
      assert (Ht_in : get_t n k ∈ k) by (apply cnf_t_lt_m; auto).
      assert (Hb_in : get_b n k ∈ k) by (apply cnf_b_lt_m; auto).
      assert (Ht_domr : get_t n k ∈ dom(h|(k))) by (rewrite Hdomr; auto).
      assert (Hb_domr : get_b n k ∈ dom(h|(k))) by (rewrite Hdomr; auto).
      pose proof (MKT126c h k Hfun (get_t n k) Ht_domr) as Hct.
      pose proof (MKT126c h k Hfun (get_b n k) Hb_domr) as Hcb.
      assert (Hht : h[get_t n k] ∈ ω) by (apply IH; auto).
      assert (Hhb : h[get_b n k] ∈ ω) by (apply IH; auto).
      pose proof (cnf_spec n k Hn Hk Hge Hn2) as Hsp.
      destruct Hsp as [_ [_ [_ [_ [_ [Hk_ω _]]]]]].
      set (val := (PlusOne n) ^ h[get_t n k] ⋅ (get_k n k) + h[get_b n k]).
      assert (Hval_ω : val ∈ ω).
      { unfold val. apply ω_Add_in_ω; auto. apply ω_Mult_in_ω; auto.
        apply ω_Exp_in_ω; auto. }
      set (v0 := (PlusOne n) ^ (h|(k))[get_t n (dom(h|(k)))]
                 ⋅ (get_k n (dom(h|(k)))) + (h|(k))[get_b n (dom(h|(k)))]).
      assert (Hv0_eq : v0 = val).
      { unfold v0, val. rewrite Hdomr, Hct, Hcb. auto. }
      assert (Hv0_ω : v0 ∈ ω) by (rewrite Hv0_eq; auto).
      assert (Hv0_ens : Ensemble v0) by (exists ω; auto).
      assert (Hmem : [h|(k), v0] ∈ G_Sn n).
      { apply AxiomII'. split; [apply MKT49a; [exact Henr|exact Hv0_ens]|].
        right. right. split; [rewrite Hdomr; exact Hk|].
        split; [rewrite Hdomr; exact Hge|]. unfold v0; reflexivity. }
      pose proof Property_Fun v0 (G_Sn n) (h|(k)) (G_Sn_fun n) Hmem as Hval.
      rewrite H, <- Hval. split; [|rewrite Hv0_eq; auto].
      apply MKT69b', MKT19. rewrite H, <- Hval; auto. }
  intros m Hm.
  assert (HPΦ : Φ ∈ dom(h) /\ h[Φ] ∈ ω).
  { apply Hstep; auto. intros j Hj. exfalso. apply (@MKT16 j); auto. }
  exact (The_Second_Mathematical_Induction
    (fun k => k ∈ dom(h) /\ h[k] ∈ ω) HPΦ Hstep m Hm).
Qed.

(* 换底算子 Sn：对底 n 与数值 m，取满足 MKT128 方程的唯一 h 的值 h[m] *)
Definition Sn n m := ∩ \{ λ u, ∀ h, Function h -> Ordinal dom(h)
   -> (∀ x, Ordinal_Number x -> h[x] = (G_Sn n)[h|(x)])
   -> u = h[m] \}.

(* Sn 的主性质：落 ω + 两条递归方程 *)
Theorem Sn_spec : ∀ n, natural_num n -> Two ≼ n ->
  (∀ m, m ∈ ω -> Sn n m ∈ ω)
  /\ (∀ m, m ∈ ω -> m ≺ n -> Sn n m = m)
  /\ (∀ m, m ∈ ω -> n ≼ m ->
        Sn n m = (PlusOne n) ^ (Sn n (get_t n m)) ⋅ (get_k n m)
                 + (Sn n (get_b n m))).
Proof.
  intros n Hn Hn2.
  New (MKT128 (G_Sn n)). destruct H as [h0 [[Hf0 [Ho0 He0]] Hu0]].
  (* Sn n m = h0[m] 对 m ∈ ω *)
  assert (Sn_val : ∀ m, m ∈ ω -> Sn n m = h0[m]).
  { intros m Hm.
    New (Sn_aux n Hn Hn2 h0 Hf0 Ho0 He0 m Hm). destruct H as [Hmdom Hmω].
    assert (Hens : Ensemble (h0[m])) by (exists ω; auto).
    unfold Sn.
    assert (Hsing : \{ λ u, ∀ h, Function h -> Ordinal dom(h)
       -> (∀ x, Ordinal_Number x -> h[x] = (G_Sn n)[h|(x)])
       -> u = h[m] \} = [h0[m]]).
    { eqext.
      - appA2H H. apply MKT41; auto.
      - apply MKT41 in H; auto. subst z. appA2G. intros h Hfh Hoh Heh.
        assert (h = h0) by (symmetry; apply Hu0; auto). subst h. auto. }
    rewrite Hsing. apply MKT44 in Hens as [HI _]. exact HI. }
  (* t,b ∈ ω *)
  assert (Htω : ∀ m, m ∈ ω -> n ≼ m -> get_t n m ∈ ω).
  { intros m Hm Hge. apply MaxinExp_in_ω; auto. }
  assert (Hbω : ∀ m, m ∈ ω -> n ≼ m -> get_b n m ∈ ω).
  { intros m Hm Hge. pose proof (cnf_spec n m Hn Hm Hge Hn2) as Hsp.
    destruct Hsp as [_ [_ [_ [_ [_ [_ Hbω]]]]]]. auto. }
  split; [|split].
  - (* ∈ ω *)
    intros m Hm. rewrite Sn_val; auto.
    New (Sn_aux n Hn Hn2 h0 Hf0 Ho0 He0 m Hm). tauto.
  - (* m ≺ n *)
    intros m Hm Hlt. rewrite Sn_val; auto.
    New (Sn_aux n Hn Hn2 h0 Hf0 Ho0 He0 m Hm). destruct H as [Hmdom _].
    apply (G_Sn' n h0 m); auto.
  - (* n ≼ m *)
    intros m Hm Hge.
    assert (Htm : get_t n m ∈ ω) by (apply Htω; auto).
    assert (Hbm : get_b n m ∈ ω) by (apply Hbω; auto).
    rewrite Sn_val; auto. rewrite (Sn_val (get_t n m) Htm), (Sn_val (get_b n m) Hbm).
    New (Sn_aux n Hn Hn2 h0 Hf0 Ho0 He0 m Hm). destruct H as [Hmdom _].
    pose proof (cnf_spec n m Hn Hm Hge Hn2) as Hsp.
    destruct Hsp as [_ [_ [_ [_ [_ [Hk_ω _]]]]]].
    New (Sn_aux n Hn Hn2 h0 Hf0 Ho0 He0 (get_t n m) Htm). destruct H as [_ Hht].
    New (Sn_aux n Hn Hn2 h0 Hf0 Ho0 He0 (get_b n m) Hbm). destruct H as [_ Hhb].
    apply (G_Sn'' n h0 m); auto.
    + apply cnf_t_lt_m; auto.
    + apply cnf_b_lt_m; auto.
Qed.

(* ===== 阶段 4：序数化算子 fn（底换成 ω，落入真正序数 R） ===== *)

Definition G_fn n := \{\ λ u v,
  ( dom(u) ∉ ω /\ v = μ )
  \/ ( dom(u) ∈ ω /\ dom(u) ≺ n /\ v = dom(u) )
  \/ ( dom(u) ∈ ω /\ n ≼ dom(u) /\
       v = ω ^ u[get_t n (dom(u))]
           ⋅ (get_k n (dom(u))) + u[get_b n (dom(u))] ) \}\.

Lemma G_fn_fun : ∀ n, Function (G_fn n).
Proof.
  intros n. split. eapply PisRel.
  intros x y1 y2 Hy1 Hy2. appoA2H Hy1. appoA2H Hy2.
  destruct H0 as [[Ha1 Hb1]|[[Ha1 [Hb1 Hc1]]|[Ha1 [Hb1 Hc1]]]].
  - destruct H2 as [[Ha2 Hb2]|[[Ha2 [Hb2 Hc2]]|[Ha2 [Hb2 Hc2]]]];
    subst; auto; contradiction.
  - destruct H2 as [[Ha2 Hb2]|[[Ha2 [Hb2 Hc2]]|[Ha2 [Hb2 Hc2]]]];
    subst; auto; try contradiction.
    destruct Hb2 as [Hg|Hg].
    + New (Ord_Num_trans _ _ _ (nat_Ord _ Ha1) Hb1 Hg). NSym.
    + subst. red in Hb1. NSym.
  - destruct H2 as [[Ha2 Hb2]|[[Ha2 [Hb2 Hc2]]|[Ha2 [Hb2 Hc2]]]];
    subst; auto; try contradiction.
    destruct Hb1 as [Hg|Hg].
    + New (Ord_Num_trans _ _ _ (nat_Ord _ Ha1) Hb2 Hg). NSym.
    + subst. red in Hb2. NSym.
Qed.

Lemma G_fn' : ∀ n h m,
  Function h -> Ordinal dom(h) -> m ∈ ω -> m ≺ n -> m ∈ dom(h)
  -> (∀ x, Ordinal_Number x -> h[x] = (G_fn n)[h|(x)])
  -> h[m] = m.
Proof.
  intros n h m Hfun Hord Hm Hlt Hdom Heq.
  assert (Hom : Ordinal_Number m) by (apply nat_Ord; auto).
  assert (Hens_m : Ensemble m) by (exists ω; auto).
  rewrite Heq; auto.
  pose proof (Property_res_dom h m Hfun Hord Hdom) as [Hres_ens Hdomres].
  assert (Hmem : [h|(m), m] ∈ G_fn n).
  { apply AxiomII'. split; [apply MKT49a; auto|].
    right. left. rewrite Hdomres. auto. }
  pose proof Property_Fun m (G_fn n) (h|(m)) (G_fn_fun n) Hmem.
  symmetry; auto.
Qed.

Lemma G_fn'' : ∀ n h m,
  Function h -> Ordinal dom(h) -> m ∈ ω -> n ≼ m -> m ∈ dom(h)
  -> get_t n m ∈ m -> get_b n m ∈ m
  -> h[get_t n m] ∈ R -> h[get_b n m] ∈ R -> get_k n m ∈ ω -> n ∈ ω
  -> (∀ x, Ordinal_Number x -> h[x] = (G_fn n)[h|(x)])
  -> h[m] = ω ^ h[get_t n m] ⋅ (get_k n m) + h[get_b n m].
Proof.
  intros n h m Hfun Hord Hm Hge Hdom Ht_in Hb_in Hht_R Hhb_R Hk_ω Hn_ω Heq.
  assert (Hom : Ordinal_Number m) by (apply nat_Ord; auto).
  assert (Hens_m : Ensemble m) by (exists ω; auto).
  rewrite Heq; auto.
  pose proof (Property_res_dom h m Hfun Hord Hdom) as [Hres_ens Hdomres].
  pose proof (Property_res h m (get_t n m) Hfun Hord Hdom Ht_in) as [Hrt _].
  pose proof (Property_res h m (get_b n m) Hfun Hord Hdom Hb_in) as [Hrb _].
  set (v := ω ^ (h|(m))[get_t n (dom(h|(m)))]
            ⋅ (get_k n (dom(h|(m)))) + (h|(m))[get_b n (dom(h|(m)))]).
  assert (Hv_eq : v = ω ^ h[get_t n m] ⋅ (get_k n m) + h[get_b n m]).
  { unfold v. rewrite Hdomres, Hrt, Hrb. auto. }
  assert (Hv_R : v ∈ R).
  { rewrite Hv_eq. apply R_Add_in_R.
    - apply R_Mult_in_R.
      + apply R_Exp_in_R. apply MKT138. exact Hht_R.
      + apply nat_Ord; exact Hk_ω.
    - exact Hhb_R. }
  assert (Hv_ens : Ensemble v) by (exists R; auto).
  assert (Hmem : [h|(m), v] ∈ G_fn n).
  { apply AxiomII'. split; [apply MKT49a; auto|].
    right. right. rewrite Hdomres. unfold v. rewrite Hdomres. auto. }
  pose proof Property_Fun v (G_fn n) (h|(m)) (G_fn_fun n) Hmem as Heqv.
  rewrite <- Heqv, Hv_eq. auto.
Qed.

Lemma fn_aux : ∀ n, natural_num n -> Two ≼ n ->
  ∀ h, Function h -> Ordinal dom(h)
  -> (∀ x, Ordinal_Number x -> h[x] = (G_fn n)[h|(x)])
  -> ∀ m, m ∈ ω -> m ∈ dom(h) /\ h[m] ∈ R.
Proof.
  intros n Hn Hn2 h Hfun Hord Heq.
  New (nat_Ord _ Hn). New (Two_le_One_lt _ Hn Hn2).
  rename H into Hon. rename H0 into Hn1.
  assert (Hstep : ∀ k, k ∈ ω -> (∀ j, j ≺ k -> (j ∈ dom(h) /\ h[j] ∈ R))
    -> (k ∈ dom(h) /\ h[k] ∈ R)).
  { intros k Hk IH.
    assert (Hok : Ordinal_Number k) by (apply nat_Ord; auto).
    assert (Hsub : k ⊂ dom(h)) by (red; intros j Hj; apply IH; auto).
    assert (Hdomr : dom(h|(k)) = k) by (rewrite MKT126b; auto; apply MKT30; auto).
    assert (Hfr : Function (h|(k))) by (apply MKT126a; auto).
    assert (Henr : Ensemble (h|(k))).
    { apply MKT75; auto. rewrite Hdomr. exists ω; auto. }
    assert (Hens_k : Ensemble k) by (exists ω; auto).
    New (Heq k Hok).
    assert (Hcase : k ≺ n \/ n ≼ k).
    { destruct (Ord_Num_tri k n Hok Hon) as [Hc|[Hc|Hc]]; auto.
      - right; right; auto.
      - right; left; auto. }
    destruct Hcase as [Hlt | Hge].
    - (* k ≺ n *)
      assert (Hmem : [h|(k), k] ∈ G_fn n).
      { apply AxiomII'. split; [apply MKT49a; auto|].
        right. left. rewrite Hdomr. auto. }
      pose proof Property_Fun k (G_fn n) (h|(k)) (G_fn_fun n) Hmem as Hval.
      rewrite H, <- Hval. split.
      + apply MKT69b', MKT19. rewrite H, <- Hval; auto.
      + apply nat_Ord; auto.
    - (* n ≼ k *)
      assert (Ht_in : get_t n k ∈ k) by (apply cnf_t_lt_m; auto).
      assert (Hb_in : get_b n k ∈ k) by (apply cnf_b_lt_m; auto).
      assert (Ht_domr : get_t n k ∈ dom(h|(k))) by (rewrite Hdomr; auto).
      assert (Hb_domr : get_b n k ∈ dom(h|(k))) by (rewrite Hdomr; auto).
      pose proof (MKT126c h k Hfun (get_t n k) Ht_domr) as Hct.
      pose proof (MKT126c h k Hfun (get_b n k) Hb_domr) as Hcb.
      assert (Hht : h[get_t n k] ∈ R) by (apply IH; auto).
      assert (Hhb : h[get_b n k] ∈ R) by (apply IH; auto).
      pose proof (cnf_spec n k Hn Hk Hge Hn2) as Hsp.
      destruct Hsp as [_ [_ [_ [_ [_ [Hk_ω _]]]]]].
      set (val := ω ^ h[get_t n k] ⋅ (get_k n k) + h[get_b n k]).
      assert (Hval_R : val ∈ R).
      { unfold val. apply R_Add_in_R.
        - apply R_Mult_in_R.
          + apply R_Exp_in_R. apply MKT138. exact Hht.
          + apply nat_Ord; exact Hk_ω.
        - exact Hhb. }
      set (v0 := ω ^ (h|(k))[get_t n (dom(h|(k)))]
                 ⋅ (get_k n (dom(h|(k)))) + (h|(k))[get_b n (dom(h|(k)))]).
      assert (Hv0_eq : v0 = val).
      { unfold v0, val. rewrite Hdomr, Hct, Hcb. auto. }
      assert (Hv0_R : v0 ∈ R) by (rewrite Hv0_eq; auto).
      assert (Hv0_ens : Ensemble v0) by (exists R; auto).
      assert (Hmem : [h|(k), v0] ∈ G_fn n).
      { apply AxiomII'. split; [apply MKT49a; [exact Henr|exact Hv0_ens]|].
        right. right. split; [rewrite Hdomr; exact Hk|].
        split; [rewrite Hdomr; exact Hge|]. unfold v0; reflexivity. }
      pose proof Property_Fun v0 (G_fn n) (h|(k)) (G_fn_fun n) Hmem as Hval.
      rewrite H, <- Hval. split; [|rewrite Hv0_eq; exact Hval_R].
      apply MKT69b', MKT19. rewrite H, <- Hval; auto. }
  intros m Hm.
  assert (HPΦ : Φ ∈ dom(h) /\ h[Φ] ∈ R).
  { apply Hstep; auto. intros j Hj. exfalso. apply (@MKT16 j); auto. }
  exact (The_Second_Mathematical_Induction
    (fun k => k ∈ dom(h) /\ h[k] ∈ R) HPΦ Hstep m Hm).
Qed.

(* 序数化算子 fn：取满足 MKT128 方程的唯一 h 的值 h[m] *)
Definition fn n m := ∩ \{ λ u, ∀ h, Function h -> Ordinal dom(h)
   -> (∀ x, Ordinal_Number x -> h[x] = (G_fn n)[h|(x)])
   -> u = h[m] \}.

(* fn 的主性质：落 R + 两条递归方程 *)
Theorem fn_spec : ∀ n, natural_num n -> Two ≼ n ->
  (∀ m, m ∈ ω -> fn n m ∈ R)
  /\ (∀ m, m ∈ ω -> m ≺ n -> fn n m = m)
  /\ (∀ m, m ∈ ω -> n ≼ m ->
        fn n m = ω ^ (fn n (get_t n m)) ⋅ (get_k n m)
                 + (fn n (get_b n m))).
Proof.
  intros n Hn Hn2.
  New (MKT128 (G_fn n)). destruct H as [h0 [[Hf0 [Ho0 He0]] Hu0]].
  assert (fn_val : ∀ m, m ∈ ω -> fn n m = h0[m]).
  { intros m Hm.
    New (fn_aux n Hn Hn2 h0 Hf0 Ho0 He0 m Hm). destruct H as [Hmdom HmR].
    assert (Hens : Ensemble (h0[m])) by (exists R; auto).
    unfold fn.
    assert (Hsing : \{ λ u, ∀ h, Function h -> Ordinal dom(h)
       -> (∀ x, Ordinal_Number x -> h[x] = (G_fn n)[h|(x)])
       -> u = h[m] \} = [h0[m]]).
    { eqext.
      - appA2H H. apply MKT41; auto.
      - apply MKT41 in H; auto. subst z. appA2G. intros h Hfh Hoh Heh.
        assert (h = h0) by (symmetry; apply Hu0; auto). subst h. auto. }
    rewrite Hsing. apply MKT44 in Hens as [HI _]. exact HI. }
  assert (Htω : ∀ m, m ∈ ω -> n ≼ m -> get_t n m ∈ ω).
  { intros m Hm Hge. apply MaxinExp_in_ω; auto. }
  assert (Hbω : ∀ m, m ∈ ω -> n ≼ m -> get_b n m ∈ ω).
  { intros m Hm Hge. pose proof (cnf_spec n m Hn Hm Hge Hn2) as Hsp.
    destruct Hsp as [_ [_ [_ [_ [_ [_ Hbω]]]]]]. auto. }
  split; [|split].
  - (* ∈ R *)
    intros m Hm. rewrite fn_val; auto.
    New (fn_aux n Hn Hn2 h0 Hf0 Ho0 He0 m Hm). tauto.
  - (* m ≺ n *)
    intros m Hm Hlt. rewrite fn_val; auto.
    New (fn_aux n Hn Hn2 h0 Hf0 Ho0 He0 m Hm). destruct H as [Hmdom _].
    apply (G_fn' n h0 m); auto.
  - (* n ≼ m *)
    intros m Hm Hge.
    assert (Htm : get_t n m ∈ ω) by (apply Htω; auto).
    assert (Hbm : get_b n m ∈ ω) by (apply Hbω; auto).
    rewrite fn_val; auto. rewrite (fn_val (get_t n m) Htm), (fn_val (get_b n m) Hbm).
    New (fn_aux n Hn Hn2 h0 Hf0 Ho0 He0 m Hm). destruct H as [Hmdom _].
    pose proof (cnf_spec n m Hn Hm Hge Hn2) as Hsp.
    destruct Hsp as [_ [_ [_ [_ [_ [Hk_ω _]]]]]].
    New (fn_aux n Hn Hn2 h0 Hf0 Ho0 He0 (get_t n m) Htm). destruct H as [_ Hht].
    New (fn_aux n Hn Hn2 h0 Hf0 Ho0 He0 (get_b n m) Hbm). destruct H as [_ Hhb].
    apply (G_fn'' n h0 m); auto.
    + apply cnf_t_lt_m; auto.
    + apply cnf_b_lt_m; auto.
Qed.
(* ===== 阶段 5：核心引理 4.5.5 ===== *)

(* 通用 CNF 顶项比较律：(e,c,r) 三元组字典序 ⟹ base^e·c+r 的序。
   base=n 给底-n 比较，base=ω 给序数比较。 *)
Lemma top_term_lt : ∀ base e1 e2 c1 c2 r1 r2,
  Ordinal_Number base -> One ≺ base ->
  Ordinal_Number e1 -> Ordinal_Number e2 ->
  Ordinal_Number c1 -> Ordinal_Number c2 ->
  Ordinal_Number r1 -> Ordinal_Number r2 ->
  c1 ≺ base -> One ≼ c2 -> r1 ≺ base ^ e1 ->
  ( e1 ≺ e2 \/ (e1 = e2 /\ c1 ≺ c2) \/ (e1 = e2 /\ c1 = c2 /\ r1 ≺ r2) ) ->
  base ^ e1 ⋅ c1 + r1 ≺ base ^ e2 ⋅ c2 + r2.
Proof.
  intros base e1 e2 c1 c2 r1 r2 Hbase Hb1 He1 He2 Hc1 Hc2 Hr1 Hr2 Hc1b Hc2pos Hr1b Hcase.
  assert (Hbe1 : Ordinal_Number (base ^ e1)) by (apply R_Exp_in_R; auto).
  assert (Hbe2 : Ordinal_Number (base ^ e2)) by (apply R_Exp_in_R; auto).
  assert (Hc2ne : c2 <> Φ).
  { intro Hz. subst c2. destruct Hc2pos as [Hlt|Heq].
    - eapply MKT16; eauto.
    - assert (HΦ : Φ ∈ One) by appA2G. rewrite Heq in HΦ. eapply MKT16; eauto. }
  assert (Hrhs_mid : Ordinal_Number (base ^ e2 ⋅ c2)) by (apply R_Mult_in_R; auto).
  assert (Hrhs : Ordinal_Number (base ^ e2 ⋅ c2 + r2)) by (apply R_Add_in_R; auto).
  assert (Htail : base ^ e2 ⋅ c2 ≼ base ^ e2 ⋅ c2 + r2) by (apply R_Add_3'; auto).
  destruct Hcase as [Hlt | [[Heq Hck] | [Heq1 [Heq2 Hrr]]]].
  - New (Mult_Union' (base ^ e1) c1 r1 base Hbe1 Hbase Hc1b Hr1b).
    rewrite <- Exp_R_Suc in H; auto.
    New (R_Add_1 e2 e1 He2 He1 Hlt).
    assert (Hexp_le : base ^ (PlusOne e1) ≼ base ^ e2).
    { destruct H0 as [Hpl|Hpe].
      - left. apply Exp_R_PrOrder_a; auto. apply Lem123; auto.
      - rewrite Hpe; right; auto. }
    assert (Hmono : base ^ e2 ≼ base ^ e2 ⋅ c2) by (apply R_Mult_1; auto).
    New (Ord_Num_trans'' _ _ _ Hbe2 H Hexp_le).
    New (Ord_Num_trans'' _ _ _ Hrhs_mid H1 Hmono).
    exact (Ord_Num_trans'' _ _ _ Hrhs H2 Htail).
  - subst e2.
    New (Mult_Union' (base ^ e1) c1 r1 c2 Hbe1 Hc2 Hck Hr1b).
    exact (Ord_Num_trans'' _ _ _ Hrhs H Htail).
  - subst e2. subst c2.
    apply Add_R_PrOrder_a; auto.
Qed.

(* 指数比较：n^a ≼ n^b ⟹ a ≼ b *)
Lemma exp_le_imp_le : ∀ n a b, natural_num n -> Two ≼ n -> a ∈ ω -> b ∈ ω ->
  n ^ a ≼ n ^ b -> a ≼ b.
Proof.
  intros n a b Hn Hn2 Ha Hb Hle.
  New (nat_Ord _ Hn). New (nat_Ord _ Ha). New (nat_Ord _ Hb).
  New (Two_le_One_lt _ Hn Hn2).
  destruct (Ord_Num_tri a b H0 H1) as [Hlt|[Heq|Hgt]].
  - left; auto.
  - right; auto.
  - exfalso. New (Exp_R_PrOrder_a b a n H1 H0 H H2 Hgt).
    New (R_Exp_in_R n b H H1).
    New (Ord_Num_trans'' _ _ _ H4 H3 Hle). NSym.
Qed.

(* a ≺ PlusOne b ⟹ a ≼ b *)
Lemma lt_suc_imp_le : ∀ a b, Ordinal_Number a -> Ordinal_Number b ->
  a ≺ PlusOne b -> a ≼ b.
Proof.
  intros a b Ha Hb Hlt.
  destruct (Ord_Num_tri a b Ha Hb) as [H|[H|H]].
  - left; auto.
  - right; auto.
  - exfalso. New (R_Add_1 a b Ha Hb H).
    New (Lem123 b Hb).
    New (Ord_Num_trans'' _ _ _ Ha Hlt H0). NSym.
Qed.

(* ≼ 的传递性 *)
Lemma le_trans : ∀ a b c, Ordinal_Number c -> a ≼ b -> b ≼ c -> a ≼ c.
Proof.
  intros a b c Hc Hab Hbc. destruct Hab as [H|H].
  - destruct Hbc as [H1|H1]; [left; eapply Ord_Num_trans; eauto | left; rewrite <- H1; auto].
  - rewrite H; auto.
Qed.

(* One ≼ x ⟹ x ≠ Φ *)
Lemma one_le_ne : ∀ x, Ordinal_Number x -> One ≼ x -> x <> Φ.
Proof.
  intros x Hx Hle Hz. subst x. destruct Hle as [H|H].
  - eapply MKT16; eauto.
  - assert (HΦ : Φ ∈ One) by appA2G. rewrite H in HΦ. eapply MKT16; eauto.
Qed.

(* ≼ 的反对称性 *)
Lemma le_antisym : ∀ a b, Ordinal_Number a -> Ordinal_Number b ->
  a ≼ b -> b ≼ a -> a = b.
Proof.
  intros a b Ha Hb Hab Hba. destruct Hab as [H|H]; auto.
  destruct Hba as [H1|H1].
  - exfalso. New (Ord_Num_antisym a b Ha Hb H). contradiction.
  - auto.
Qed.

(* 分解识别器：若 M = n^e·k+r 满足底-n 分解约束，则 M 的 get_t/get_k/get_b 恰为 e,k,r。 *)
Lemma decomp_recognizer : ∀ n M e k r,
  natural_num n -> Two ≼ n -> natural_num M -> n ≼ M ->
  e ∈ ω -> k ∈ ω -> r ∈ ω ->
  One ≼ k -> k ≺ n -> r ≺ n ^ e ->
  M = n ^ e ⋅ k + r ->
  get_t n M = e /\ get_k n M = k /\ get_b n M = r.
Proof.
  intros n M e k r Hn Hn2 HM Hnm He Hk Hr Hk1 Hkn Hrb HMeq.
  New (nat_Ord _ Hn). New (nat_Ord _ HM). New (nat_Ord _ He).
  New (nat_Ord _ Hk). New (nat_Ord _ Hr).
  rename H into HnO. rename H0 into HMO. rename H1 into HeO.
  rename H2 into HkO. rename H3 into HrO.
  New (Two_le_One_lt _ Hn Hn2).
  assert (Hne_O : Ordinal_Number (n ^ e)) by (apply R_Exp_in_R; auto).
  assert (Hnek_O : Ordinal_Number (n ^ e ⋅ k)) by (apply R_Mult_in_R; auto).
  assert (Hkne : k <> Φ) by (apply one_le_ne; auto).
  assert (Hge : n ^ e ≼ M).
  { apply (le_trans (n ^ e) (n ^ e ⋅ k) M HMO).
    - apply R_Mult_1; auto.
    - rewrite HMeq. apply R_Add_3'; auto. }
  assert (Hlt : M ≺ n ^ (PlusOne e)).
  { rewrite HMeq, Exp_R_Suc; auto. apply Mult_Union'; auto. }
  assert (Hone_le_M : One ≼ M).
  { apply (le_trans One n M HMO); [left; auto | auto]. }
  New (CNF_1 n M HnO HMO H Hone_le_M). destruct H0 as [_ Hmx_le].
  New (MaxinExp_maximal n M Hn HM Hnm Hn2).
  New (MaxinExp_in_ω n M Hn HM Hnm Hn2).
  rename H0 into Hmax. rename H1 into Hmxω.
  set (Mx := MaxinExp n M) in *.
  assert (HMxO : Ordinal_Number Mx) by (apply nat_Ord; auto).
  assert (HMxe : Mx ≼ e).
  { New (R_Exp_in_R n (PlusOne e) HnO (Lem123 e HeO)).
    New (Ord_Num_trans' _ _ _ H0 Hmx_le Hlt).
    New (Exp_R_PrOrder_b Mx (PlusOne e) n HMxO (Lem123 e HeO) HnO H H1).
    apply lt_suc_imp_le; auto. }
  assert (HeMx : e ≼ Mx).
  { New (R_Exp_in_R n (PlusOne Mx) HnO (Lem123 Mx HMxO)).
    New (Ord_Num_trans' _ _ _ H0 Hge Hmax).
    New (Exp_R_PrOrder_b e (PlusOne Mx) n HeO (Lem123 Mx HMxO) HnO H H1).
    apply lt_suc_imp_le; auto. }
  assert (Hte : get_t n M = e).
  { unfold get_t. apply le_antisym; auto. }
  New (cnf_spec n M Hn HM Hnm Hn2).
  destruct H0 as [Hdec [_ [_ [Hblt [_ [Hkω Hbω]]]]]].
  rewrite Hte in Hdec, Hblt.
  New (nat_Ord _ Hkω). New (nat_Ord _ Hbω).
  assert (Heqq : n ^ e ⋅ (get_k n M) + (get_b n M) = n ^ e ⋅ k + r).
  { rewrite <- Hdec. exact HMeq. }
  New (cnf_decomp_unique (n ^ e) (get_k n M) (get_b n M) k r
        Hne_O H0 H1 HkO HrO Hblt Hrb Heqq).
  destruct H2 as [Hkk Hbb].
  split; [exact Hte | split; [exact Hkk | exact Hbb]].
Qed.

(* fₙ(n^s) = ω^{fₙ s}（s≥1）：n^s 的底-n 分解为 n^s·1+0，经识别器化简。 *)
Lemma fn_pow : ∀ n s, natural_num n -> Two ≼ n -> s ∈ ω -> One ≼ s ->
  fn n (n ^ s) = ω ^ (fn n s).
Proof.
  intros n s Hn Hn2 Hs Hs1.
  New (nat_Ord _ Hn). New (nat_Ord _ Hs).
  rename H into HnO. rename H0 into HsO.
  New (Two_le_One_lt _ Hn Hn2).
  assert (Hns_ω : n ^ s ∈ ω) by (apply ω_Exp_in_ω; auto).
  assert (Hns_O : Ordinal_Number (n ^ s)) by (apply R_Exp_in_R; auto).
  assert (HΦn : Φ ≺ n). { assert (Φ ≺ One) by appA2G. eapply Ord_Num_trans; eauto. }
  assert (Hn_le : n ≼ n ^ s).
  { destruct Hs1 as [Hlt1|Heq1].
    - left. New (Exp_R_PrOrder_a One s n (Lem123 Φ Φ_is_Ord) HsO HnO H Hlt1).
      New (Exp_R_PlusOneΦ_r n HnO). rewrite H1 in H0. exact H0.
    - New (Exp_R_PlusOneΦ_r n HnO). rewrite <- Heq1, H0; right; auto. }
  assert (HMeq : n ^ s = n ^ s ⋅ One + Φ).
  { rewrite Mult_R_PlusOneΦ; auto. rewrite Add_R_Φ_r; auto. }
  assert (HΦ_lt : Φ ≺ n ^ s) by (apply R_Exp_3'; auto).
  New (decomp_recognizer n (n ^ s) s One Φ Hn Hn2 Hns_ω Hn_le Hs
        (MKT134 MKT135a) MKT135a (or_intror eq_refl) H HΦ_lt HMeq).
  destruct H0 as [Hgt [Hgk Hgb]].
  New (fn_spec n Hn Hn2). destruct H0 as [Hfn_R [Hfn_lt Hfn_rec]].
  rewrite (Hfn_rec (n ^ s) Hns_ω Hn_le).
  rewrite Hgt, Hgk, Hgb.
  assert (HfΦ : fn n Φ = Φ) by (apply Hfn_lt; [apply MKT135a | exact HΦn]).
  rewrite HfΦ.
  assert (HfsR : fn n s ∈ R) by (apply Hfn_R; auto).
  pose proof MKT138 as Hω.
  assert (HωfsR : Ordinal_Number (ω ^ (fn n s))) by (apply R_Exp_in_R; auto).
  rewrite Mult_R_PlusOneΦ; auto. rewrite Add_R_Φ_r; auto.
Qed.

(* One ≼ x ⟹ One ≼ fₙ x *)
Lemma fn_ge_one : ∀ n x, natural_num n -> Two ≼ n -> x ∈ ω -> One ≼ x ->
  One ≼ fn n x.
Proof.
  intros n x Hn Hn2 Hx Hx1.
  New (nat_Ord _ Hn). rename H into HnO.
  New (Two_le_One_lt _ Hn Hn2).
  New (fn_spec n Hn Hn2). destruct H0 as [Hfn_R [Hfn_lt Hfn_rec]].
  TF (x ≺ n).
  - rewrite (Hfn_lt x Hx H0). exact Hx1.
  - assert (Hge : n ≼ x).
    { destruct (Ord_Num_tri x n (nat_Ord _ Hx) HnO) as [Hc|[Hc|Hc]]; try contradiction.
      - right; auto.
      - left; auto. }
    rewrite (Hfn_rec x Hx Hge).
    set (t := get_t n x). set (k := get_k n x). set (b := get_b n x).
    New (cnf_spec n x Hn Hx Hge Hn2).
    destruct H1 as [_ [Hk1 [_ [_ [Ht1 [Hkω Hbω]]]]]].
    assert (Htω : t ∈ ω) by (apply MaxinExp_in_ω; auto).
    assert (HftR : fn n t ∈ R) by (apply Hfn_R; auto).
    assert (HfbR : fn n b ∈ R) by (apply Hfn_R; auto).
    pose proof MKT138 as Hω.
    assert (HωftR : Ordinal_Number (ω ^ (fn n t))) by (apply R_Exp_in_R; auto).
    assert (Hmid : Ordinal_Number (ω ^ (fn n t) ⋅ k)) by (apply R_Mult_in_R; auto; apply nat_Ord; auto).
    assert (Hfull : Ordinal_Number (ω ^ (fn n t) ⋅ k + fn n b)) by (apply R_Add_in_R; auto).
    assert (HΦlt : Φ ≺ ω ^ (fn n t)) by (apply (R_Exp_3' (fn n t) ω HftR Hω (MKT134 MKT135a))).
    assert (HoneE : One ≼ ω ^ (fn n t)) by (apply R_Add_1; auto; apply Φ_is_Ord).
    apply (le_trans One (ω ^ (fn n t)) _ Hfull); auto.
    apply (le_trans (ω ^ (fn n t)) (ω ^ (fn n t) ⋅ k) _ Hfull).
    + apply R_Mult_1; auto. apply nat_Ord; auto. apply one_le_ne; auto. apply nat_Ord; auto.
    + apply R_Add_3'; auto.
Qed.

(* n ≼ x ⟹ ω ≼ fₙ x *)
Lemma fn_ge_omega : ∀ n x, natural_num n -> Two ≼ n -> x ∈ ω -> n ≼ x ->
  ω ≼ fn n x.
Proof.
  intros n x Hn Hn2 Hx Hge.
  New (nat_Ord _ Hn). rename H into HnO.
  New (Two_le_One_lt _ Hn Hn2).
  New (fn_spec n Hn Hn2). destruct H0 as [Hfn_R [Hfn_lt Hfn_rec]].
  rewrite (Hfn_rec x Hx Hge).
  set (t := get_t n x). set (k := get_k n x). set (b := get_b n x).
  New (cnf_spec n x Hn Hx Hge Hn2).
  destruct H0 as [_ [Hk1 [_ [_ [Ht1 [Hkω Hbω]]]]]].
  assert (Htω : t ∈ ω) by (apply MaxinExp_in_ω; auto).
  assert (HftR : fn n t ∈ R) by (apply Hfn_R; auto).
  assert (HfbR : fn n b ∈ R) by (apply Hfn_R; auto).
  pose proof MKT138 as Hω.
  assert (HωftR : Ordinal_Number (ω ^ (fn n t))) by (apply R_Exp_in_R; auto).
  assert (Hmid : Ordinal_Number (ω ^ (fn n t) ⋅ k)) by (apply R_Mult_in_R; auto; apply nat_Ord; auto).
  assert (Hfull : Ordinal_Number (ω ^ (fn n t) ⋅ k + fn n b)) by (apply R_Add_in_R; auto).
  assert (Hft1 : One ≼ fn n t) by (apply fn_ge_one; auto).
  assert (Hωle : ω ≼ ω ^ (fn n t)).
  { New (Exp_R_PlusOneΦ_r ω Hω).
    destruct Hft1 as [Hlt1|Heq1].
    - left. New (Exp_R_PrOrder_a One (fn n t) ω (Lem123 Φ Φ_is_Ord) HftR Hω (MKT134 MKT135a) Hlt1).
      rewrite H0 in H1. exact H1.
    - rewrite <- Heq1, H0; right; auto. }
  apply (le_trans ω (ω ^ (fn n t)) _ Hfull); auto.
  apply (le_trans (ω ^ (fn n t)) (ω ^ (fn n t) ⋅ k) _ Hfull).
  - apply R_Mult_1; auto. apply nat_Ord; auto. apply one_le_ne; auto. apply nat_Ord; auto.
  - apply R_Add_3'; auto.
Qed.

(* 4.5.5(1)：fₙ 严格单调递增。强归纳 + (t,k,b) 三元组字典序。 *)
Lemma fn_mono : ∀ n, natural_num n -> Two ≼ n ->
  ∀ mp, mp ∈ ω -> ∀ m, m ∈ mp -> fn n m ≺ fn n mp.
Proof.
  intros n Hn Hn2.
  New (nat_Ord _ Hn). rename H into HnO.
  New (Two_le_One_lt _ Hn Hn2). rename H into Hn1.
  New (fn_spec n Hn Hn2). destruct H as [Hfn_R [Hfn_lt Hfn_rec]].
  pose proof MKT138 as Hω.
  assert (Hone_lt_ω : One ≺ ω) by (apply (MKT134 MKT135a)).
  assert (Hstep : ∀ mp, mp ∈ ω ->
    (∀ j, j ≺ mp -> ∀ i, i ∈ j -> fn n i ≺ fn n j) ->
    ∀ m, m ∈ mp -> fn n m ≺ fn n mp).
  { intros mp Hmp IH m Hm.
    assert (HmpO : Ordinal_Number mp) by (apply nat_Ord; auto).
    assert (Hmω : m ∈ ω) by (appA2H Hmp; appA2G; eapply MKT132; eauto).
    assert (HmO : Ordinal_Number m) by (apply nat_Ord; auto).
    TF (mp ≺ n).
    - assert (Hmn : m ≺ n) by (apply (Ord_Num_trans m mp n HnO Hm H)).
      rewrite (Hfn_lt m Hmω Hmn), (Hfn_lt mp Hmp H). exact Hm.
    - assert (Hgemp : n ≼ mp).
      { destruct (Ord_Num_tri mp n HmpO HnO) as [Hc|[Hc|Hc]]; try contradiction;
        [right; auto | left; auto]. }
      TF (m ≺ n).
      + rewrite (Hfn_lt m Hmω H0).
        assert (Homega : ω ≼ fn n mp) by (apply fn_ge_omega; auto).
        assert (HfmpR : fn n mp ∈ R) by (apply Hfn_R; auto).
        exact (Ord_Num_trans'' m ω (fn n mp) HfmpR Hmω Homega).
      + assert (Hgem : n ≼ m).
        { destruct (Ord_Num_tri m n HmO HnO) as [Hc|[Hc|Hc]]; try contradiction;
          [right; auto | left; auto]. }
        New (cnf_spec n m Hn Hmω Hgem Hn2).
        destruct H1 as [Hdecm [Hk1m [Hknm [Hbltm [Ht1m [Hkωm Hbωm]]]]]].
        New (cnf_spec n mp Hn Hmp Hgemp Hn2).
        destruct H1 as [Hdecmp [Hk1mp [Hknmp [Hbltmp [Ht1mp [Hkωmp Hbωmp]]]]]].
        rewrite (Hfn_rec m Hmω Hgem), (Hfn_rec mp Hmp Hgemp).
        set (t := get_t n m) in *. set (k := get_k n m) in *. set (b := get_b n m) in *.
        set (tp := get_t n mp) in *. set (kp := get_k n mp) in *. set (bp := get_b n mp) in *.
        assert (Htω : t ∈ ω) by (apply MaxinExp_in_ω; auto).
        assert (Htpω : tp ∈ ω) by (apply MaxinExp_in_ω; auto).
        assert (HtO : Ordinal_Number t) by (apply nat_Ord; auto).
        assert (HtpO : Ordinal_Number tp) by (apply nat_Ord; auto).
        assert (HkO : Ordinal_Number k) by (apply nat_Ord; auto).
        assert (HkpO : Ordinal_Number kp) by (apply nat_Ord; auto).
        assert (HbO : Ordinal_Number b) by (apply nat_Ord; auto).
        assert (HbpO : Ordinal_Number bp) by (apply nat_Ord; auto).
        assert (HftR : fn n t ∈ R) by (apply Hfn_R; auto).
        assert (HftpR : fn n tp ∈ R) by (apply Hfn_R; auto).
        assert (HfbR : fn n b ∈ R) by (apply Hfn_R; auto).
        assert (HfbpR : fn n bp ∈ R) by (apply Hfn_R; auto).
        assert (Htp_lt_mp : tp ≺ mp) by (apply cnf_t_lt_m; auto).
        assert (Hbp_lt_mp : bp ≺ mp) by (apply cnf_b_lt_m; auto).
        assert (Hone_le_m : One ≼ m) by (apply (le_trans One n m HmO); [left; auto | auto]).
        New (CNF_1 n m HnO HmO Hn1 Hone_le_m). destruct H1 as [_ Hnt_le_m].
        assert (Hnt_lt_mp : n ^ t ≺ mp) by (apply (Ord_Num_trans' (n ^ t) m mp HmpO Hnt_le_m Hm)).
        assert (Hbound : fn n b ≺ ω ^ (fn n t)).
        { New (IH (n ^ t) Hnt_lt_mp b Hbltm).
          assert (Hfnpow : fn n (n ^ t) = ω ^ (fn n t)) by (apply fn_pow; auto).
          rewrite Hfnpow in H1. exact H1. }
        assert (Hmpm : (tp ≺ t \/ (tp = t /\ kp ≺ k) \/ (tp = t /\ kp = k /\ bp ≺ b)) -> False).
        { intro D.
          New (top_term_lt n tp t kp k bp b HnO Hn1 HtpO HtO HkpO HkO HbpO HbO Hknmp Hk1m Hbltmp D).
          rewrite <- Hdecmp, <- Hdecm in H1.
          New (Ord_Num_antisym m mp HmO HmpO Hm). contradiction. }
        assert (Hlex : (fn n t ≺ fn n tp) \/ (fn n t = fn n tp /\ k ≺ kp)
                     \/ (fn n t = fn n tp /\ k = kp /\ fn n b ≺ fn n bp)).
        { destruct (Ord_Num_tri t tp HtO HtpO) as [Htt1|[Htt2|Htt3]].
          - left. apply (IH tp Htp_lt_mp t Htt1).
          - destruct (Ord_Num_tri k kp HkO HkpO) as [Hkk1|[Hkk2|Hkk3]].
            + right; left; split; [rewrite Htt2; auto | exact Hkk1].
            + destruct (Ord_Num_tri b bp HbO HbpO) as [Hbb1|[Hbb2|Hbb3]].
              * right; right; split; [rewrite Htt2; auto | split; [exact Hkk2 | apply (IH bp Hbp_lt_mp b Hbb1)]].
              * exfalso. assert (Hmm : m = mp).
                { rewrite Hdecm, Hdecmp, Htt2, Hkk2, Hbb2; auto. }
                rewrite Hmm in Hm. eapply MKT101; eauto.
              * exfalso. apply Hmpm. right; right; split;
                [symmetry; exact Htt2 | split; [symmetry; exact Hkk2 | exact Hbb3]].
            + exfalso. apply Hmpm. right; left; split; [symmetry; exact Htt2 | exact Hkk3].
          - exfalso. apply Hmpm. left; auto. }
        apply top_term_lt; auto.
  }
  intros mp Hmp.
  apply (The_Second_Mathematical_Induction
           (fun mp => ∀ m, m ∈ mp -> fn n m ≺ fn n mp)); auto.
  intros m Hm. exfalso. eapply (@MKT16 m); auto.
Qed.

(* One ≼ x ⟹ One ≼ Sₙ x *)
Lemma Sn_ge_one : ∀ n x, natural_num n -> Two ≼ n -> x ∈ ω -> One ≼ x ->
  One ≼ Sn n x.
Proof.
  intros n x Hn Hn2 Hx Hx1.
  New (nat_Ord _ Hn). rename H into HnO.
  New (Two_le_One_lt _ Hn Hn2). rename H into Hn1.
  assert (HsO : Ordinal_Number (PlusOne n)) by (apply Lem123; auto).
  assert (Hn1' : One ≺ PlusOne n).
  { assert (Hnn : n ≺ PlusOne n) by appA2G. apply (Ord_Num_trans One n (PlusOne n) HsO Hn1 Hnn). }
  assert (Hsω : PlusOne n ∈ ω) by (apply MKT134; auto).
  New (Sn_spec n Hn Hn2). destruct H as [Hsn_ω [Hsn_lt Hsn_rec]].
  TF (x ≺ n).
  - rewrite (Hsn_lt x Hx H). exact Hx1.
  - assert (Hge : n ≼ x).
    { destruct (Ord_Num_tri x n (nat_Ord _ Hx) HnO) as [Hc|[Hc|Hc]]; try contradiction;
      [right; auto | left; auto]. }
    rewrite (Hsn_rec x Hx Hge).
    set (t := get_t n x). set (k := get_k n x). set (b := get_b n x).
    New (cnf_spec n x Hn Hx Hge Hn2).
    destruct H0 as [_ [Hk1 [_ [_ [Ht1 [Hkω Hbω]]]]]].
    assert (Htω : t ∈ ω) by (apply MaxinExp_in_ω; auto).
    assert (Hstω : Sn n t ∈ ω) by (apply Hsn_ω; auto).
    assert (Hsbω : Sn n b ∈ ω) by (apply Hsn_ω; auto).
    assert (HExpω : (PlusOne n) ^ (Sn n t) ∈ ω) by (apply ω_Exp_in_ω; auto).
    assert (HExpO : Ordinal_Number ((PlusOne n) ^ (Sn n t))) by (apply nat_Ord; auto).
    assert (Hmid : Ordinal_Number ((PlusOne n) ^ (Sn n t) ⋅ k)) by (apply R_Mult_in_R; [exact HExpO | apply nat_Ord; auto]).
    assert (Hfull : Ordinal_Number ((PlusOne n) ^ (Sn n t) ⋅ k + Sn n b)) by (apply R_Add_in_R; [exact Hmid | apply nat_Ord; auto]).
    assert (HΦlt : Φ ≺ (PlusOne n) ^ (Sn n t)) by (apply (R_Exp_3' (Sn n t) (PlusOne n) (nat_Ord _ Hstω) HsO Hn1')).
    assert (HoneE : One ≼ (PlusOne n) ^ (Sn n t)) by (apply R_Add_1; auto; apply Φ_is_Ord).
    apply (le_trans One ((PlusOne n) ^ (Sn n t)) _ Hfull); auto.
    apply (le_trans ((PlusOne n) ^ (Sn n t)) ((PlusOne n) ^ (Sn n t) ⋅ k) _ Hfull).
    + apply R_Mult_1; [exact HExpO | apply nat_Ord; auto | apply one_le_ne; [apply nat_Ord; auto | exact Hk1]].
    + apply R_Add_3'; [exact Hmid | apply nat_Ord; auto].
Qed.

(* n ≼ x ⟹ (n+1) ≼ Sₙ x *)
Lemma Sn_ge_succ : ∀ n x, natural_num n -> Two ≼ n -> x ∈ ω -> n ≼ x ->
  (PlusOne n) ≼ Sn n x.
Proof.
  intros n x Hn Hn2 Hx Hge.
  New (nat_Ord _ Hn). rename H into HnO.
  New (Two_le_One_lt _ Hn Hn2). rename H into Hn1.
  assert (HsO : Ordinal_Number (PlusOne n)) by (apply Lem123; auto).
  assert (Hn1' : One ≺ PlusOne n).
  { assert (Hnn : n ≺ PlusOne n) by appA2G. apply (Ord_Num_trans One n (PlusOne n) HsO Hn1 Hnn). }
  assert (Hsω : PlusOne n ∈ ω) by (apply MKT134; auto).
  New (Sn_spec n Hn Hn2). destruct H as [Hsn_ω [Hsn_lt Hsn_rec]].
  rewrite (Hsn_rec x Hx Hge).
  set (t := get_t n x). set (k := get_k n x). set (b := get_b n x).
  New (cnf_spec n x Hn Hx Hge Hn2).
  destruct H as [_ [Hk1 [_ [_ [Ht1 [Hkω Hbω]]]]]].
  assert (Htω : t ∈ ω) by (apply MaxinExp_in_ω; auto).
  assert (Hstω : Sn n t ∈ ω) by (apply Hsn_ω; auto).
  assert (Hsbω : Sn n b ∈ ω) by (apply Hsn_ω; auto).
  assert (HExpω : (PlusOne n) ^ (Sn n t) ∈ ω) by (apply ω_Exp_in_ω; auto).
  assert (HExpO : Ordinal_Number ((PlusOne n) ^ (Sn n t))) by (apply nat_Ord; auto).
  assert (Hmid : Ordinal_Number ((PlusOne n) ^ (Sn n t) ⋅ k)) by (apply R_Mult_in_R; [exact HExpO | apply nat_Ord; auto]).
  assert (Hfull : Ordinal_Number ((PlusOne n) ^ (Sn n t) ⋅ k + Sn n b)) by (apply R_Add_in_R; [exact Hmid | apply nat_Ord; auto]).
  assert (Hst1 : One ≼ Sn n t) by (apply Sn_ge_one; auto).
  assert (Hsle : (PlusOne n) ≼ (PlusOne n) ^ (Sn n t)).
  { pose proof (Exp_R_PlusOneΦ_r (PlusOne n) HsO) as HpowOne.
    destruct Hst1 as [Hlt1|Heq1].
    - left. pose proof (Exp_R_PrOrder_a One (Sn n t) (PlusOne n) (Lem123 Φ Φ_is_Ord) (nat_Ord _ Hstω) HsO Hn1' Hlt1) as Hmono.
      rewrite HpowOne in Hmono. exact Hmono.
    - rewrite <- Heq1, HpowOne; right; auto. }
  apply (le_trans (PlusOne n) ((PlusOne n) ^ (Sn n t)) _ Hfull); auto.
  apply (le_trans ((PlusOne n) ^ (Sn n t)) ((PlusOne n) ^ (Sn n t) ⋅ k) _ Hfull).
  - apply R_Mult_1; [exact HExpO | apply nat_Ord; auto | apply one_le_ne; [apply nat_Ord; auto | exact Hk1]].
  - apply R_Add_3'; [exact Hmid | apply nat_Ord; auto].
Qed.

(* Sₙ(n^s) = (n+1)^{Sₙ s}（s≥1）：n^s 的底-n 分解经识别器化简。 *)
Lemma Sn_pow : ∀ n s, natural_num n -> Two ≼ n -> s ∈ ω -> One ≼ s ->
  Sn n (n ^ s) = (PlusOne n) ^ (Sn n s).
Proof.
  intros n s Hn Hn2 Hs Hs1.
  New (nat_Ord _ Hn). New (nat_Ord _ Hs).
  rename H into HnO. rename H0 into HsO.
  New (Two_le_One_lt _ Hn Hn2). rename H into Hn1.
  assert (HsucO : Ordinal_Number (PlusOne n)) by (apply Lem123; auto).
  assert (Hns_ω : n ^ s ∈ ω) by (apply ω_Exp_in_ω; auto).
  assert (Hns_O : Ordinal_Number (n ^ s)) by (apply R_Exp_in_R; auto).
  assert (HΦn : Φ ≺ n). { assert (Φ ≺ One) by appA2G. eapply Ord_Num_trans; eauto. }
  assert (Hn_le : n ≼ n ^ s).
  { destruct Hs1 as [Hlt1|Heq1].
    - left. pose proof (Exp_R_PrOrder_a One s n (Lem123 Φ Φ_is_Ord) HsO HnO Hn1 Hlt1) as Hm1.
      pose proof (Exp_R_PlusOneΦ_r n HnO) as Hp1. rewrite Hp1 in Hm1. exact Hm1.
    - pose proof (Exp_R_PlusOneΦ_r n HnO) as Hp1. rewrite <- Heq1, Hp1; right; auto. }
  assert (HMeq : n ^ s = n ^ s ⋅ One + Φ).
  { rewrite Mult_R_PlusOneΦ; auto. rewrite Add_R_Φ_r; auto. }
  assert (HΦ_lt : Φ ≺ n ^ s) by (apply R_Exp_3'; auto).
  New (decomp_recognizer n (n ^ s) s One Φ Hn Hn2 Hns_ω Hn_le Hs
        (MKT134 MKT135a) MKT135a (or_intror eq_refl) Hn1 HΦ_lt HMeq).
  destruct H as [Hgt [Hgk Hgb]].
  New (Sn_spec n Hn Hn2). destruct H as [Hsn_ω [Hsn_lt Hsn_rec]].
  rewrite (Hsn_rec (n ^ s) Hns_ω Hn_le).
  rewrite Hgt, Hgk, Hgb.
  assert (HsΦ : Sn n Φ = Φ) by (apply Hsn_lt; [apply MKT135a | exact HΦn]).
  rewrite HsΦ.
  assert (Hssω : Sn n s ∈ ω) by (apply Hsn_ω; auto).
  assert (HExpO : Ordinal_Number ((PlusOne n) ^ (Sn n s))) by (apply R_Exp_in_R; [exact HsucO | apply nat_Ord; auto]).
  rewrite Mult_R_PlusOneΦ; auto. rewrite Add_R_Φ_r; auto.
Qed.

(* 4.5.5(1) 镜像：Sₙ 严格单调递增。 *)
Lemma Sn_mono : ∀ n, natural_num n -> Two ≼ n ->
  ∀ mp, mp ∈ ω -> ∀ m, m ∈ mp -> Sn n m ≺ Sn n mp.
Proof.
  intros n Hn Hn2.
  New (nat_Ord _ Hn). rename H into HnO.
  New (Two_le_One_lt _ Hn Hn2). rename H into Hn1.
  New (Sn_spec n Hn Hn2). destruct H as [Hsn_ω [Hsn_lt Hsn_rec]].
  assert (HsucO : Ordinal_Number (PlusOne n)) by (apply Lem123; auto).
  assert (Hnn' : n ≺ PlusOne n) by appA2G.
  assert (Hn1' : One ≺ PlusOne n) by (apply (Ord_Num_trans One n (PlusOne n) HsucO Hn1 Hnn')).
  assert (Hstep : ∀ mp, mp ∈ ω ->
    (∀ j, j ≺ mp -> ∀ i, i ∈ j -> Sn n i ≺ Sn n j) ->
    ∀ m, m ∈ mp -> Sn n m ≺ Sn n mp).
  { intros mp Hmp IH m Hm.
    assert (HmpO : Ordinal_Number mp) by (apply nat_Ord; auto).
    assert (Hmω : m ∈ ω) by (appA2H Hmp; appA2G; eapply MKT132; eauto).
    assert (HmO : Ordinal_Number m) by (apply nat_Ord; auto).
    TF (mp ≺ n).
    - assert (Hmn : m ≺ n) by (apply (Ord_Num_trans m mp n HnO Hm H)).
      rewrite (Hsn_lt m Hmω Hmn), (Hsn_lt mp Hmp H). exact Hm.
    - assert (Hgemp : n ≼ mp).
      { destruct (Ord_Num_tri mp n HmpO HnO) as [Hc|[Hc|Hc]]; try contradiction;
        [right; auto | left; auto]. }
      TF (m ≺ n).
      + rewrite (Hsn_lt m Hmω H0).
        assert (Hsucc : (PlusOne n) ≼ Sn n mp) by (apply Sn_ge_succ; auto).
        assert (HsmpO : Ordinal_Number (Sn n mp)) by (apply nat_Ord; apply Hsn_ω; auto).
        assert (Hm_lt_s : m ≺ PlusOne n) by (apply (Ord_Num_trans m n (PlusOne n) HsucO H0 Hnn')).
        exact (Ord_Num_trans'' m (PlusOne n) (Sn n mp) HsmpO Hm_lt_s Hsucc).
      + assert (Hgem : n ≼ m).
        { destruct (Ord_Num_tri m n HmO HnO) as [Hc|[Hc|Hc]]; try contradiction;
          [right; auto | left; auto]. }
        New (cnf_spec n m Hn Hmω Hgem Hn2).
        destruct H1 as [Hdecm [Hk1m [Hknm [Hbltm [Ht1m [Hkωm Hbωm]]]]]].
        New (cnf_spec n mp Hn Hmp Hgemp Hn2).
        destruct H1 as [Hdecmp [Hk1mp [Hknmp [Hbltmp [Ht1mp [Hkωmp Hbωmp]]]]]].
        rewrite (Hsn_rec m Hmω Hgem), (Hsn_rec mp Hmp Hgemp).
        set (t := get_t n m) in *. set (k := get_k n m) in *. set (b := get_b n m) in *.
        set (tp := get_t n mp) in *. set (kp := get_k n mp) in *. set (bp := get_b n mp) in *.
        assert (Htω : t ∈ ω) by (apply MaxinExp_in_ω; auto).
        assert (Htpω : tp ∈ ω) by (apply MaxinExp_in_ω; auto).
        assert (HtO : Ordinal_Number t) by (apply nat_Ord; auto).
        assert (HtpO : Ordinal_Number tp) by (apply nat_Ord; auto).
        assert (HkO : Ordinal_Number k) by (apply nat_Ord; auto).
        assert (HkpO : Ordinal_Number kp) by (apply nat_Ord; auto).
        assert (HbO : Ordinal_Number b) by (apply nat_Ord; auto).
        assert (HbpO : Ordinal_Number bp) by (apply nat_Ord; auto).
        assert (HstO : Ordinal_Number (Sn n t)) by (apply nat_Ord; apply Hsn_ω; auto).
        assert (HstpO : Ordinal_Number (Sn n tp)) by (apply nat_Ord; apply Hsn_ω; auto).
        assert (HsbO : Ordinal_Number (Sn n b)) by (apply nat_Ord; apply Hsn_ω; auto).
        assert (HsbpO : Ordinal_Number (Sn n bp)) by (apply nat_Ord; apply Hsn_ω; auto).
        assert (Hk_lt_s : k ≺ PlusOne n) by (apply (Ord_Num_trans k n (PlusOne n) HsucO Hknm Hnn')).
        assert (Htp_lt_mp : tp ≺ mp) by (apply cnf_t_lt_m; auto).
        assert (Hbp_lt_mp : bp ≺ mp) by (apply cnf_b_lt_m; auto).
        assert (Hone_le_m : One ≼ m) by (apply (le_trans One n m HmO); [left; auto | auto]).
        New (CNF_1 n m HnO HmO Hn1 Hone_le_m). destruct H1 as [_ Hnt_le_m].
        assert (Hnt_lt_mp : n ^ t ≺ mp) by (apply (Ord_Num_trans' (n ^ t) m mp HmpO Hnt_le_m Hm)).
        assert (Hbound : Sn n b ≺ (PlusOne n) ^ (Sn n t)).
        { New (IH (n ^ t) Hnt_lt_mp b Hbltm).
          assert (Hsnpow : Sn n (n ^ t) = (PlusOne n) ^ (Sn n t)) by (apply Sn_pow; auto).
          rewrite Hsnpow in H1. exact H1. }
        assert (Hmpm : (tp ≺ t \/ (tp = t /\ kp ≺ k) \/ (tp = t /\ kp = k /\ bp ≺ b)) -> False).
        { intro D.
          New (top_term_lt n tp t kp k bp b HnO Hn1 HtpO HtO HkpO HkO HbpO HbO Hknmp Hk1m Hbltmp D).
          rewrite <- Hdecmp, <- Hdecm in H1.
          New (Ord_Num_antisym m mp HmO HmpO Hm). contradiction. }
        assert (Hlex : (Sn n t ≺ Sn n tp) \/ (Sn n t = Sn n tp /\ k ≺ kp)
                     \/ (Sn n t = Sn n tp /\ k = kp /\ Sn n b ≺ Sn n bp)).
        { destruct (Ord_Num_tri t tp HtO HtpO) as [Htt1|[Htt2|Htt3]].
          - left. apply (IH tp Htp_lt_mp t Htt1).
          - destruct (Ord_Num_tri k kp HkO HkpO) as [Hkk1|[Hkk2|Hkk3]].
            + right; left; split; [rewrite Htt2; auto | exact Hkk1].
            + destruct (Ord_Num_tri b bp HbO HbpO) as [Hbb1|[Hbb2|Hbb3]].
              * right; right; split; [rewrite Htt2; auto | split; [exact Hkk2 | apply (IH bp Hbp_lt_mp b Hbb1)]].
              * exfalso. assert (Hmm : m = mp).
                { rewrite Hdecm, Hdecmp, Htt2, Hkk2, Hbb2; auto. }
                rewrite Hmm in Hm. eapply MKT101; eauto.
              * exfalso. apply Hmpm. right; right; split;
                [symmetry; exact Htt2 | split; [symmetry; exact Hkk2 | exact Hbb3]].
            + exfalso. apply Hmpm. right; left; split; [symmetry; exact Htt2 | exact Hkk3].
          - exfalso. apply Hmpm. left; auto. }
        apply top_term_lt; auto.
  }
  intros mp Hmp.
  apply (The_Second_Mathematical_Induction
           (fun mp => ∀ m, m ∈ mp -> Sn n m ≺ Sn n mp)); auto.
  intros m Hm. exfalso. eapply (@MKT16 m); auto.
Qed.

(* 界引理 4.5.5 前置：b < n^t ⟹ Sₙ(b) < (n+1)^{Sₙ t}。由 Sn_mono + Sn_pow。 *)
Lemma Sn_bound : ∀ n t b, natural_num n -> Two ≼ n -> t ∈ ω -> b ∈ ω ->
  One ≼ t -> b ≺ n ^ t -> Sn n b ≺ (PlusOne n) ^ (Sn n t).
Proof.
  intros n t b Hn Hn2 Ht Hb Ht1 Hblt.
  assert (Hntω : n ^ t ∈ ω) by (apply ω_Exp_in_ω; auto).
  pose proof (Sn_mono n Hn Hn2 (n ^ t) Hntω b Hblt) as Hmono.
  pose proof (Sn_pow n t Hn Hn2 Ht Ht1) as Hpow.
  rewrite Hpow in Hmono. exact Hmono.
Qed.

(* 4.5.5(2)：f_{n+1}(Sₙ(m)) = fₙ(m)。对 m 强归纳；归纳步用 Sn_bound 识别 Sₙ(m) 的底-(n+1) 分解。 *)
Lemma fn_Sn : ∀ n, natural_num n -> Two ≼ n ->
  ∀ m, m ∈ ω -> fn (PlusOne n) (Sn n m) = fn n m.
Proof.
  intros n Hn Hn2.
  New (nat_Ord _ Hn). rename H into HnO.
  New (Two_le_One_lt _ Hn Hn2). rename H into Hn1.
  assert (HsucN : natural_num (PlusOne n)) by (apply MKT134; auto).
  assert (HsucO : Ordinal_Number (PlusOne n)) by (apply Lem123; auto).
  assert (Hnn' : n ≺ PlusOne n) by appA2G.
  assert (Hn2' : Two ≼ PlusOne n) by (left; apply (Ord_Num_trans' Two n (PlusOne n) HsucO Hn2 Hnn')).
  New (fn_spec n Hn Hn2). destruct H as [Hfn_R [Hfn_lt Hfn_rec]].
  New (fn_spec (PlusOne n) HsucN Hn2'). destruct H as [Hfn_R' [Hfn_lt' Hfn_rec']].
  New (Sn_spec n Hn Hn2). destruct H as [Hsn_ω [Hsn_lt Hsn_rec]].
  assert (Hstep : ∀ m, m ∈ ω -> (∀ j, j ≺ m -> fn (PlusOne n) (Sn n j) = fn n j)
    -> fn (PlusOne n) (Sn n m) = fn n m).
  { intros m Hm IH.
    assert (HmO : Ordinal_Number m) by (apply nat_Ord; auto).
    TF (m ≺ n).
    - rewrite (Hsn_lt m Hm H).
      assert (Hmsuc : m ≺ PlusOne n) by (apply (Ord_Num_trans m n (PlusOne n) HsucO H Hnn')).
      rewrite (Hfn_lt' m Hm Hmsuc). rewrite (Hfn_lt m Hm H). auto.
    - assert (Hgem : n ≼ m).
      { destruct (Ord_Num_tri m n HmO HnO) as [Hc|[Hc|Hc]]; try contradiction;
        [right; auto | left; auto]. }
      New (cnf_spec n m Hn Hm Hgem Hn2).
      destruct H0 as [Hdecm [Hk1m [Hknm [Hbltm [Ht1m [Hkωm Hbωm]]]]]].
      set (t := get_t n m) in *. set (k := get_k n m) in *. set (b := get_b n m) in *.
      assert (Htω : t ∈ ω) by (apply MaxinExp_in_ω; auto).
      assert (Hstω : Sn n t ∈ ω) by (apply Hsn_ω; auto).
      assert (Hsbω : Sn n b ∈ ω) by (apply Hsn_ω; auto).
      assert (Hsmω : Sn n m ∈ ω) by (apply Hsn_ω; auto).
      assert (HSnm_eq : Sn n m = (PlusOne n) ^ (Sn n t) ⋅ k + Sn n b) by (exact (Hsn_rec m Hm Hgem)).
      assert (Hsucc : (PlusOne n) ≼ Sn n m) by (apply Sn_ge_succ; auto).
      assert (Hk_lt_s : k ≺ PlusOne n) by (apply (Ord_Num_trans k n (PlusOne n) HsucO Hknm Hnn')).
      assert (Hbound : Sn n b ≺ (PlusOne n) ^ (Sn n t)) by (apply Sn_bound; auto).
      New (decomp_recognizer (PlusOne n) (Sn n m) (Sn n t) k (Sn n b)
            HsucN Hn2' Hsmω Hsucc Hstω Hkωm Hsbω Hk1m Hk_lt_s Hbound HSnm_eq).
      destruct H0 as [Hgt' [Hgk' Hgb']].
      rewrite (Hfn_rec' (Sn n m) Hsmω Hsucc).
      rewrite Hgt', Hgk', Hgb'.
      assert (Ht_lt_m : t ≺ m) by (apply cnf_t_lt_m; auto).
      assert (Hb_lt_m : b ≺ m) by (apply cnf_b_lt_m; auto).
      rewrite (IH t Ht_lt_m), (IH b Hb_lt_m).
      rewrite (Hfn_rec m Hm Hgem). reflexivity.
  }
  intros m Hm.
  apply (The_Second_Mathematical_Induction
           (fun m => fn (PlusOne n) (Sn n m) = fn n m)); auto.
  apply Hstep; [apply MKT135a | intros j Hj; exfalso; eapply (@MKT16 j); eauto].
Qed.
