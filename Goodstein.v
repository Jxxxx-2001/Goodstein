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
