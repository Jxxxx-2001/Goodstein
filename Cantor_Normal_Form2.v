(* Cantor 范式唯一性 (Cantor Normal Form — Uniqueness)

   本文件在 Cantor_Normal_Form1.v 的存在性定理 CNF 的基础上，给出
   完整的、无 Admitted / 无新公理的唯一性证明。

   核心思路：
   - 支配性界 (CNF_upper / Sum_Monodc): α^γ[Φ] ≼ Sum(f α γ δ) n ≺ α^(γ[Φ]+1)。
   - 由界唯一确定首指数 γ[Φ] = MaxinExp α β (MaxinExp_unique / CNF_leadexp)。
   - 由欧氏除法唯一性 (Mult_R_PrOrder_c) 唯一确定首系数 δ[Φ] 与余项。
   - 对余项 (低一阶 CNF) 归纳，得 n、γ、δ 全等。
*)

Require Export OrdinalNum.Cantor_Normal_Form1.

(* ================================================================= *)
(*                     基础: 指数单调与首指数唯一                     *)
(* ================================================================= *)

(* 非严格指数单调: a1 ≼ a2 -> b^a1 ≼ b^a2 *)
Lemma Exp_R_LeOrder : ∀ a1 a2 b, Ordinal_Number a1 -> Ordinal_Number a2
  -> Ordinal_Number b -> PlusOne Φ ≺ b -> a1 ≼ a2 -> b ^ a1 ≼ b ^ a2.
Proof.
  intros. destruct H3. left. apply Exp_R_PrOrder_a; auto. right. subst; auto.
Qed.

(* 首指数唯一性: 若 α^v ≼ β ≺ α^(v+1)，则 MaxinExp α β = v。
   这把 MaxinExp 定为满足该区间的唯一指数。 *)
Lemma MaxinExp_unique : ∀ α β v, Ordinal_Number α -> Ordinal_Number β
  -> Ordinal_Number v -> PlusOne Φ ≺ α
  -> α ^ v ≼ β -> β ≺ α ^ (PlusOne v) -> MaxinExp α β = v.
Proof.
  intros. unfold MaxinExp.
  assert (HS: \{ λ w, α ^ w ≼ β \} = PlusOne v).
  { eqext.
    - appA2H H5. assert (Hz: Ordinal_Number z). { eapply (ONpreceq α β); eauto. }
      New (Ord_Num_tri z v Hz H1). apply MKT4. destruct H7 as [?|[?|?]].
      + left; auto.
      + right. subst. apply MKT41; eauto.
      + exfalso. apply R_Add_1 in H7; auto.
        assert (Hpv: Ordinal_Number (PlusOne v)). { apply Lem123; auto. }
        assert (Hle2: α ^ (PlusOne v) ≼ α ^ z). { apply Exp_R_LeOrder; auto. }
        assert (Hp: Ordinal_Number (α ^ (PlusOne v))). { eapply R_Exp_in_R; eauto. }
        assert (α ^ z ≺ α ^ (PlusOne v)). { eapply Ord_Num_trans'; eauto. }
        assert (α ^ (PlusOne v) ≺ α ^ (PlusOne v)). { eapply Ord_Num_trans'; eauto. }
        eapply MKT101; eauto.
    - appA2G. apply MKT4 in H5. destruct H5.
      + assert (Hz: Ordinal_Number z). { eapply (trans_Ord_Num v); eauto. }
        assert (Hle2: α ^ z ≼ α ^ v). { apply Exp_R_LeOrder; auto. left; auto. }
        destruct Hle2 as [Hle|Hle], H3 as [Hb|Hb].
        * left. eapply Ord_Num_trans; eauto.
        * left. rewrite <- Hb; auto.
        * left. rewrite Hle; auto.
        * right. rewrite Hle; auto.
      + apply MKT41 in H5; eauto. subst; auto. }
  rewrite HS. apply MKT124; auto.
Qed.

(* ================================================================= *)
(*            左移位序列 lsh: (lsh F)[u] = F[u+1]                     *)
(* ================================================================= *)

Definition lsh F := \{\ λ u v, u ∈ ∪ dom(F) /\ v = F[PlusOne u] \}\.

Lemma lsh_fun : ∀ F, Function (lsh F).
Proof.
  intros. split. apply PisRel. intros. appoA2H H. appoA2H H0. deand. subst; auto.
Qed.

Lemma lsh_value : ∀ F u, PlusOne u ∈ dom(F) -> (lsh F)[u] = F[PlusOne u].
Proof.
  intros.
  assert (Eu: Ensemble u).
  { assert (Ensemble (PlusOne u)) by eauto. unfold PlusOne in H0.
    apply AxiomIV' in H0; tauto. }
  assert (Hu: u ∈ ∪ dom(F)).
  { appA2G. exists (PlusOne u). split; auto. unfold PlusOne.
    apply MKT4. right. apply MKT41; auto. }
  assert (Es: Ensemble (F[PlusOne u])). { apply MKT19, MKT69b; auto. }
  eqext.
  - appA2H H0. apply H1. appA2G. appoA2G.
  - appA2G. intros. appA2H H1. appoA2H H2. deand. subst; auto.
Qed.

Lemma lsh_dom : ∀ F n, n ∈ ω -> dom(F) = PlusOne n -> dom(lsh F) = n.
Proof.
  intros. assert (On: Ordinal_Number n). { eapply (trans_Ord_Num ω); auto. apply MKT138. }
  assert (HU: ∪ dom(F) = n). { rewrite H0. apply MKT124; auto. }
  eqext.
  - appA2H H1. rdeHex. appoA2H H2. deand. rewrite HU in H3; auto.
  - assert (Hz: Ordinal_Number z). { eapply (trans_Ord_Num n); auto. }
    assert (Hpz: PlusOne z ∈ dom(F)). { rewrite H0. apply -> R_Add_2'; auto. }
    appA2G. exists (F[PlusOne z]). appoA2G.
    + apply MKT49a; [eauto | apply MKT19, MKT69b; auto].
    + split; [rewrite HU; auto | auto].
Qed.

Lemma lsh_ran : ∀ F n, n ∈ ω -> Function F -> dom(F) = PlusOne n -> ran(F) ⊂ R
  -> ran(lsh F) ⊂ R.
Proof.
  intros. assert (On: Ordinal_Number n). { eapply (trans_Ord_Num ω); auto. apply MKT138. }
  assert (HU: ∪ dom(F) = n). { rewrite H1. apply MKT124; auto. }
  red. intros z Hz. appA2H Hz. rdeHex. appoA2H H4. deand. subst z.
  rewrite HU in H5.
  assert (Hx: Ordinal_Number x). { eapply (trans_Ord_Num n); auto. }
  assert (Hpx: PlusOne x ∈ dom(F)). { rewrite H1. apply -> R_Add_2'; auto. }
  apply H2, Property_dm; auto.
Qed.

Lemma lsh_Monodc : ∀ γ n, n ∈ ω -> dom(γ) = PlusOne n -> Monodc_f γ
  -> Monodc_f (lsh γ).
Proof.
  intros. destruct H1 as [Hf Hmono]. split. apply lsh_fun.
  intros k1 k2 [Hk1 [Hk2 Hlt]].
  assert (Hd: dom(lsh γ) = n). { apply lsh_dom; auto. }
  rewrite Hd in Hk1, Hk2.
  assert (On: Ordinal_Number n). { eapply (trans_Ord_Num ω); auto. apply MKT138. }
  assert (Ok1: Ordinal_Number k1). { eapply (trans_Ord_Num n); auto. }
  assert (Ok2: Ordinal_Number k2). { eapply (trans_Ord_Num n); auto. }
  assert (Hpk1: PlusOne k1 ∈ dom(γ)). { rewrite H0. apply -> R_Add_2'; auto. }
  assert (Hpk2: PlusOne k2 ∈ dom(γ)). { rewrite H0. apply -> R_Add_2'; auto. }
  rewrite (lsh_value γ k1); auto. rewrite (lsh_value γ k2); auto.
  apply (Hmono (PlusOne k1) (PlusOne k2)). split; auto. split; auto.
  apply -> R_Add_2'; auto.
Qed.

(* α>1 的幂非零 *)
Lemma Exp_pos : ∀ α a, Ordinal_Number α -> Ordinal_Number a -> PlusOne Φ ≺ α
  -> α ^ a ≠ Φ.
Proof.
  intros. assert (HΦ: Φ ≺ PlusOne Φ). { apply MKT4. right. apply MKT41; eauto. }
  assert (Hα0: Φ ≺ α). { eapply Ord_Num_trans; eauto. }
  TF (a = Φ).
  - subst. rewrite Exp_R_Φ_r; auto. intro He. rewrite He in HΦ. eapply MKT101; eauto.
  - New (R_Exp_1 α a H H0 Hα0 H2). intro He. rewrite He in H3. destruct H3.
    + emf.
    + rewrite H3 in Hα0. eapply MKT101; eauto.
Qed.

Lemma Phi_in_PlusOne : ∀ n, Ordinal_Number n -> Φ ∈ PlusOne n.
Proof.
  intros. TF (n = Φ). subst. apply MKT4; right; apply MKT41; eauto.
  New (Φ_is_First_Ord n H H0). apply MKT4; left; auto.
Qed.

Lemma ransub_R : ∀ δ α, Ordinal_Number α -> ran(δ) ⊂ α -> ran(δ) ⊂ R.
Proof. intros. red. intros z Hz. apply H0 in Hz. eapply trans_Ord_Num; eauto. Qed.

Lemma lsh_ranB : ∀ F n B, n ∈ ω -> Function F -> dom(F) = PlusOne n -> ran(F) ⊂ B
  -> ran(lsh F) ⊂ B.
Proof.
  intros. assert (On: Ordinal_Number n). { eapply (trans_Ord_Num ω); auto. apply MKT138. }
  assert (HU: ∪ dom(F) = n). { rewrite H1. apply MKT124; auto. }
  red. intros z Hz. appA2H Hz. rdeHex. appoA2H H4. deand. subst z.
  rewrite HU in H5.
  assert (Hx: Ordinal_Number x). { eapply (trans_Ord_Num n); auto. }
  assert (Hpx: PlusOne x ∈ dom(F)). { rewrite H1. apply -> R_Add_2'; auto. }
  apply H2, Property_dm; auto.
Qed.

(* ================================================================= *)
(*   支配性上界: 任何 CNF 的和 ≺ α^(首指数+1)。配合 Sum_Monodc 即得    *)
(*   α^γ[Φ] ≼ Sum(f α γ δ) n ≺ α^(PlusOne γ[Φ])。                     *)
(* ================================================================= *)

Lemma CNF_upper : ∀ α, Ordinal_Number α -> PlusOne Φ ≺ α
  -> ∀ n, n ∈ ω -> ∀ γ δ, OnTo γ (PlusOne n) R -> OnTo δ (dom(γ)) α -> Monodc_f γ
  -> Sum (f α γ δ) n ≺ α ^ (PlusOne (γ[Φ])).
Proof.
  intros α H H0.
  set (p := fun n => ∀ γ δ, OnTo γ (PlusOne n) R -> OnTo δ (dom(γ)) α -> Monodc_f γ
    -> Sum (f α γ δ) n ≺ α ^ (PlusOne (γ[Φ]))).
  assert (Hmain: ∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction.
    - unfold p. intros γ δ Hγ Hδ Hmono.
      destruct Hγ as [Hγf [Hγd Hγr]]. destruct Hδ as [Hδf [Hδd Hδr]].
      assert (Hdω: dom(γ) ∈ ω). { rewrite Hγd. apply MKT134, MKT135a. }
      assert (HδR: ran(δ) ⊂ R). { eapply ransub_R; eauto. }
      assert (HΦd: Φ ∈ dom(γ)). { rewrite Hγd. apply Phi_in_PlusOne, Φ_is_Ord. }
      assert (Hγ0: Ordinal_Number (γ[Φ])). { apply Hγr, Property_dm; auto. }
      assert (Hδ0: δ[Φ] ≺ α). { apply Hδr, Property_dm; auto. rewrite Hδd; auto. }
      assert (Hδ0O: Ordinal_Number (δ[Φ])). { eapply (trans_Ord_Num α); eauto. }
      pose proof (CNF_3 α γ δ H H0 Hγf Hγr Hδf Hδd HδR) as [Hff [Hfd Hfr]].
      assert (Hfdω: dom(f α γ δ) ∈ ω). { rewrite Hfd; auto. }
      rewrite Sum_Lemma2; auto.
      rewrite (com_f_value α γ δ H H0 Hγf Hdω Hγr Hδf Hδd HδR Φ HΦd).
      rewrite Exp_R_Suc; auto.
      apply Mult_R_PrOrder_a; auto.
      + eapply R_Exp_in_R; eauto.
      + apply Exp_pos; auto.
    - intros k Hk IH. unfold p. intros γ δ Hγ Hδ Hmono.
      destruct Hγ as [Hγf [Hγd Hγr]]. destruct Hδ as [Hδf [Hδd Hδr]].
      assert (Ok: Ordinal_Number k). { eapply (trans_Ord_Num ω); eauto. apply MKT138. }
      assert (HPk: PlusOne k ∈ ω). { apply MKT134; auto. }
      assert (OPk: Ordinal_Number (PlusOne k)). { eapply (trans_Ord_Num ω); eauto. apply MKT138. }
      assert (Hdω: dom(γ) ∈ ω). { rewrite Hγd. apply MKT134; auto. }
      assert (HδR: ran(δ) ⊂ R). { apply (ransub_R δ α); auto. }
      assert (HΦd: Φ ∈ dom(γ)). { rewrite Hγd. apply Phi_in_PlusOne; auto. }
      assert (HPΦd: PlusOne Φ ∈ dom(γ)).
        { rewrite Hγd. apply (proj1 (R_Add_2' Φ (PlusOne k) Φ_is_Ord OPk)). apply Phi_in_PlusOne; auto. }
      assert (Hγ0: Ordinal_Number (γ[Φ])). { apply Hγr, Property_dm; auto. }
      assert (HγP0: Ordinal_Number (γ[PlusOne Φ])). { apply Hγr, Property_dm; auto. }
      assert (Hδ0: δ[Φ] ≺ α). { apply Hδr, Property_dm; auto. rewrite Hδd; auto. }
      assert (Hδ0O: Ordinal_Number (δ[Φ])). { eapply (trans_Ord_Num α); eauto. }
      assert (Hdec: γ[PlusOne Φ] ≺ γ[Φ]).
        { destruct Hmono as [_ Hm]. apply (Hm Φ (PlusOne Φ)). split; auto. split; auto.
          apply MKT4; right; apply MKT41; eauto. }
      assert (Hγ'd: dom(lsh γ) = PlusOne k). { apply (lsh_dom γ (PlusOne k)); auto. }
      assert (Hδ'd: dom(lsh δ) = PlusOne k). { apply (lsh_dom δ (PlusOne k)); auto. rewrite Hδd; auto. }
      assert (Hγ'r: ran(lsh γ) ⊂ R). { apply (lsh_ranB γ (PlusOne k) R); auto. }
      assert (Hδ'rα: ran(lsh δ) ⊂ α). { apply (lsh_ranB δ (PlusOne k) α); auto. rewrite Hδd; auto. }
      assert (Hδ'R: ran(lsh δ) ⊂ R). { apply (ransub_R (lsh δ) α); auto. }
      assert (Hγ'mono: Monodc_f (lsh γ)). { apply (lsh_Monodc γ (PlusOne k)); auto. }
      assert (HOnγ': OnTo (lsh γ) (PlusOne k) R). { split; [apply lsh_fun | split; auto]. }
      assert (HOnδ': OnTo (lsh δ) (dom(lsh γ)) α). { split; [apply lsh_fun | split; [rewrite Hγ'd; auto | auto]]. }
      assert (HIH: Sum (f α (lsh γ) (lsh δ)) k ≺ α ^ (PlusOne ((lsh γ)[Φ]))). { apply IH; auto. }
      assert (Hγ'0: (lsh γ)[Φ] = γ[PlusOne Φ]). { apply lsh_value; auto. }
      rewrite Hγ'0 in HIH.
      assert (HtailB: Sum (f α (lsh γ) (lsh δ)) k ≺ α ^ (γ[Φ])).
        { eapply Ord_Num_trans''; [eapply R_Exp_in_R; eauto | exact HIH | ].
          apply Exp_R_LeOrder; auto; [apply Lem123; auto | apply R_Add_1; auto]. }
      pose proof (CNF_3 α γ δ H H0 Hγf Hγr Hδf Hδd HδR) as [Hff [Hfd Hfr]].
      assert (Hδγ'd: dom(lsh δ) = dom(lsh γ)). { rewrite Hδ'd, Hγ'd; auto. }
      assert (Hγ'dω: dom(lsh γ) ∈ ω). { rewrite Hγ'd; auto. }
      pose proof (CNF_3 α (lsh γ) (lsh δ) H H0 (lsh_fun γ) Hγ'r (lsh_fun δ) Hδγ'd Hδ'R) as [Hgf [Hgd Hgr]].
      assert (Hfdω: dom(f α γ δ) ∈ ω). { rewrite Hfd; auto. }
      assert (Hgdω: dom(f α (lsh γ) (lsh δ)) ∈ ω). { rewrite Hgd, Hγ'd; auto. }
      assert (Hkg: k ∈ dom(f α (lsh γ) (lsh δ))). { rewrite Hgd, Hγ'd. apply MKT4; right; apply MKT41; eauto. }
      assert (HPkf: PlusOne k ∈ dom(f α γ δ)). { rewrite Hfd, Hγd. apply MKT4; right; apply MKT41; eauto. }
      assert (Hmatch: ∀ m, m ∈ k \/ m = k -> (f α (lsh γ) (lsh δ))[m] = (f α γ δ)[PlusOne m]).
        { intros m Hm.
          assert (Hmpk: m ∈ PlusOne k). { apply MKT4. destruct Hm; [left; auto | right; apply MKT41; eauto]. }
          assert (Om: Ordinal_Number m). { eapply (trans_Ord_Num (PlusOne k)); eauto. }
          assert (Hpmd: PlusOne m ∈ dom(γ)).
            { rewrite Hγd. apply (proj1 (R_Add_2' m (PlusOne k) Om OPk)); auto. }
          assert (Hpmδ: PlusOne m ∈ dom(δ)). { rewrite Hδd; auto. }
          assert (Hmd': m ∈ dom(lsh γ)). { rewrite Hγ'd; auto. }
          rewrite (com_f_value α (lsh γ) (lsh δ) H H0 (lsh_fun γ) Hγ'dω Hγ'r (lsh_fun δ) Hδγ'd Hδ'R m Hmd').
          rewrite (com_f_value α γ δ H H0 Hγf Hdω Hγr Hδf Hδd HδR (PlusOne m) Hpmd).
          rewrite (lsh_value γ m Hpmd). rewrite (lsh_value δ m Hpmδ). auto. }
      rewrite (Sum_Lemma4 (f α γ δ) (f α (lsh γ) (lsh δ)) k Hff Hfdω Hfr Hgf Hgdω Hgr Hkg HPkf Hmatch).
      rewrite (com_f_value α γ δ H H0 Hγf Hdω Hγr Hδf Hδd HδR Φ HΦd).
      rewrite (Exp_R_Suc α (γ[Φ]) H Hγ0).
      apply Mult_Union'; try (eapply R_Exp_in_R; eauto); auto. }
  intros. apply Hmain; auto.
Qed.

(* ≼ 的传递性 *)
Lemma Le_trans : ∀ a b c, Ordinal_Number c -> a ≼ b -> b ≼ c -> a ≼ c.
Proof.
  intros a b c Hc H1 H2. destruct H1 as [H1|H1], H2 as [H2|H2].
  - left. eapply Ord_Num_trans; eauto.
  - subst c. left; auto.
  - subst b. left; auto.
  - subst. right; auto.
Qed.

(* 首指数被唯一确定: γ[Φ] = MaxinExp α β *)
Lemma CNF_leadexp : ∀ α β n γ δ, Ordinal_Number α -> PlusOne Φ ≺ α -> n ∈ ω
  -> OnTo γ (PlusOne n) R -> OnTo δ (dom(γ)) α -> Monodc_f γ -> (∀ k, δ[k] ≠ Φ)
  -> β = Sum (f α γ δ) n -> MaxinExp α β = γ[Φ].
Proof.
  intros α β n γ δ H H0 H1 HOnγ HOnδ Hmono Hnz Hβ.
  destruct HOnγ as [Hγf [Hγd Hγr]]. destruct HOnδ as [Hδf [Hδd Hδr]].
  assert (On: Ordinal_Number n). { eapply (trans_Ord_Num ω); eauto. apply MKT138. }
  assert (Hdω: dom(γ) ∈ ω). { rewrite Hγd. apply MKT134; auto. }
  assert (HδR: ran(δ) ⊂ R). { apply (ransub_R δ α); auto. }
  assert (HΦd: Φ ∈ dom(γ)). { rewrite Hγd. apply Phi_in_PlusOne; auto. }
  assert (Hγ0: Ordinal_Number (γ[Φ])). { apply Hγr, Property_dm; auto. }
  assert (Hδ0: δ[Φ] ≺ α). { apply Hδr, Property_dm; auto. rewrite Hδd; auto. }
  assert (Hδ0O: Ordinal_Number (δ[Φ])). { eapply (trans_Ord_Num α); eauto. }
  assert (Hnz0: δ[Φ] ≠ Φ). { apply Hnz. }
  assert (HOe: Ordinal_Number (α^γ[Φ])). { eapply R_Exp_in_R; eauto. }
  assert (HOnγ: OnTo γ (PlusOne n) R). { split; [auto | split; auto]. }
  assert (HOnδ: OnTo δ (dom(γ)) α). { split; [auto | split; auto]. }
  pose proof (CNF_3 α γ δ H H0 Hγf Hγr Hδf Hδd HδR) as [Hff [Hfd Hfr]].
  assert (Hfdω: dom(f α γ δ) ∈ ω). { rewrite Hfd; auto. }
  assert (Hndf: n ∈ dom(f α γ δ)). { rewrite Hfd, Hγd. apply MKT4; right; apply MKT41; eauto. }
  assert (HβR: Ordinal_Number β). { rewrite Hβ. apply Sum_Lemma3; auto. }
  apply (MaxinExp_unique α β (γ[Φ])); auto.
  - apply (Le_trans (α^γ[Φ]) (α^γ[Φ]⋅δ[Φ]) β); auto.
    + apply R_Mult_1; auto.
    + rewrite Hβ. apply Sum_Monodc; auto. rewrite <- Hβ; auto.
  - rewrite Hβ. apply CNF_upper; auto.
Qed.

(* 除法/余项唯一性: a⋅c1+r1 = a⋅c2+r2 且 r1,r2 ≺ a ⇒ c1=c2 且 r1=r2 *)
Lemma div_unique : ∀ a c1 c2 r1 r2, Ordinal_Number a -> Ordinal_Number c1
  -> Ordinal_Number c2 -> Ordinal_Number r1 -> Ordinal_Number r2
  -> r1 ≺ a -> r2 ≺ a -> a ⋅ c1 + r1 = a ⋅ c2 + r2 -> c1 = c2 /\ r1 = r2.
Proof.
  intros a c1 c2 r1 r2 Ha Hc1 Hc2 Hr1 Hr2 Hr1a Hr2a Heq.
  assert (Hc: c1 = c2).
  { New (Ord_Num_tri c1 c2 Hc1 Hc2). destruct H as [Hlt|[He|Hlt]]; auto.
    - exfalso.
      assert (T1: a ⋅ c1 + r1 ≺ a ⋅ c2). { apply Mult_Union'; auto. }
      assert (T2: a ⋅ c2 ≼ a ⋅ c2 + r2). { apply R_Add_3'; [eapply R_Mult_in_R; eauto | auto]. }
      rewrite Heq in T1.
      assert (a ⋅ c2 ≺ a ⋅ c2). { eapply Ord_Num_trans'; eauto. eapply R_Mult_in_R; eauto. }
      eapply MKT101; eauto.
    - exfalso.
      assert (T1: a ⋅ c2 + r2 ≺ a ⋅ c1). { apply Mult_Union'; auto. }
      assert (T2: a ⋅ c1 ≼ a ⋅ c1 + r1). { apply R_Add_3'; [eapply R_Mult_in_R; eauto | auto]. }
      rewrite <- Heq in T1.
      assert (a ⋅ c1 ≺ a ⋅ c1). { eapply Ord_Num_trans'; eauto. eapply R_Mult_in_R; eauto. }
      eapply MKT101; eauto. }
  split; auto. subst c2.
  apply (proj1 (Add_R_Cancellation r1 r2 (a⋅c1) Hr1 Hr2 (R_Mult_in_R _ _ Ha Hc1))); auto.
Qed.

(* 剥离首项: β = α^γ[Φ]·δ[Φ] + (左移尾部和), 且尾部 ≺ α^γ[Φ] *)
Lemma CNF_peel : ∀ α k γ δ, Ordinal_Number α -> PlusOne Φ ≺ α -> k ∈ ω
  -> OnTo γ (PlusOne (PlusOne k)) R -> OnTo δ (dom(γ)) α -> Monodc_f γ
  -> Sum (f α γ δ) (PlusOne k) = α ^ γ[Φ] ⋅ δ[Φ] + Sum (f α (lsh γ) (lsh δ)) k
     /\ Sum (f α (lsh γ) (lsh δ)) k ≺ α ^ γ[Φ].
Proof.
  intros α k γ δ H H0 Hk HOnγ HOnδ Hmono.
  destruct HOnγ as [Hγf [Hγd Hγr]]. destruct HOnδ as [Hδf [Hδd Hδr]].
  assert (Ok: Ordinal_Number k). { eapply (trans_Ord_Num ω); eauto. apply MKT138. }
  assert (HPk: PlusOne k ∈ ω). { apply MKT134; auto. }
  assert (OPk: Ordinal_Number (PlusOne k)). { eapply (trans_Ord_Num ω); eauto. apply MKT138. }
  assert (Hdω: dom(γ) ∈ ω). { rewrite Hγd. apply MKT134; auto. }
  assert (HδR: ran(δ) ⊂ R). { apply (ransub_R δ α); auto. }
  assert (HΦd: Φ ∈ dom(γ)). { rewrite Hγd. apply Phi_in_PlusOne; auto. }
  assert (HPΦd: PlusOne Φ ∈ dom(γ)).
    { rewrite Hγd. apply (proj1 (R_Add_2' Φ (PlusOne k) Φ_is_Ord OPk)). apply Phi_in_PlusOne; auto. }
  assert (Hγ0: Ordinal_Number (γ[Φ])). { apply Hγr, Property_dm; auto. }
  assert (HγP0: Ordinal_Number (γ[PlusOne Φ])). { apply Hγr, Property_dm; auto. }
  assert (Hδ0: δ[Φ] ≺ α). { apply Hδr, Property_dm; auto. rewrite Hδd; auto. }
  assert (Hδ0O: Ordinal_Number (δ[Φ])). { eapply (trans_Ord_Num α); eauto. }
  assert (Hdec: γ[PlusOne Φ] ≺ γ[Φ]).
    { destruct Hmono as [_ Hm]. apply (Hm Φ (PlusOne Φ)). split; auto. split; auto.
      apply MKT4; right; apply MKT41; eauto. }
  assert (Hγ'd: dom(lsh γ) = PlusOne k). { apply (lsh_dom γ (PlusOne k)); auto. }
  assert (Hδ'd: dom(lsh δ) = PlusOne k). { apply (lsh_dom δ (PlusOne k)); auto. rewrite Hδd; auto. }
  assert (Hγ'r: ran(lsh γ) ⊂ R). { apply (lsh_ranB γ (PlusOne k) R); auto. }
  assert (Hδ'rα: ran(lsh δ) ⊂ α). { apply (lsh_ranB δ (PlusOne k) α); auto. rewrite Hδd; auto. }
  assert (Hδ'R: ran(lsh δ) ⊂ R). { apply (ransub_R (lsh δ) α); auto. }
  assert (Hγ'mono: Monodc_f (lsh γ)). { apply (lsh_Monodc γ (PlusOne k)); auto. }
  assert (HOnγ': OnTo (lsh γ) (PlusOne k) R). { split; [apply lsh_fun | split; auto]. }
  assert (HOnδ': OnTo (lsh δ) (dom(lsh γ)) α). { split; [apply lsh_fun | split; [rewrite Hγ'd; auto | auto]]. }
  assert (HIH: Sum (f α (lsh γ) (lsh δ)) k ≺ α ^ (PlusOne ((lsh γ)[Φ]))).
    { apply (CNF_upper α H H0 k Hk (lsh γ) (lsh δ)); auto. }
  assert (Hγ'0: (lsh γ)[Φ] = γ[PlusOne Φ]). { apply lsh_value; auto. }
  rewrite Hγ'0 in HIH.
  assert (HtailB: Sum (f α (lsh γ) (lsh δ)) k ≺ α ^ (γ[Φ])).
    { eapply Ord_Num_trans''; [eapply R_Exp_in_R; eauto | exact HIH | ].
      apply Exp_R_LeOrder; auto; [apply Lem123; auto | apply R_Add_1; auto]. }
  pose proof (CNF_3 α γ δ H H0 Hγf Hγr Hδf Hδd HδR) as [Hff [Hfd Hfr]].
  assert (Hδγ'd: dom(lsh δ) = dom(lsh γ)). { rewrite Hδ'd, Hγ'd; auto. }
  assert (Hγ'dω: dom(lsh γ) ∈ ω). { rewrite Hγ'd; auto. }
  pose proof (CNF_3 α (lsh γ) (lsh δ) H H0 (lsh_fun γ) Hγ'r (lsh_fun δ) Hδγ'd Hδ'R) as [Hgf [Hgd Hgr]].
  assert (Hfdω: dom(f α γ δ) ∈ ω). { rewrite Hfd; auto. }
  assert (Hgdω: dom(f α (lsh γ) (lsh δ)) ∈ ω). { rewrite Hgd, Hγ'd; auto. }
  assert (Hkg: k ∈ dom(f α (lsh γ) (lsh δ))). { rewrite Hgd, Hγ'd. apply MKT4; right; apply MKT41; eauto. }
  assert (HPkf: PlusOne k ∈ dom(f α γ δ)). { rewrite Hfd, Hγd. apply MKT4; right; apply MKT41; eauto. }
  assert (Hmatch: ∀ m, m ∈ k \/ m = k -> (f α (lsh γ) (lsh δ))[m] = (f α γ δ)[PlusOne m]).
    { intros m Hm.
      assert (Hmpk: m ∈ PlusOne k). { apply MKT4. destruct Hm; [left; auto | right; apply MKT41; eauto]. }
      assert (Om: Ordinal_Number m). { eapply (trans_Ord_Num (PlusOne k)); eauto. }
      assert (Hpmd: PlusOne m ∈ dom(γ)).
        { rewrite Hγd. apply (proj1 (R_Add_2' m (PlusOne k) Om OPk)); auto. }
      assert (Hpmδ: PlusOne m ∈ dom(δ)). { rewrite Hδd; auto. }
      assert (Hmd': m ∈ dom(lsh γ)). { rewrite Hγ'd; auto. }
      rewrite (com_f_value α (lsh γ) (lsh δ) H H0 (lsh_fun γ) Hγ'dω Hγ'r (lsh_fun δ) Hδγ'd Hδ'R m Hmd').
      rewrite (com_f_value α γ δ H H0 Hγf Hdω Hγr Hδf Hδd HδR (PlusOne m) Hpmd).
      rewrite (lsh_value γ m Hpmd). rewrite (lsh_value δ m Hpmδ). auto. }
  split.
  - rewrite (Sum_Lemma4 (f α γ δ) (f α (lsh γ) (lsh δ)) k Hff Hfdω Hfr Hgf Hgdω Hgr Hkg HPkf Hmatch).
    rewrite (com_f_value α γ δ H H0 Hγf Hdω Hγr Hδf Hδd HδR Φ HΦd). auto.
  - exact HtailB.
Qed.

(* 左移保持系数非零 *)
Lemma lsh_nz : ∀ δ, (∀ j, δ[j] ≠ Φ) -> ∀ j, (lsh δ)[j] ≠ Φ.
Proof.
  intros δ Hnz j. TF (j ∈ dom(lsh δ)).
  - appA2H H. rdeHex. New H0. appoA2H H0. deand. subst x.
    apply Property_Fun in H1; [| apply lsh_fun]. rewrite <- H1. apply Hnz.
  - apply MKT69a in H. rewrite H. intro He. New EnEm. rewrite <- He in H0.
    New MKT39. contradiction.
Qed.

(* 非零系数的 CNF 和为正 (≠ Φ) *)
Lemma Sum_pos : ∀ α n γ δ, Ordinal_Number α -> PlusOne Φ ≺ α -> n ∈ ω
  -> OnTo γ (PlusOne n) R -> OnTo δ (dom(γ)) α -> (∀ k, δ[k] ≠ Φ)
  -> Sum (f α γ δ) n ≠ Φ.
Proof.
  intros α n γ δ H H0 Hn HOnγ HOnδ Hnz.
  destruct HOnγ as [Hγf [Hγd Hγr]]. destruct HOnδ as [Hδf [Hδd Hδr]].
  assert (HδR: ran(δ) ⊂ R). { apply (ransub_R δ α); auto. }
  assert (Hdω: dom(γ) ∈ ω). { rewrite Hγd. apply MKT134; auto. }
  assert (HΦd: Φ ∈ dom(γ)).
    { rewrite Hγd. apply Phi_in_PlusOne. eapply (trans_Ord_Num ω); eauto. apply MKT138. }
  assert (Hγ0: Ordinal_Number (γ[Φ])). { apply Hγr, Property_dm; auto. }
  assert (Hδ0: δ[Φ] ≺ α). { apply Hδr, Property_dm; auto. rewrite Hδd; auto. }
  assert (Hδ0O: Ordinal_Number (δ[Φ])). { eapply (trans_Ord_Num α); eauto. }
  assert (HOe: Ordinal_Number (α^γ[Φ])). { eapply R_Exp_in_R; eauto. }
  assert (HOnγ: OnTo γ (PlusOne n) R). { split; [auto | split; auto]. }
  assert (HOnδ: OnTo δ (dom(γ)) α). { split; [auto | split; auto]. }
  pose proof (CNF_3 α γ δ H H0 Hγf Hγr Hδf Hδd HδR) as [Hff [Hfd Hfr]].
  assert (Hfdω: dom(f α γ δ) ∈ ω). { rewrite Hfd; auto. }
  assert (Hndf: n ∈ dom(f α γ δ)). { rewrite Hfd, Hγd. apply MKT4; right; apply MKT41; eauto. }
  assert (HsumR: Sum (f α γ δ) n ∈ R). { apply Sum_Lemma3; auto. }
  assert (Hprodpos: Φ ≺ α^γ[Φ] ⋅ δ[Φ]).
  { assert (Hd1: Φ ≺ δ[Φ]). { apply Φ_is_First_Ord; auto. }
    assert (Hd2: δ[Φ] ≼ α^γ[Φ]⋅δ[Φ]). { apply R_Mult_2; auto. apply Exp_pos; auto. }
    eapply Ord_Num_trans''; [ eapply R_Mult_in_R; eauto | exact Hd1 | exact Hd2 ]. }
  assert (Hle: α^γ[Φ]⋅δ[Φ] ≼ Sum (f α γ δ) n). { apply Sum_Monodc; auto. }
  intro He. rewrite He in Hle.
  assert (Φ ≺ Φ). { eapply Ord_Num_trans''; [apply Φ_is_Ord | exact Hprodpos | exact Hle]. }
  eapply MKT101; eauto.
Qed.

(* 由首值与左移序列重建原序列 (unshift): γ 由 γ[Φ] 与 lsh γ 唯一确定 *)
Lemma unshift_eq : ∀ m γ1 γ2, m ∈ ω -> Function γ1 -> Function γ2
  -> dom(γ1) = PlusOne m -> dom(γ2) = PlusOne m
  -> γ1[Φ] = γ2[Φ] -> lsh γ1 = lsh γ2 -> γ1 = γ2.
Proof.
  intros m γ1 γ2 Hm Hf1 Hf2 Hd1 Hd2 HΦ Hlsh.
  apply (proj2 (MKT71 γ1 γ2 Hf1 Hf2)). intro x.
  TF (x ∈ PlusOne m).
  - TF (x = Φ).
    + subst; auto.
    + assert (Hxω: x ∈ ω).
        { eapply Ord_Num_trans; [apply MKT138 | exact H | apply MKT134; auto]. }
      New (ω_Num_is_Suc_Ord x Hxω H0). destruct H1 as [y [Hy Hxy]].
      assert (Hux: ∪x = y). { rewrite Hxy. apply MKT124; auto. }
      assert (Hx': x = PlusOne (∪x)). { rewrite Hux; auto. }
      assert (HPux1: PlusOne (∪x) ∈ dom(γ1)). { rewrite Hd1, <- Hx'; auto. }
      assert (HPux2: PlusOne (∪x) ∈ dom(γ2)). { rewrite Hd2, <- Hx'; auto. }
      assert (E1: (lsh γ1)[∪x] = γ1[x]). { rewrite (lsh_value γ1 (∪x) HPux1). rewrite <- Hx'; auto. }
      assert (E2: (lsh γ2)[∪x] = γ2[x]). { rewrite (lsh_value γ2 (∪x) HPux2). rewrite <- Hx'; auto. }
      rewrite <- E1, <- E2, Hlsh. auto.
  - assert (Hn1: x ∉ dom(γ1)). { rewrite Hd1; auto. }
    assert (Hn2: x ∉ dom(γ2)). { rewrite Hd2; auto. }
    apply MKT69a in Hn1, Hn2. rewrite Hn1, Hn2. auto.
Qed.

(* 空左移: dom = PlusOne Φ 时 lsh 为空函数, 任意两者相等 *)
Lemma lsh_emp_eq : ∀ γ1 γ2, dom(γ1) = PlusOne Φ -> dom(γ2) = PlusOne Φ -> lsh γ1 = lsh γ2.
Proof.
  intros. apply (proj2 (MKT71 _ _ (lsh_fun γ1) (lsh_fun γ2))). intro x.
  assert (Hd1: dom(lsh γ1) = Φ). { apply (lsh_dom γ1 Φ); auto. }
  assert (Hd2: dom(lsh γ2) = Φ). { apply (lsh_dom γ2 Φ); auto. }
  assert (x ∉ dom(lsh γ1)). { rewrite Hd1. intro He. emf. }
  assert (x ∉ dom(lsh γ2)). { rewrite Hd2. intro He. emf. }
  apply MKT69a in H1, H2. rewrite H1, H2. auto.
Qed.

(* ================================================================= *)
(*                Cantor 范式唯一性 (主定理)                          *)
(*   同一 β 的两个 CNF 表示 (项数 n、指数序列 γ、系数序列 δ) 必相等。   *)
(* ================================================================= *)

Theorem CNF_unique : ∀ α β n1 γ1 δ1 n2 γ2 δ2, Ordinal_Number α -> PlusOne Φ ≺ α
  -> (n1 ∈ ω /\ OnTo γ1 (PlusOne n1) R /\ Monodc_f γ1 /\ OnTo δ1 (dom(γ1)) α /\ (∀ k, δ1[k] ≠ Φ) /\ β = Sum (f α γ1 δ1) n1)
  -> (n2 ∈ ω /\ OnTo γ2 (PlusOne n2) R /\ Monodc_f γ2 /\ OnTo δ2 (dom(γ2)) α /\ (∀ k, δ2[k] ≠ Φ) /\ β = Sum (f α γ2 δ2) n2)
  -> n1 = n2 /\ γ1 = γ2 /\ δ1 = δ2.
Proof.
  intros α.
  set (P := fun n1 => ∀ β n2 γ1 δ1 γ2 δ2, Ordinal_Number α -> PlusOne Φ ≺ α
    -> (OnTo γ1 (PlusOne n1) R /\ Monodc_f γ1 /\ OnTo δ1 (dom(γ1)) α /\ (∀ k, δ1[k] ≠ Φ) /\ β = Sum (f α γ1 δ1) n1)
    -> (n2 ∈ ω /\ OnTo γ2 (PlusOne n2) R /\ Monodc_f γ2 /\ OnTo δ2 (dom(γ2)) α /\ (∀ k, δ2[k] ≠ Φ) /\ β = Sum (f α γ2 δ2) n2)
    -> n1 = n2 /\ γ1 = γ2 /\ δ1 = δ2).
  assert (Hmain: ∀ n1, n1 ∈ ω -> P n1).
  { apply Mathematical_Induction.
    - unfold P. intros β n2 γ1 δ1 γ2 δ2 HOα Hα R1 R2.
      destruct R1 as [HOnγ1 [Hmono1 [HOnδ1 [Hnz1 Hβ1]]]].
      destruct R2 as [Hn2 [HOnγ2 [Hmono2 [HOnδ2 [Hnz2 Hβ2]]]]].
      assert (He1: MaxinExp α β = γ1[Φ]). { apply (CNF_leadexp α β Φ γ1 δ1); auto using MKT135a. }
      assert (He2: MaxinExp α β = γ2[Φ]). { apply (CNF_leadexp α β n2 γ2 δ2); auto. }
      assert (Hee: γ1[Φ] = γ2[Φ]). { rewrite <- He1, <- He2; auto. }
      destruct HOnγ1 as [Hγ1f [Hγ1d Hγ1r]]. destruct HOnδ1 as [Hδ1f [Hδ1d Hδ1r]].
      destruct HOnγ2 as [Hγ2f [Hγ2d Hγ2r]]. destruct HOnδ2 as [Hδ2f [Hδ2d Hδ2r]].
      assert (HδR1: ran(δ1) ⊂ R). { apply (ransub_R δ1 α); auto. }
      assert (HδR2: ran(δ2) ⊂ R). { apply (ransub_R δ2 α); auto. }
      assert (HΦd1: Φ ∈ dom(γ1)). { rewrite Hγ1d. apply Phi_in_PlusOne, Φ_is_Ord. }
      assert (Hγ10: Ordinal_Number (γ1[Φ])). { apply Hγ1r, Property_dm; auto. }
      assert (Hδ10: Ordinal_Number (δ1[Φ])).
        { eapply (trans_Ord_Num α); eauto. apply Hδ1r, Property_dm; auto. rewrite Hδ1d; auto. }
      assert (HOe: Ordinal_Number (α^γ1[Φ])). { eapply R_Exp_in_R; eauto. }
      assert (HOe0: Φ ≺ α^γ1[Φ]). { apply Φ_is_First_Ord; auto. apply Exp_pos; auto. }
      assert (Hd1ω: dom(γ1) ∈ ω). { rewrite Hγ1d. apply MKT134, MKT135a. }
      pose proof (CNF_3 α γ1 δ1 HOα Hα Hγ1f Hγ1r Hδ1f Hδ1d HδR1) as [Hff1 [Hfd1 Hfr1]].
      assert (Hf1dω: dom(f α γ1 δ1) ∈ ω). { rewrite Hfd1; auto. }
      assert (Hβ1': β = α^γ1[Φ] ⋅ δ1[Φ] + Φ).
      { rewrite Hβ1, Sum_Lemma2; auto.
        rewrite (com_f_value α γ1 δ1 HOα Hα Hγ1f Hd1ω Hγ1r Hδ1f Hδ1d HδR1 Φ HΦd1).
        rewrite Add_R_Φ_r; auto. eapply R_Mult_in_R; eauto. }
      TF (n2 = Φ).
      + subst n2.
        assert (HΦd2: Φ ∈ dom(γ2)). { rewrite Hγ2d. apply Phi_in_PlusOne, Φ_is_Ord. }
        assert (Hγ20: Ordinal_Number (γ2[Φ])). { apply Hγ2r, Property_dm; auto. }
        assert (HOe2: Ordinal_Number (α^γ2[Φ])). { eapply R_Exp_in_R; eauto. }
        assert (Hδ20: Ordinal_Number (δ2[Φ])).
          { eapply (trans_Ord_Num α); eauto. apply Hδ2r, Property_dm; auto. rewrite Hδ2d; auto. }
        assert (Hd2ω: dom(γ2) ∈ ω). { rewrite Hγ2d. apply MKT134, MKT135a. }
        pose proof (CNF_3 α γ2 δ2 HOα Hα Hγ2f Hγ2r Hδ2f Hδ2d HδR2) as [Hff2 [Hfd2 Hfr2]].
        assert (Hf2dω: dom(f α γ2 δ2) ∈ ω). { rewrite Hfd2; auto. }
        assert (Hβ2': β = α^γ2[Φ] ⋅ δ2[Φ] + Φ).
        { rewrite Hβ2, Sum_Lemma2; auto.
          rewrite (com_f_value α γ2 δ2 HOα Hα Hγ2f Hd2ω Hγ2r Hδ2f Hδ2d HδR2 Φ HΦd2).
          rewrite Add_R_Φ_r; auto. eapply R_Mult_in_R; eauto. }
        assert (Heqd: α^γ1[Φ] ⋅ δ1[Φ] + Φ = α^γ1[Φ] ⋅ δ2[Φ] + Φ).
        { rewrite <- Hβ1', Hβ2', Hee; auto. }
        pose proof (div_unique (α^γ1[Φ]) (δ1[Φ]) (δ2[Φ]) Φ Φ HOe Hδ10 Hδ20 Φ_is_Ord Φ_is_Ord HOe0 HOe0 Heqd) as [Hδeq _].
        assert (Hδ1d': dom(δ1) = PlusOne Φ). { rewrite Hδ1d; auto. }
        assert (Hδ2d': dom(δ2) = PlusOne Φ). { rewrite Hδ2d; auto. }
        assert (Hlshγ: lsh γ1 = lsh γ2). { apply lsh_emp_eq; auto. }
        assert (Hlshδ: lsh δ1 = lsh δ2). { apply lsh_emp_eq; auto. }
        split; [auto | split;
          [ apply (unshift_eq Φ γ1 γ2); auto using MKT135a
          | apply (unshift_eq Φ δ1 δ2); auto using MKT135a ]].
      + New (ω_Num_is_Suc_Ord n2 Hn2 H). destruct H0 as [k2 [Hk2O Hn2eq]]. subst n2.
        assert (Hk2: k2 ∈ ω).
          { eapply Ord_Num_trans; [apply MKT138 | | exact Hn2]. apply MKT4; right; apply MKT41; eauto. }
        assert (HΦd2: Φ ∈ dom(γ2)). { rewrite Hγ2d. apply Phi_in_PlusOne. apply Lem123; auto. }
        assert (Hγ20: Ordinal_Number (γ2[Φ])). { apply Hγ2r, Property_dm; auto. }
        assert (HOe2: Ordinal_Number (α^γ2[Φ])). { eapply R_Exp_in_R; eauto. }
        assert (Hδ20: Ordinal_Number (δ2[Φ])).
          { eapply (trans_Ord_Num α); eauto. apply Hδ2r, Property_dm; auto. rewrite Hδ2d; auto. }
        assert (HOnγ2: OnTo γ2 (PlusOne (PlusOne k2)) R). { split; [auto | split; auto]. }
        assert (HOnδ2: OnTo δ2 (dom(γ2)) α). { split; [auto | split; auto]. }
        pose proof (CNF_peel α k2 γ2 δ2 HOα Hα Hk2 HOnγ2 HOnδ2 Hmono2) as [Hpeel Htail].
        assert (Hβ2': β = α^γ2[Φ] ⋅ δ2[Φ] + Sum (f α (lsh γ2) (lsh δ2)) k2). { rewrite Hβ2. exact Hpeel. }
        assert (HT2O: Ordinal_Number (Sum (f α (lsh γ2) (lsh δ2)) k2)). { eapply (trans_Ord_Num (α^γ2[Φ])); eauto. }
        assert (HtailT2: Sum (f α (lsh γ2) (lsh δ2)) k2 ≺ α^γ1[Φ]). { rewrite Hee. exact Htail. }
        assert (Heqd: α^γ1[Φ] ⋅ δ1[Φ] + Φ = α^γ1[Φ] ⋅ δ2[Φ] + Sum (f α (lsh γ2) (lsh δ2)) k2).
        { rewrite <- Hβ1', Hβ2', Hee; auto. }
        pose proof (div_unique (α^γ1[Φ]) (δ1[Φ]) (δ2[Φ]) Φ (Sum (f α (lsh γ2) (lsh δ2)) k2)
                    HOe Hδ10 Hδ20 Φ_is_Ord HT2O HOe0 HtailT2 Heqd) as [_ HΦT2].
        assert (Hδ2dd: dom(δ2) = PlusOne (PlusOne k2)). { rewrite Hδ2d; auto. }
        assert (Hγ2'd: dom(lsh γ2) = PlusOne k2). { apply (lsh_dom γ2 (PlusOne k2)); auto. }
        assert (Hγ2'r: ran(lsh γ2) ⊂ R). { apply (lsh_ranB γ2 (PlusOne k2) R); auto. }
        assert (Hδ2'rα: ran(lsh δ2) ⊂ α). { apply (lsh_ranB δ2 (PlusOne k2) α); auto. }
        assert (HOnγ2': OnTo (lsh γ2) (PlusOne k2) R). { split; [apply lsh_fun | split; auto]. }
        assert (HOnδ2': OnTo (lsh δ2) (dom(lsh γ2)) α).
          { split; [apply lsh_fun | split; [rewrite Hγ2'd; auto | auto]]. apply (lsh_dom δ2 (PlusOne k2)); auto. }
        exfalso. apply (Sum_pos α k2 (lsh γ2) (lsh δ2) HOα Hα Hk2 HOnγ2' HOnδ2' (lsh_nz δ2 Hnz2)).
        symmetry. exact HΦT2.
    - intros k1 Hk1 IH. unfold P. intros β n2 γ1 δ1 γ2 δ2 HOα Hα R1 R2.
      destruct R1 as [HOnγ1 [Hmono1 [HOnδ1 [Hnz1 Hβ1]]]].
      destruct R2 as [Hn2 [HOnγ2 [Hmono2 [HOnδ2 [Hnz2 Hβ2]]]]].
      assert (Ok1: Ordinal_Number k1). { eapply (trans_Ord_Num ω); eauto. apply MKT138. }
      assert (OPk1: Ordinal_Number (PlusOne k1)). { apply Lem123; auto. }
      assert (Hn1: PlusOne k1 ∈ ω). { apply MKT134; auto. }
      assert (He1: MaxinExp α β = γ1[Φ]). { apply (CNF_leadexp α β (PlusOne k1) γ1 δ1); auto. }
      assert (He2: MaxinExp α β = γ2[Φ]). { apply (CNF_leadexp α β n2 γ2 δ2); auto. }
      assert (Hee: γ1[Φ] = γ2[Φ]). { rewrite <- He1, <- He2; auto. }
      destruct HOnγ1 as [Hγ1f [Hγ1d Hγ1r]]. destruct HOnδ1 as [Hδ1f [Hδ1d Hδ1r]].
      destruct HOnγ2 as [Hγ2f [Hγ2d Hγ2r]]. destruct HOnδ2 as [Hδ2f [Hδ2d Hδ2r]].
      assert (HδR1: ran(δ1) ⊂ R). { apply (ransub_R δ1 α); auto. }
      assert (HδR2: ran(δ2) ⊂ R). { apply (ransub_R δ2 α); auto. }
      assert (HΦd1: Φ ∈ dom(γ1)). { rewrite Hγ1d. apply Phi_in_PlusOne; auto. }
      assert (Hγ10: Ordinal_Number (γ1[Φ])). { apply Hγ1r, Property_dm; auto. }
      assert (Hδ10: Ordinal_Number (δ1[Φ])).
        { eapply (trans_Ord_Num α); eauto. apply Hδ1r, Property_dm; auto. rewrite Hδ1d; auto. }
      assert (HOe: Ordinal_Number (α^γ1[Φ])). { eapply R_Exp_in_R; eauto. }
      assert (HOe0: Φ ≺ α^γ1[Φ]). { apply Φ_is_First_Ord; auto. apply Exp_pos; auto. }
      assert (HOnγ1: OnTo γ1 (PlusOne (PlusOne k1)) R). { split; [auto | split; auto]. }
      assert (HOnδ1: OnTo δ1 (dom(γ1)) α). { split; [auto | split; auto]. }
      pose proof (CNF_peel α k1 γ1 δ1 HOα Hα Hk1 HOnγ1 HOnδ1 Hmono1) as [Hpeel1 Htail1].
      assert (Hβ1': β = α^γ1[Φ] ⋅ δ1[Φ] + Sum (f α (lsh γ1) (lsh δ1)) k1). { rewrite Hβ1. exact Hpeel1. }
      assert (HT1O: Ordinal_Number (Sum (f α (lsh γ1) (lsh δ1)) k1)). { eapply (trans_Ord_Num (α^γ1[Φ])); eauto. }
      TF (n2 = Φ).
      + subst n2. exfalso.
        assert (HΦd2: Φ ∈ dom(γ2)). { rewrite Hγ2d. apply Phi_in_PlusOne, Φ_is_Ord. }
        assert (Hγ20: Ordinal_Number (γ2[Φ])). { apply Hγ2r, Property_dm; auto. }
        assert (HOe2: Ordinal_Number (α^γ2[Φ])). { eapply R_Exp_in_R; eauto. }
        assert (Hδ20: Ordinal_Number (δ2[Φ])).
          { eapply (trans_Ord_Num α); eauto. apply Hδ2r, Property_dm; auto. rewrite Hδ2d; auto. }
        assert (Hd2ω: dom(γ2) ∈ ω). { rewrite Hγ2d. apply MKT134, MKT135a. }
        pose proof (CNF_3 α γ2 δ2 HOα Hα Hγ2f Hγ2r Hδ2f Hδ2d HδR2) as [Hff2 [Hfd2 Hfr2]].
        assert (Hf2dω: dom(f α γ2 δ2) ∈ ω). { rewrite Hfd2; auto. }
        assert (Hβ2': β = α^γ2[Φ] ⋅ δ2[Φ] + Φ).
        { rewrite Hβ2, Sum_Lemma2; auto.
          rewrite (com_f_value α γ2 δ2 HOα Hα Hγ2f Hd2ω Hγ2r Hδ2f Hδ2d HδR2 Φ HΦd2).
          rewrite Add_R_Φ_r; auto. eapply R_Mult_in_R; eauto. }
        assert (Heqd: α^γ1[Φ] ⋅ δ1[Φ] + Sum (f α (lsh γ1) (lsh δ1)) k1 = α^γ1[Φ] ⋅ δ2[Φ] + Φ).
        { rewrite <- Hβ1', Hβ2', Hee; auto. }
        pose proof (div_unique (α^γ1[Φ]) (δ1[Φ]) (δ2[Φ]) (Sum (f α (lsh γ1) (lsh δ1)) k1) Φ
                    HOe Hδ10 Hδ20 HT1O Φ_is_Ord Htail1 HOe0 Heqd) as [_ HT1Φ].
        assert (Hδ1dd: dom(δ1) = PlusOne (PlusOne k1)). { rewrite Hδ1d; auto. }
        assert (Hγ1'd: dom(lsh γ1) = PlusOne k1). { apply (lsh_dom γ1 (PlusOne k1)); auto. }
        assert (Hδ1'd: dom(lsh δ1) = PlusOne k1). { apply (lsh_dom δ1 (PlusOne k1)); auto. }
        assert (Hγ1'r: ran(lsh γ1) ⊂ R). { apply (lsh_ranB γ1 (PlusOne k1) R); auto. }
        assert (Hδ1'rα: ran(lsh δ1) ⊂ α). { apply (lsh_ranB δ1 (PlusOne k1) α); auto. }
        assert (HOnγ1': OnTo (lsh γ1) (PlusOne k1) R). { split; [apply lsh_fun | split; auto]. }
        assert (HOnδ1': OnTo (lsh δ1) (dom(lsh γ1)) α). { split; [apply lsh_fun | split; [rewrite Hδ1'd, Hγ1'd; auto | auto]]. }
        apply (Sum_pos α k1 (lsh γ1) (lsh δ1) HOα Hα Hk1 HOnγ1' HOnδ1' (lsh_nz δ1 Hnz1)). exact HT1Φ.
      + New (ω_Num_is_Suc_Ord n2 Hn2 H). destruct H0 as [k2 [Hk2O Hn2eq]]. subst n2.
        assert (Hk2: k2 ∈ ω).
          { eapply Ord_Num_trans; [apply MKT138 | | exact Hn2]. apply MKT4; right; apply MKT41; eauto. }
        assert (HΦd2: Φ ∈ dom(γ2)). { rewrite Hγ2d. apply Phi_in_PlusOne. apply Lem123; auto. }
        assert (Hγ20: Ordinal_Number (γ2[Φ])). { apply Hγ2r, Property_dm; auto. }
        assert (HOe2: Ordinal_Number (α^γ2[Φ])). { eapply R_Exp_in_R; eauto. }
        assert (Hδ20: Ordinal_Number (δ2[Φ])).
          { eapply (trans_Ord_Num α); eauto. apply Hδ2r, Property_dm; auto. rewrite Hδ2d; auto. }
        assert (HOnγ2: OnTo γ2 (PlusOne (PlusOne k2)) R). { split; [auto | split; auto]. }
        assert (HOnδ2: OnTo δ2 (dom(γ2)) α). { split; [auto | split; auto]. }
        pose proof (CNF_peel α k2 γ2 δ2 HOα Hα Hk2 HOnγ2 HOnδ2 Hmono2) as [Hpeel2 Htail2].
        assert (Hβ2': β = α^γ2[Φ] ⋅ δ2[Φ] + Sum (f α (lsh γ2) (lsh δ2)) k2). { rewrite Hβ2. exact Hpeel2. }
        assert (HT2O: Ordinal_Number (Sum (f α (lsh γ2) (lsh δ2)) k2)). { eapply (trans_Ord_Num (α^γ2[Φ])); eauto. }
        assert (HtailT2: Sum (f α (lsh γ2) (lsh δ2)) k2 ≺ α^γ1[Φ]). { rewrite Hee. exact Htail2. }
        assert (Heqd: α^γ1[Φ] ⋅ δ1[Φ] + Sum (f α (lsh γ1) (lsh δ1)) k1
                    = α^γ1[Φ] ⋅ δ2[Φ] + Sum (f α (lsh γ2) (lsh δ2)) k2).
        { rewrite <- Hβ1', Hβ2', Hee; auto. }
        pose proof (div_unique (α^γ1[Φ]) (δ1[Φ]) (δ2[Φ]) (Sum (f α (lsh γ1) (lsh δ1)) k1)
                    (Sum (f α (lsh γ2) (lsh δ2)) k2) HOe Hδ10 Hδ20 HT1O HT2O Htail1 HtailT2 Heqd) as [Hδeq HTeq].
        assert (Hδ1dd: dom(δ1) = PlusOne (PlusOne k1)). { rewrite Hδ1d; auto. }
        assert (Hδ2dd: dom(δ2) = PlusOne (PlusOne k2)). { rewrite Hδ2d; auto. }
        assert (Hγ1'd: dom(lsh γ1) = PlusOne k1). { apply (lsh_dom γ1 (PlusOne k1)); auto. }
        assert (Hδ1'd: dom(lsh δ1) = PlusOne k1). { apply (lsh_dom δ1 (PlusOne k1)); auto. }
        assert (Hγ2'd: dom(lsh γ2) = PlusOne k2). { apply (lsh_dom γ2 (PlusOne k2)); auto. }
        assert (Hδ2'd: dom(lsh δ2) = PlusOne k2). { apply (lsh_dom δ2 (PlusOne k2)); auto. }
        assert (Hγ1'r: ran(lsh γ1) ⊂ R). { apply (lsh_ranB γ1 (PlusOne k1) R); auto. }
        assert (Hδ1'rα: ran(lsh δ1) ⊂ α). { apply (lsh_ranB δ1 (PlusOne k1) α); auto. }
        assert (Hγ2'r: ran(lsh γ2) ⊂ R). { apply (lsh_ranB γ2 (PlusOne k2) R); auto. }
        assert (Hδ2'rα: ran(lsh δ2) ⊂ α). { apply (lsh_ranB δ2 (PlusOne k2) α); auto. }
        assert (Hmono1': Monodc_f (lsh γ1)). { apply (lsh_Monodc γ1 (PlusOne k1)); auto. }
        assert (Hmono2': Monodc_f (lsh γ2)). { apply (lsh_Monodc γ2 (PlusOne k2)); auto. }
        assert (Hrep1: OnTo (lsh γ1) (PlusOne k1) R /\ Monodc_f (lsh γ1) /\ OnTo (lsh δ1) (dom(lsh γ1)) α
                       /\ (∀ k, (lsh δ1)[k] ≠ Φ) /\ Sum (f α (lsh γ1) (lsh δ1)) k1 = Sum (f α (lsh γ1) (lsh δ1)) k1).
        { split; [split; [apply lsh_fun | split; auto] | ].
          split; [auto | ]. split; [split; [apply lsh_fun | split; [rewrite Hδ1'd, Hγ1'd; auto | auto]] | ].
          split; [apply lsh_nz; auto | auto]. }
        assert (Hrep2: k2 ∈ ω /\ OnTo (lsh γ2) (PlusOne k2) R /\ Monodc_f (lsh γ2) /\ OnTo (lsh δ2) (dom(lsh γ2)) α
                       /\ (∀ k, (lsh δ2)[k] ≠ Φ) /\ Sum (f α (lsh γ1) (lsh δ1)) k1 = Sum (f α (lsh γ2) (lsh δ2)) k2).
        { split; [auto | ]. split; [split; [apply lsh_fun | split; auto] | ].
          split; [auto | ]. split; [split; [apply lsh_fun | split; [rewrite Hδ2'd, Hγ2'd; auto | auto]] | ].
          split; [apply lsh_nz; auto | exact HTeq]. }
        pose proof (IH (Sum (f α (lsh γ1) (lsh δ1)) k1) k2 (lsh γ1) (lsh δ1) (lsh γ2) (lsh δ2)
                    HOα Hα Hrep1 Hrep2) as [Hkeq [Hγeq Hδeq2]].
        split; [rewrite Hkeq; auto | split].
        * apply (unshift_eq (PlusOne k1) γ1 γ2); auto. rewrite Hγ2d, <- Hkeq; auto.
        * apply (unshift_eq (PlusOne k1) δ1 δ2); auto. rewrite Hδ2dd, <- Hkeq; auto. }
  intros β n1 γ1 δ1 n2 γ2 δ2 H Hα R1 R2.
  destruct R1 as [Hn1 R1'].
  apply (Hmain n1 Hn1 β n2 γ1 δ1 γ2 δ2 H Hα R1' R2).
Qed.
