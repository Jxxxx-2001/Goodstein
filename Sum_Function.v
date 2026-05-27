Require Export OrdinalNum.R_Operation_Exp.

Theorem MKT128 :  ∀ g, exists ! f, Function f /\ Ordinal dom(f) 
  /\ (∀ x, Ordinal_Number x -> f[x] = g[f|(x)]).
Proof.
  intros. New (MKT128a g). destruct H as [f]. exists f. split. auto.
  intros. New (MKT128b g x' H0 f H). symmetry. auto.
Qed.

Ltac μ_notset :=
  match goal with
  | H: μ ∈ ?a
    |- _ => New MKT39; appA2H H; contradiction
  | H1: ?a = μ, H2: Ensemble ?a
    |- _ => rewrite H1 in H2; New MKT39; contradiction
  | H1: μ = ?a, H2: Ensemble ?a
    |- _ => rewrite <- H1 in H2; New MKT39; contradiction
  | H1: ?a = ?b, H2: ?b = μ, H3: Ensemble ?a
    |- _ => rewrite H1,H2 in H3; New MKT39; contradiction
  | H1: ?a = ?b, H2: ?a = μ, H3: Ensemble ?b
    |- _ => rewrite <- H1 in H3; rewrite H2 in H3; New MKT39; contradiction
  end.

Lemma Add_μ : ∀ a, a + μ = μ.
Proof.
  intros. eqext. appA2H H; auto. appA2G. intros. appA2H H0.
  deand. apply AddFunction_R in H1 as [H1 [H3 _]]. deand. New H3.
  apply H2 in H3; eauto. subst y. destruct H6 as [H3 [H6 _]].
  assert( μ ∉ dom(H1) ). red. unfold not. intros. μ_notset.
  eapply MKT69a in H7; eauto. rewrite H7; auto.
  intros. apply H5 in H7 as [H7 _]; auto.
  intros. New H7. apply H5 in H7 as [_ H7]; auto.
Qed.

Definition G f := \{\ λ u v, ( dom(u) ∉ ω /\ v = μ )
  \/ ( dom(u) ∈ ω /\ ( ( dom(u) = Φ /\ v = f[Φ] )
  \/ ( dom(u) ≠ Φ /\ v = u[∪dom(u)] + f[dom(u)] ) ) ) \}\.

Lemma G' : ∀ f h, Ordinal_Number dom(f)
  -> (∀ x, Ordinal_Number x -> h[x] = (G f)[h|(x)])
  -> h[Φ] = f[Φ].
Proof.
  intros. New (H0 Φ Φ_is_Ord). rewrite H1.
  assert( h | (Φ) = Φ ). eqE. appA2H H2. rdeHex. appA2H H4. rdeHex. emf.
  rewrite H2. assert( dom(Φ) = Φ ). eqE. appA2H H3. rdeHex. emf.
  eqext. TF( dom(f) = Φ ). assert( f[Φ] = μ ).
  eapply MKT69a. rewrite H5. apply MKT101. rewrite H6. appA2H H4. auto.
  appA2H H4. apply H6. assert( Ensemble f[Φ] ).
  { eapply MKT19,MKT69b; eauto. eapply Φ_is_First_Ord; eauto. }
  appA2G. appoA2G. right. rewrite H3. auto.
  appA2G. intros. appA2H H5. appoA2H H6. rewrite H3 in H7.
  destruct H7; deand. New MKT135a. contradiction.
  destruct H8; deand; subst; auto. contradiction.
Qed.

Lemma pre_G'' : ∀ h k, Function h -> Ordinal dom(h) -> PlusOne k ∈ dom(h)
  -> h[k] = (h|(PlusOne k))[∪(PlusOne k)] .
Proof.
  intros. assert( Ordinal_Number (PlusOne k) ). { appA2G. eapply MKT111; eauto. }
  assert( k ∈ PlusOne k ).
  { appA2H H1. eapply AxiomIV' in H1. deand. appA2G. }
  New (trans_Ord_Num _ _ H2 H3). rewrite MKT124; auto.
  pose proof (Property_res h (PlusOne k) k H H0 H1 H3) as [H5 _]. auto.
Qed.

Lemma G'' : ∀ f h k, Function f -> ran(f) ⊂ R
  -> Function h -> Ordinal dom(h)
  -> (∀ x, Ordinal_Number x -> h[x] = (G f)[h|(x)])
  -> PlusOne k ∈ dom(h) -> k ∈ ω
  -> h[PlusOne k] = h[k] + f[PlusOne k].
Proof.
  intros. assert( k ∈ PlusOne k ). appA2G.
  assert( Ordinal_Number (PlusOne k) ). { appA2G. eapply MKT111; eauto. }
  New H7. apply H3 in H8. rewrite H8. clear H8.
  pose proof (Property_res_dom h _ H1 H2 H4) as [].
  TF( PlusOne k ∈ dom(f) ).
  - eapply Property_dm in H10; eauto. TF( h[k] ∈ R ).
    assert( Ensemble (h[k] + f[PlusOne k]) ).
    { exists R. eapply R_Add_in_R; eauto. apply H0 in H10; auto. }
    eqext. appA2H H13. apply H14. appA2G. appoA2G. rewrite H9.
    right. split; try eapply MKT134; eauto.
    right; split; try eapply MKT135b in H5; eauto. rewrite pre_G''; auto.
    appA2G. intros. appA2H H14. appoA2H H15. rewrite H9 in H16.
    New H5. eapply MKT134 in H5; eauto. eapply MKT135b in H17; eauto.
    destruct H16; deand; try contradiction; try subst y. unfold not in H17.
    destruct H18; deand. symmetry in H18; contradiction. subst y.
    rewrite <- pre_G''; auto. assert( h[k] + f[PlusOne k] = μ ).
    { unfold Add_R. eqext. appA2H H12; auto. appA2G. intros. appA2H H13.
      destruct H14. contradiction. }
    rewrite H12. eqext. appA2H H13; auto. appA2G. intros. appA2H H14.
    appoA2H H15. rewrite H9 in H16.
    New H5. eapply MKT134 in H5; eauto. eapply MKT135b in H17; eauto.
    destruct H16; deand; try contradiction; try subst y. unfold not in H17.
    destruct H18; deand. symmetry in H18; contradiction. subst y.
    rewrite <- pre_G''; auto. rewrite H12. auto.
  - eapply MKT69a in H10; eauto. rewrite H10,Add_μ; eauto.
    eqext. appA2H H11; auto. appA2G. intros. appA2H H12. appoA2H H13.
    rewrite H9 in H14. New H5. eapply MKT134 in H5.
    destruct H14; deand; try contradiction.
    destruct H16; deand. eapply MKT135b in H15. symmetry in H16; contradiction. subst y.
    rewrite <- pre_G''; auto. rewrite H10,Add_μ; auto.
Qed.

Theorem CNF_f : ∀ f, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> exists ! h, Function h /\ dom(h) = dom(f) /\ ran(h) ⊂ R
  /\ h[Φ] = f[Φ]
  /\ ∀ n, (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n].
Proof.
  intros. New (MKT128 (G f)). destruct H2 as [h]. exists h. split.
  - (* 存在性 *)
    destruct H2 as [H2 _]. deand. split; auto.
    New (trans_Ord_Num _ _ MKT138 H0). New H5. appA2H H6.
    New (MKT110 H3 H7). clear H6 H7.
    assert( H': dom(h) ≼ dom(f) -> ∀ n, n ∈ ω -> n ∈ dom(h) -> h[n] ∈ R ).
    { intro. assert( dom(h) ⊂ dom(f) ).
      eapply MKT118 in H6; eauto. appA2H H5. auto. intros n H9.
      eapply Mathematical_Induction with (n:=n); eauto.
      intros. New (G' f h H5 H4). rewrite H11. apply H1,Property_dm; auto.
      intros. assert( k ∈ dom(h) ).
      { destruct H3 as [_ H3]. apply H3 in H12.
        assert( k ∈ PlusOne k ). appA2G. auto. }
      apply H11 in H13; auto. New H12. apply H7 in H14.
      New (G'' f h k H H1 H2 H3 H4 H12 H10).
      rewrite H15. eapply R_Add_in_R; eauto. apply H1,Property_dm; auto. }
    try destruct H8; try destruct H6.
    + (* dom(h) ∈ dom(f) *)
      TF( dom(h) = Φ ). New (G' f h H5 H4).
      assert( Ensemble f[Φ] ). eapply MKT19,MKT69b. rewrite <- H7; auto.
      assert( h[Φ] = μ ). eapply MKT69a. rewrite H7. apply MKT101. μ_notset.
      (* dom(h) ≠ Φ *)
      New (trans_Ord_Num _ _ H5 H6). apply H4 in H8.
      New (MKT69a (MKT101 dom(h))). assert( dom(h) ⊂ dom(h) ). auto.
      New (frebig h _ H2 H10). rewrite H11 in H8.
      assert( h[∪dom(h)] + f[dom(h)] ∈ R ).
      { eapply R_Add_in_R; eauto. New (Ord_Num_trans dom(h) _ ω MKT138 H6 H0).
        assert( ∪dom(h) ∈ dom(h) ).
        { apply ω_Num_is_Suc_Ord in H12; auto. destruct H12. deand.
          rewrite H13, MKT124; eauto. appA2G. }
        eapply H'; eauto. left; auto. eapply Ord_Num_trans; eauto.
        apply MKT138. apply H1,Property_dm; auto. }
      assert( (G f)[h] = h[∪dom(h)] + f[dom(h)] ).
      { eqext. appA2H H13. apply H14. appA2G. appoA2G.
        eapply MKT49a; eauto. eapply MKT75; eauto. right. split.
        eapply (Ord_Num_trans _ _ _ MKT138); eauto. right; split; auto.
        appA2G. intros. appA2H H14. appoA2H H15. destruct H16; deand.
        subst y. appA2H H13; auto.
        destruct H17; deand; try contradiction; try subst y; auto. }
      rewrite <- H13 in H12. appA2H H12. μ_notset.
    + (* dom(f) ∈ dom(h) *)
      assert( ∃ x, x ∈ dom(h) /\ x ∉ dom(f) ).
      { exists dom(f). split; auto. apply MKT101. }
      rdeHex. TF( x = Φ ). subst x. TF( dom(f) = Φ ). New (G' f h H5 H4).
      assert( f[Φ] = μ ). eapply MKT69a. rewrite H9. apply MKT101.
      apply Property_dm in H7; auto. appA2H H7. μ_notset.
      apply Φ_is_First_Ord in H9; auto. contradiction.
      pose proof (Property_res_dom h x H2 H3 H7) as [].
      (* x ∈ ω *)
      TF( x ∈ ω ). New H12. eapply ω_Num_is_Suc_Ord in H13; eauto.
      destruct H13; deand. subst x.
      assert( x0 ∈ ω ). { eapply (Ord_Num_trans _ _ _ MKT138 _ H12); eauto. }
      New (G'' f h x0 H H1 H2 H3 H4 H7 H14).
      assert( h[x0] + f[PlusOne x0] = μ ).
      { eapply MKT69a in H8; eauto. rewrite H8. rewrite (Add_μ (h[x0])); eauto. }
      rewrite H16 in H15. apply Property_dm in H7; eauto. appA2H H7. μ_notset.
      (* x ∉ ω *)
      assert( Ordinal_Number x ). appA2G. eapply MKT111; eauto.
      apply H4 in H13. assert( (G f)[h | (x)] = μ ).
      eqext. appA2H H14; auto. appA2G. intros. appA2H H15. appoA2H H16.
      rewrite H11 in H17. destruct H17; deand; try subst; auto. contradiction.
      rewrite H14 in H13. apply Property_dm in H7; auto. appA2H H7. μ_notset.
    + split; auto. split. red. intros. appA2H H7. rdeHex.
      apply Property_Fun in H8; auto. subst z.
      apply MKT19,(@ MKT69b') in H7; auto. eapply H'; eauto.
      right; auto. eapply Ord_Num_trans; eauto. apply MKT138. rewrite H6; auto.
      split. eapply G'; eauto. intros.
      assert( n ∈ PlusOne n ). appA2H H7. apply AxiomIV' in H7. deand. appA2G.
      assert( n ∈ ω ). rewrite H6 in H7.
      try repeat (eapply Ord_Num_trans; eauto; try apply MKT138).
      eapply G''; eauto.
  - destruct H2. clear H2. intros. apply H3. clear H3.
    deand. split; auto. split. rewrite H3. eapply MKT111; eauto.
    intros. New H7. assert( Ordinal dom(x') ). rewrite H3. eapply MKT111; eauto.
    appA2H H7. New (Th110ano H10 H9). clear H7 H10. destruct H11.
    + TF( x = Φ ). subst x. rewrite H5.
      pose proof (Property_res_dom _ _ H2 H9 H7) as [].
      eqext. appA2G. intros. appA2H H13. appoA2H H14.
      rewrite H11 in H15. destruct H15; deand. New MKT135a. contradiction.
      destruct H16; deand; try subst; auto; try contradiction.
      appA2H H12. apply H13. clear z H12 H13.
      assert( f[Φ] ∈ R ). rewrite <- H5. apply Property_dm in H7; auto.
      appA2G. appoA2G. right. rewrite H11. split; try apply MKT135a; auto.
      rewrite H3 in H7.
      assert( x ∈ ω ). { eapply Ord_Num_trans; eauto. eapply MKT138. }
      New H11. eapply ω_Num_is_Suc_Ord in H11; eauto.
      destruct H11. deand. subst x. assert( x0 ∈ ω ).
      { assert( x0 ∈ PlusOne x0 ). appA2G.
        eapply Ord_Num_trans; eauto. eapply MKT138. }
      rewrite <- H3 in H7. New H7. apply H6 in H7. rewrite H7.
      pose proof (Property_res_dom _ _ H2 H9 H14) as [].
      eqext. appA2G. intros. appA2H H18. appoA2H H19. rewrite H16 in H20.
      destruct H20; deand. subst y. appA2H H17. auto.
      destruct H21; deand. assert( x0 ∈ PlusOne x0 ). appA2G.
      rewrite H21 in H23. emf. rewrite <- pre_G'' in H22; eauto. subst y; auto.
      appA2H H17. apply H18. clear z H17 H18.
      assert( x'[x0] + f[PlusOne x0] ∈ R ).
      { apply R_Add_in_R. apply H4,Property_dm; auto.
        assert( x0 ∈ PlusOne x0 ). appA2G. eapply Ord_Num_trans; eauto.
        rewrite H3. appA2G. eapply (MKT111 _ _ _ H0); eauto.
        apply H1,Property_dm; auto. rewrite <- H3. auto. }
      appA2G. appoA2G. rewrite H16. right; split; auto. right; split.
      apply MKT135b in H13. auto. rewrite pre_G''; auto.
    + rewrite frebig; eauto. assert( x'[x] = μ ). eapply MKT69a; eauto.
      red. unfold not. intros. apply H7 in H10. NSym.
      rewrite H10. eqext. appA2G. intros. appA2H H12. appoA2H H13.
      destruct H14; deand; try subst; auto. destruct H15; deand.
      subst y. rewrite <- H5. assert( Φ ∉ dom(x') ). rewrite H15.
      apply MKT101. apply MKT69a in H16. rewrite H16; auto.
      assert( f[dom(x')] = μ ). eapply MKT69a; eauto. rewrite H3; apply MKT101.
      rewrite H17,Add_μ in H16. subst y; auto. appA2H H11; auto.
      Unshelve. appA2G. New MKT138. appA2H H18; auto.
Qed.

Definition Sum f n := ∩ (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
  ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
  -> h[Φ] = f[Φ]
  -> (∀ n, (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
  -> u = h[n] ) \}).

Lemma Sum_Lemma1 : ∀ f n, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> (PlusOne n) ∈ dom(f)
  -> Sum f (PlusOne n) = Sum f n + f[PlusOne n].
Proof.
  intros. pose proof H. apply CNF_f in H3 as [h1[[H3[H4[H5[]]]]]]; auto.
  assert (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
    ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
    -> h[Φ] = f[Φ]
    -> (∀ n, (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
    -> u = h[PlusOne n] ) \} = [h1[PlusOne n]]).
  { apply AxiomI; split; intros. apply AxiomII in H9 as [H9[H10[H11[]]]].
    apply H13 in H7; auto. apply MKT41; auto. rewrite <- H7. auto.
    assert (Ensemble z). eauto. apply MKT41 in H9. apply AxiomII. split; auto.
    split; auto. split; auto. split; auto. intros.
    assert (h1 = h). { apply H8; auto. } rewrite <-H16; auto.
    rewrite <- H4 in H2. eapply Property_dm in H2; eauto. }
  unfold Sum at 1. rewrite H9. assert (Ensemble (h1[PlusOne n])).
  { rewrite <- H4 in H2. eapply Property_dm in H2; eauto. }
  apply MKT44 in H10 as []. rewrite H10,H7; try rewrite H4; auto.
  assert ( Ensemble h1[n] ).
  { eapply MKT19a,MKT69b; eauto. rewrite H4. eapply Ord_Num_trans; eauto.
      eapply trans_Ord_Num; eauto. eapply MKT138. appA2H H2.
      apply AxiomIV' in H2. deand. appA2G. }
  assert (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
    ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
    -> h[Φ] = f[Φ]
    -> (∀ n, (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
    -> u = h[n] ) \} = [h1[n]]).
  { apply AxiomI; split; intros. apply AxiomII in H13 as [H13[H14[H15[]]]].
    apply H17 in H7; auto. apply MKT41; auto. appA2G.
    try repeat (split; auto). intros.
    assert (h1 = h). { apply H8; auto. } rewrite <- H19. appA2H H13. auto. }
  unfold Sum. rewrite H13. apply MKT44 in H12 as []. rewrite H12; auto.
Qed.

Lemma Sum_Lemma2 : ∀ f, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> Sum f Φ = f[Φ].
Proof.
  intros. pose proof H. apply CNF_f in H2 as [h1[[H2[H3[H4[]]]]]]; auto.
  destruct (classic (Φ ∈ dom(f))).
  assert (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
    ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
    -> h[Φ] = f[Φ]
    -> (∀ n, (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
    -> u = h[Φ] ) \} = [h1[Φ]]).
  { apply AxiomI; split; intros. apply AxiomII in H9 as [H9[H10[H11[]]]].
    apply H13 in H6; auto. apply MKT41; auto. rewrite <-H6. auto.
    assert (Ensemble z). eauto. apply MKT41 in H9. apply AxiomII. split; auto.
    split; auto. split; auto. split; auto. intros.
    assert (h1 = h). { apply H7; auto. } rewrite <-H16; auto.
    apply MKT69b in H8; auto. rewrite H5. auto. }
  unfold Sum. rewrite H9. rewrite <- H5. eapply MKT44; eauto.
  rewrite H5. eapply Property_dm in H8; eauto.
  assert (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
    ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
    -> h[Φ] = f[Φ]
    -> (∀ n, (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
    -> u = h[Φ] ) \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H9 as [H9[H10[H11[]]]].
    apply H13 in H6; auto. rewrite <-H3 in H8.
    apply MKT69a in H8. μ_notset. emf. }
  unfold Sum. rewrite H9. apply MKT69a in H8. rewrite H8. apply MKT24.
Qed.

Lemma Sum_Lemma3 : ∀ f n, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> n ∈ dom(f) -> (Sum f n) ∈ R.
Proof.
  set (p := fun n => ∀ f, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
    -> n ∈ dom(f) -> (Sum f n) ∈ R).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction.
    - unfold p. intros. rewrite Sum_Lemma2; auto.
      apply H1,(@Property_ran Φ),Property_Value; auto.
    - unfold p; intros. assert (k ∈ dom(f)).
      assert( k ∈ PlusOne k ). appA2G.
      eapply Ord_Num_trans; eauto. eapply trans_Ord_Num; eauto.
      eapply MKT138.
      rewrite Sum_Lemma1; auto. apply R_Add_in_R. apply H0; auto.
      apply H3,(@Property_ran (PlusOne k)),Property_Value; auto. }
  intros. apply H; auto. eapply Ord_Num_trans; eauto. eapply MKT138.
Qed.

Lemma Sum_Lemma4 : ∀ f g n, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> Function g -> dom(g) ∈ ω -> ran(g) ⊂ R
  -> n ∈ dom(g) -> (PlusOne n) ∈ dom(f)
  -> (∀ m, m ∈ n \/ m = n -> g[m] = f[PlusOne m])
  -> Sum f (PlusOne n) = f[Φ] + Sum g n.
Proof.
  set (p := fun n => ∀ f g, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
    -> Function g -> dom(g) ∈ ω -> ran(g) ⊂ R
    -> n ∈ dom(g) -> (PlusOne n) ∈ dom(f)
    -> (∀ m, m ∈ n \/ m = n -> g[m] = f[PlusOne m])
    -> Sum f (PlusOne n) = f[Φ] + Sum g n).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction.
    - unfold p. intros. rewrite Sum_Lemma1; auto.
      rewrite Sum_Lemma2,Sum_Lemma2,H7; auto.
    - unfold p; intros.
      assert (k ∈ dom(g) /\ (PlusOne k) ∈ dom(f)) as [].
      { assert( k ∈ PlusOne k ). appA2G. split.
        eapply Ord_Num_trans; eauto. eapply trans_Ord_Num; eauto.
        apply MKT138. assert( PlusOne k ∈ PlusOne(PlusOne k) ). appA2G.
        eapply Ord_Num_trans; eauto. eapply trans_Ord_Num; eauto. eapply MKT138. }
      pose proof (H0 f g H1 H2 H3 H4 H5 H6 H10 H11).
      rewrite Sum_Lemma1; auto. rewrite H12. rewrite Sum_Lemma1; auto.
      rewrite (H9 (PlusOne k)); auto. apply Add_R_Association.
      assert (Φ ∈ dom(f)).
      { eapply Φ_is_First_Ord; eauto. eapply trans_Ord_Num; eauto.
        apply MKT138. red. intros. rewrite H13 in H8. emf. }
      apply Property_Value,Property_ran in H13; auto. apply Sum_Lemma3; auto.
      apply H3,(@Property_ran (PlusOne (PlusOne k))),Property_Value; auto.
      intros. apply H9. destruct H13; left; apply MKT4; auto. right.
      apply MKT41; eauto. }
  intros. apply H; auto. eapply Ord_Num_trans; eauto. apply MKT138.
Qed.