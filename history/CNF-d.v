Require Export R_Operation_Exp.

Theorem MKT128 :  ∀ g, exists ! f, Function f /\ Ordinal dom(f) 
  /\ (∀ x, Ordinal_Number x -> f[x] = g[f|(x)]).
Proof.
  intros. New (MKT128a g). destruct H as [f]. exists f. split. auto.
  intros. New (MKT128b g x' H0 f H). symmetry. auto.
Qed.

Definition G f := \{\ λ u v, ( dom(u) ∉ ω /\ v = μ )
 \/ ( dom(u) ∈ ω /\ ( ( dom(u) = Φ /\ v = f[Φ] )
 \/ ( dom(u) ≠ Φ /\ v = u[∪dom(u)] + f[dom(u)] ) ) ) \}\.

Lemma G' : ∀ f h, OnTo f ω R -> Function h -> Ordinal dom(h)
  -> (∀ x, Ordinal_Number x -> h[x] = (G f)[h|(x)])
  -> h[Φ] = f[Φ].
Proof.
  intros. New (H2 Φ Φ_is_Ord). rewrite H3. clear H2 H3. New Φ_is_Ord.
  assert( H': f[Φ] ∈ R ).
  { destruct H as [H[]]. New MKT135a. rewrite <- H3 in H5.
    eapply Property_dm in H5; eauto. }
  TF( dom(h) = Φ ).
  - rewrite (frebig h Φ H0).
    eqext. appA2H H4. apply H5. clear z H4 H5.
    appA2G. appoA2G. eapply MKT49a; eauto.
    eapply MKT75; eauto. rewrite H3. auto.
    right. split. rewrite H3. apply MKT135a.
    left. split; auto.
    appA2G. intros. appA2H H5. appoA2H H6. destruct H7. deand.
    rewrite H3 in H7. New MKT135a. contradiction.
    deand. destruct H8; deand; subst; auto; contradiction.
    rewrite H3. red. intros. emf.
  - assert( Φ ∈ dom(h) ). appA2H H2. New (Th110ano H4 H1).
    destruct H5; auto. eapply (MKT118 _ _ H1 H4) in H5; eauto.
    destruct H5. emf. contradiction.
    pose proof (Property_res_dom h Φ H0 H1 H4) as [].
    eqext. appA2H H7. apply H8. clear z H7 H8.
    appA2G. appoA2G. right. split. rewrite H6; auto. left. split; auto.
    appA2G. intros. appA2H H8. appoA2H H9. destruct H10. deand.
    rewrite H6 in H10. New MKT135a. contradiction. deand.
    try repeat (destruct H11,H11; try contradiction; try subst; auto ).
Qed.

Lemma G'' : ∀ f h k, OnTo f ω R -> Function h -> Ordinal dom(h)
  -> (∀ x, Ordinal_Number x -> h[x] = (G f)[h|(x)])
  -> PlusOne k ∈ dom(h) -> k ∈ ω -> h[k] ∈ R
  -> h[PlusOne k] = h[k] + f[PlusOne k].
Proof.
  intros. New (trans_Ord_Num ω _ MKT138 (MKT134 H4)). New H6.
  apply H2 in H6. rewrite H6. clear H2 H6.
  assert( h[k] + f[PlusOne k] ∈ R ).
  { apply R_Plus_in_R. eapply H5; auto. assert( PlusOne k ⊂ dom(h) ).
    appA2H H7. pose proof (Th110ano H1 H6) as [].
    New (MKT102 _ _ H3 H7). destruct H8. auto.
    destruct H as [H[]]. apply H8. eapply Property_dm; eauto.
    rewrite H6. apply MKT134; auto. }
  pose proof (Property_res_dom h _ H0 H1 H3) as [].
  assert( h[k] + f[PlusOne k]
    = (h|(PlusOne k))[∪dom(h|(PlusOne k))] + f[dom(h|(PlusOne k))] ).
  { rewrite H8. assert( k ∈ R ).
    { eapply trans_Ord_Num in H4; eauto. apply MKT138. }
    rewrite MKT124; eauto. assert( k ∈ PlusOne k ). appA2G.
    pose proof (Property_res _ (PlusOne k) k H0 H1 H3 H10) as [].
    rewrite H11; auto. }
  assert( (G f) [h | (PlusOne k)] = h[k] + f[PlusOne k] ).
  { eqext. appA2H H10. apply H11. clear z H10 H11.
    appA2G. appoA2G. right. split. rewrite H8; auto. right. split.
    rewrite H8. red. intros. apply (MKT135b _ H4). auto.
    rewrite <- H9; auto. appA2G. intros. appA2H H11.
    appoA2H H12; destruct H13; deand. rewrite H8 in H13.
    apply MKT134 in H4. contradiction.
    destruct H14; deand; rewrite H8 in H14. New (MKT135b _ H4).
    symmetry in H14. apply H16 in H14. destruct H14.
    subst y. rewrite <- H9; auto. }
  symmetry; auto.
Qed.

Theorem CNF_f : ∀ f, OnTo f ω R
  -> exists ! h, OnTo h ω R
  /\  h[Φ] = f[Φ]
  /\ ∀ n, n ∈ ω -> h[PlusOne n] = h[n] + f[PlusOne n].
Proof.
  intros. New (MKT128 (G f)). destruct H0 as [h]. exists h. split.
  - destruct H0 as [H0 _]. deand.
    assert( ∀ n, n ∈ ω -> n ∈ dom(h) -> h[n] ∈ R ).
    { intros n H4. eapply Mathematical_Induction with (n:=n); eauto.
      intros. New (G' f h H H0 H1 H2). rewrite H5. destruct H as [H []].
      apply H7. eapply Property_dm; try rewrite H6; auto. intros.
      assert( k ∈ dom(h) ).
      { destruct H1 as [_ H1]. apply H1 in H6.
        assert( k ∈ PlusOne k ). appA2G. auto. }
      apply H5 in H7. New (G'' f h k H H0 H1 H2 H6 H3 H7).
      rewrite H8. eapply R_Plus_in_R; eauto.
      destruct H as [H[]]. apply H10,Property_dm; eauto.
      rewrite H9. eapply MKT134; auto. }
    assert( dom(h) = ω ).
    { New MKT138. appA2H H4. New (MKT110 H1 H5).
      try repeat destruct H6; auto.
      TF( dom(h) = Φ ). New (G' f h H H0 H1 H2).
      New (H2 _ Φ_is_Ord). rewrite H8 in H9.
      assert( f[Φ] ∈ R ).
      { destruct H as [H[]]. New MKT135a. rewrite <- H10 in H12.
        eapply Property_dm in H12; eauto. }
      assert( h[Φ] = μ ). eapply MKT69a. rewrite H7. eapply MKT101; eauto.
      rewrite H11 in H8. rewrite <- H8 in H10. appA2H H10.
      apply MKT39 in H10. destruct H10.
      assert( Ordinal_Number dom(h) ).
      { eapply trans_Ord_Num; eauto. eapply MKT138. }
      New H8. apply H2 in H8.
      assert( ∪dom(h) ∈ dom(h) ).
      { assert( dom(h) ⊂ R ). red. intros. eapply trans_Ord_Num; eauto.
        eapply MKT120 in H10. pose proof (Th110ano H10 H1). destruct H11; auto.
        eapply (MKT118 _ _ H1 H10) in H11; eauto. destruct H11. appA2H H11.
        destruct H12. deand. eapply MKT102 in H12; eauto. destruct H12.
        eapply ω_Num_is_Suc_Ord in H6; eauto. destruct H6. deand.
        assert( x ∈ ∪dom(h) ). rewrite <- H11. rewrite H12. appA2G.
        appA2H H13. destruct H14. deand. rewrite H12 in H15.
        eapply Ord_Num_not_dense in H14; eauto. contradiction.
        rewrite <- H12 in H15. eapply trans_Ord_Num; eauto. }
      assert( h[∪dom(h)] + f[dom(h)] ∈ R ).
      { apply R_Plus_in_R. apply H3; auto. eapply Ord_Num_trans; eauto.
        appA2G; auto. destruct H as [H[]].
        apply H12,Property_dm; auto. rewrite H11; auto. }
      assert( (G f)[h|(dom(h))] = h[∪dom(h)] + f[dom(h)] ).
      { New (frebig h dom(h) H0 (MKT26a dom(h))). rewrite H12.
        eqext. appA2H H13. apply H14. clear z H13 H14.
        appA2G. appoA2G. eapply MKT49a; eauto.
        eapply MKT75; eauto.
        appA2G. intros. appA2H H14. appoA2H H15.
        destruct H16; deand. contradiction.
        destruct H17; deand; try subst; auto; try contradiction. }
      rewrite H12 in H8. clear H12. rewrite <- H8 in H11.
      assert( h[dom(h)] = μ ). eapply MKT69a. eapply MKT101; eauto.
      rewrite H12 in H11. appA2H H11. apply MKT39 in H11. destruct H11.
      pose proof (Property_res_dom _ _ H0 H1 H6) as [_ H7].
      New (H2 _ MKT138). assert( (G f)[h|(ω)] = μ ).
      { eqext. appA2H H9. auto. appA2G. intros.
        appA2H H10. appoA2H H11. destruct H12; deand; subst; auto.
        rewrite H7 in H12. NSym. }
      rewrite H9 in H8. apply Property_dm in H6; auto.
      rewrite H8 in H6. appA2H H6. apply MKT39 in H6. destruct H6. }
    split; auto. split; auto. split; auto.
    red. intros. apply Einr in H5; auto. destruct H5. deand.
    subst z. New H5. rewrite H4 in H5. eapply H3; eauto.
    split. eapply G'; eauto. intros. eapply G''; eauto.
    rewrite H4. apply MKT134; auto. New H5.
    rewrite <- H4 in H5. eapply H3; eauto.
  - destruct H0. clear H0. intros. apply H1. clear H1.
    deand. split. destruct H0; auto. split. destruct H0 as [H0[]].
    rewrite H3. New MKT138. appA2H H5; auto. intros.
    destruct H0 as [H0[]]. New H3.
    New MKT138. appA2H H7. appA2H H3. rewrite <- H4 in H8.
    New (Th110ano H9 H8). clear H3 H9 H7. destruct H10.
    + TF( x = Φ ). subst x. rewrite H1.
      pose proof (Property_res_dom _ _ H0 H8 H3) as [].
      eqext. appA2G. intros. appA2H H11. appoA2H H12.
      destruct H13; deand. rewrite H9 in H13. rewrite H4 in H3. contradiction.
      destruct H14; deand; try subst; auto; try contradiction.
      appA2H H10. apply H11. clear z H10 H11.
      assert( f[Φ] ∈ R ). destruct H as [H[]]. apply H11,Property_dm; auto.
      rewrite H10. apply MKT135a. appA2G. appoA2G. right.
      split. rewrite H9. apply MKT135a. left. split; auto.
      rewrite H4 in H3. New H3. eapply ω_Num_is_Suc_Ord in H9; eauto.
      destruct H9. deand. subst x. assert( x0 ∈ ω ).
      { assert( x0 ∈ PlusOne x0 ). appA2G. eapply Ord_Num_trans; eauto.
        eapply MKT138. }
      apply H2 in H10. rewrite H10. rewrite <- H4 in H3.
      pose proof (Property_res_dom _ _ H0 H8 H3) as [].
      eqext. appA2G. intros. appA2H H14. appoA2H H15.
      destruct H16; deand. rewrite H12 in H16. rewrite H4 in H3. contradiction.
      destruct H17; deand. rewrite H12 in H17. contradiction. subst y.
      rewrite H12. rewrite MKT124; auto.
      rewrite MKT126c; eauto. rewrite H12. appA2G.
      appA2H H13. apply H14. clear z H13 H14.
      assert( x'[x0] + f[PlusOne x0] ∈ R ).
      { apply R_Plus_in_R. apply H5,Property_dm; auto.
        assert( x0 ∈ PlusOne x0 ). appA2G. eapply Ord_Num_trans; eauto.
        rewrite H4. apply MKT138. destruct H as [H[]].
        apply H14,Property_dm; auto. rewrite H13. rewrite <- H4; auto. }
      appA2G. appoA2G. right. split. rewrite H12. rewrite <- H4. auto.
      right. split; rewrite H12; auto. rewrite MKT124; auto.
      rewrite MKT126c; eauto. rewrite H12. appA2G.
    + rewrite frebig; eauto. assert( x'[x] = μ ). eapply MKT69a; eauto.
      red. unfold not. intros. apply H3 in H7. NSym.
      rewrite H7. eqext. appA2G. intros. appA2H H10. appoA2H H11.
      destruct H12; deand; try subst; auto. rewrite H4 in H12. NSym.
      appA2H H9; auto.
Qed.

(* 这是我用 CNF_f 证的定义域不完全等于ω的情况.
   应该也可以利用CNF_f直接改造, 可以自己选择一下怎么呈现 *)
   (* 这个定理中的 n ∈ dom(h) 和 (PlusOne n) ∈ dom(h) 两个条件感觉能省略掉一个,
      可以试一试, 甚至不知道是不是都能省略, 如果都能省略用起来最方便 *)
Theorem CNF_f1 : ∀ f, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> exists ! h, Function h /\ dom(h) = dom(f) /\ ran(h) ⊂ R
  /\  h[Φ] = f[Φ]
  /\ ∀ n, n ∈ dom(h) -> (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n].
Proof.
  intros. set (φ := \{\ λ u v, u ∈ ω
    /\ (u ∈ dom(f) -> v = f[u]) /\ (u ∈ (ω ~ dom(f)) -> v = Φ) \}\).
  assert (OnTo φ ω R).
  { assert (Function φ).
    { split; unfold Relation; intros. apply AxiomII in H2 as [_[x[y[]]]].
      eauto. apply AxiomII' in H2 as [_[H2[]]], H3 as [_[_[]]]. admit. }
    assert (dom(φ) = ω).
    { apply AxiomI; split; intros. apply AxiomII in H3 as [_[]].
      apply AxiomII' in H3 as []; tauto. apply AxiomII; split. eauto.
      destruct (classic (z ∈ dom(f))). exists f[z]. apply AxiomII'. split. admit.
      split; auto. split; intros; auto. apply AxiomII in H5 as [_[]].
      apply AxiomII in H6 as []. elim H7; auto.
      exists Φ. apply AxiomII'; split. admit. split; auto. split; intros; auto.
      elim H4; auto. }
    assert (ran(φ) ⊂ R).
    { red; intros. apply AxiomII in H4 as [H4[]]. apply AxiomII' in H5 as [_[H5[]]].
      destruct (classic (x ∈ dom(f))). apply H1. rewrite H6; auto.
      apply (@Property_ran x),Property_Value; auto.
      rewrite H7; auto. admit. }
    red; auto. }
  pose proof H2. apply CNF_f in H3 as [h[[H3[]]]].
  set (h1 := h|(dom(f))). exists h1.
  assert (Function h1). { apply MKT126a. destruct H3; auto. }
  assert (dom(h1) = dom(f)).
  { destruct H3 as [H3[]]. unfold h1. rewrite MKT126b; auto.
    rewrite H8. admit. }
  assert (ran(h1) ⊂ R).
  { red; intros. apply AxiomII in H9 as [_[]]. apply AxiomII in H9 as [_[]].
    pose proof H9. destruct H3 as [H3[]]. apply Property_Fun in H9; auto.
    rewrite H9 in H11. rewrite H9. apply Property_ran in H11; auto. }
  assert (h1[Φ] = f[Φ]).
  { destruct (classic (Φ ∈ dom(f))).
    assert (Φ ∈ dom(φ)). { destruct H2 as [H2[]]. rewrite H11. auto. }
    destruct H2 as [H2[]]. apply Property_Value,AxiomII' in H11 as [_[H11[]]];
    auto. rewrite <-H14; auto. unfold h1. destruct H3 as [H3[]].
    rewrite MKT126c; auto. unfold h1 in H8. rewrite H8. auto.
    pose proof H10. rewrite <-H8 in H11. apply MKT69a in H10,H11.
    rewrite H10,H11; auto. }
  assert (∀ x, x ∈ dom(f) -> h1[x] = h[x]).
  { intros. destruct H3 as [H3[]]. unfold h1. rewrite MKT126c; auto.
    rewrite MKT126b; auto. rewrite H12. (* 序数充满 *) admit. }
  assert (∀ x, x ∈ dom(f) -> φ[x] = f[x]).
  { intros. assert (x ∈ dom(φ)).
    { apply AxiomII; split. eauto. exists f[x]. apply AxiomII'. split. admit.
      split. admit. split; auto. intros. apply MKT4' in H13 as [].
      apply AxiomII in H14 as []. elim H15; auto. }
    destruct H2 as [H2[]]. apply Property_Value,AxiomII' in H13 as [_[_[]]]; auto. }
  assert (∀ n, n ∈ dom(h1) -> (PlusOne n) ∈ dom(h1)
    -> h1[PlusOne n] = h1[n] + f[PlusOne n]).
  { intros. assert (n ∈ (PlusOne n)).
    { apply MKT4. right. apply MKT41; auto. apply (MKT33 (PlusOne n)).
      eauto. red; intros. apply MKT4; auto. }
    assert (n ∈ ω). { (* 利用序数充满性 *) admit. }
    rewrite H11,H11,<-H12; auto; rewrite <-H8; auto. }
  split; auto. intros. destruct H14 as [H14[H15[H16[]]]].
  (* 至此需要重复类似构造φ的过程，将x'现扩展到定义域为ω范围，然后利用H6，
     即可得到扩展后的x'与h(也即扩展后的h1，因为h1是对h的限制)相等，最后就可以证明h1=x' *)
Admitted.


Definition Sum1 f n := ∩ (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
  ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
  -> h[Φ] = f[Φ]
  -> (∀ n, n ∈ dom(h) -> (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
  -> u = h[n] ) \}).

(* 这个引理应该可以省略一个 n ∈ dom(f) 的条件 可以试一试 *)
Lemma Sum1_Lemma1 : ∀ f n, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> n ∈ dom(f) -> (PlusOne n) ∈ dom(f)
  -> Sum1 f (PlusOne n) = Sum1 f n + f[PlusOne n].
Proof.
  intros. pose proof H. apply CNF_f1 in H4 as [h1[[H4[H5[H6[]]]]]]; auto.
  assert (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
    ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
    -> h[Φ] = f[Φ]
    -> (∀ n, n ∈ dom(h) -> (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
    -> u = h[PlusOne n] ) \} = [h1[PlusOne n]]).
  { apply AxiomI; split; intros. apply AxiomII in H10 as [H10[H11[H12[]]]].
    apply H14 in H8; auto. apply MKT41; auto. rewrite <-H8. auto.
    assert (Ensemble z). eauto. apply MKT41 in H10. apply AxiomII. split; auto.
    split; auto. split; auto. split; auto. intros.
    assert (h1 = h). { apply H9; auto. } rewrite <-H17; auto. admit. }
  unfold Sum1 at 1. rewrite H10. assert (Ensemble (h1[PlusOne n])). admit.
  apply MKT44 in H11 as []. rewrite H11,H8; try rewrite H5; auto.
  assert (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
    ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
    -> h[Φ] = f[Φ]
    -> (∀ n, n ∈ dom(h) -> (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
    -> u = h[n] ) \} = [h1[n]]).
  { apply AxiomI; split; intros. apply AxiomII in H13 as [H13[H14[H15[]]]].
    apply H17 in H8; auto. apply MKT41; auto. rewrite <-H8. auto.
    assert (Ensemble z). eauto. apply MKT41 in H13. apply AxiomII. split; auto.
    split; auto. split; auto. split; auto. intros.
    assert (h1 = h). { apply H9; auto. } rewrite <-H20; auto. admit. }
  unfold Sum1. rewrite H13. assert (Ensemble h1[n]). admit.
  apply MKT44 in H14 as []. rewrite H14; auto.
Admitted.

Lemma Sum1_Lemma2 : ∀ f, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> Sum1 f Φ = f[Φ].
Proof.
  intros. pose proof H. apply CNF_f1 in H2 as [h1[[H2[H3[H4[]]]]]]; auto.
  destruct (classic (Φ ∈ dom(f))).
  assert (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
    ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
    -> h[Φ] = f[Φ]
    -> (∀ n, n ∈ dom(h) -> (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
    -> u = h[Φ] ) \} = [h1[Φ]]).
  { apply AxiomI; split; intros. apply AxiomII in H9 as [H9[H10[H11[]]]].
    apply H13 in H6; auto. apply MKT41; auto. rewrite <-H6. auto.
    assert (Ensemble z). eauto. apply MKT41 in H9. apply AxiomII. split; auto.
    split; auto. split; auto. split; auto. intros.
    assert (h1 = h). { apply H7; auto. } rewrite <-H16; auto. admit. }
  unfold Sum1. rewrite H9. assert (Ensemble (h1[Φ])). admit.
  apply MKT44 in H10 as []. rewrite H10,H5; auto.
  assert (\{ λ u, Function f /\ dom(f) ∈ ω /\ ran(f) ⊂ R /\
    ( ∀ h, Function h -> dom(h) = dom(f) -> ran(h) ⊂ R
    -> h[Φ] = f[Φ]
    -> (∀ n, n ∈ dom(h) -> (PlusOne n) ∈ dom(h) -> h[PlusOne n] = h[n] + f[PlusOne n])
    -> u = h[Φ] ) \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H9 as [H9[H10[H11[]]]].
    apply H13 in H6; auto. rewrite <-H3 in H8. apply MKT69a in H8.
    rewrite H6,H8 in H9. elim MKT39; auto. elim (@ MKT16 z); auto. }
  unfold Sum1. rewrite H9. apply MKT69a in H8. rewrite H8. apply MKT24.
Admitted.

Lemma Sum1_Lemma3 : ∀ f n, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> n ∈ dom(f) -> (Sum1 f n) ∈ R.
Proof.
  set (p := fun n => ∀ f, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
    -> n ∈ dom(f) -> (Sum1 f n) ∈ R).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction.
    - unfold p. intros. rewrite Sum1_Lemma2; auto.
      apply H1,(@Property_ran Φ),Property_Value; auto.
    - unfold p; intros. assert (k ∈ dom(f)). admit.
      rewrite Sum1_Lemma1; auto. apply R_Plus_in_R. apply H0; auto.
      apply H3,(@Property_ran (PlusOne k)),Property_Value; auto. }
  intros. apply H; auto. admit.
  (* 其实不需要归纳, 只要把n拆成Φ和PlusOne m两种情况就行 *)
Admitted.

Lemma Sum1_Lemma4 : ∀ f g n, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
  -> Function g -> dom(g) ∈ ω -> ran(g) ⊂ R
  -> n ∈ dom(g) -> (PlusOne n) ∈ dom(f)
  -> (∀ m, m ∈ n \/ m = n -> g[m] = f[PlusOne m])
  -> Sum1 f (PlusOne n) = f[Φ] + Sum1 g n.
Proof.
  set (p := fun n => ∀ f g, Function f -> dom(f) ∈ ω -> ran(f) ⊂ R
    -> Function g -> dom(g) ∈ ω -> ran(g) ⊂ R
    -> n ∈ dom(g) -> (PlusOne n) ∈ dom(f)
    -> (∀ m, m ∈ n \/ m = n -> g[m] = f[PlusOne m])
    -> Sum1 f (PlusOne n) = f[Φ] + Sum1 g n).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction.
    - unfold p. intros. rewrite Sum1_Lemma1; auto.
      rewrite Sum1_Lemma2,Sum1_Lemma2,H7; auto. (* 充满性 *) admit.
    - unfold p; intros.
      assert (k ∈ dom(g) /\ (PlusOne k) ∈ dom(f)) as []. { (* 充满性 *) admit. }
      pose proof (H0 f g H1 H2 H3 H4 H5 H6 H10 H11).
      rewrite Sum1_Lemma1; auto. rewrite H12. rewrite Sum1_Lemma1; auto.
      rewrite (H9 (PlusOne k)); auto. apply Plus_R_Association.
      assert (Φ ∈ dom(f)). (* 通过证明Φ ∈ (PlusOne k) *) admit.
      apply Property_Value,Property_ran in H13; auto. apply Sum1_Lemma3; auto.
      apply H3,(@Property_ran (PlusOne (PlusOne k))),Property_Value; auto.
      intros. apply H9. destruct H13; left; apply MKT4; auto. right.
      apply MKT41; eauto. }
  intros. apply H; auto. admit.
Admitted.
  
  
  
  
Definition MaxinExp α β:= ∪ \{ λ v, α ^ v ≼ β \}.

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
      eapply R_Plus_2 in H6; eauto. destruct H6.
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

Definition Sum f n:= ∩ (\{ λ u, OnTo f ω R /\
  ( ∀ h, OnTo h ω R
  -> h[Φ] = f[Φ]
  -> (∀ n, n ∈ ω -> h[PlusOne n] = h[n] + f[PlusOne n])
  -> u = h[n] ) \}).

Definition f α δ := \{\ λ u v, v = (α ^ u ⋅ δ) \}\.

Theorem CNF: ∀ α β δ, Ordinal_Number α -> Ordinal_Number β-> Ordinal_Number δ
  -> PlusOne Φ ≺ α -> PlusOne Φ ≼ β
  -> ∃ γ n, (∀ k1 k2, k1 ∈ dom(γ) /\ k2 ∈ dom(γ) /\ k1 ≺ k2 -> γ[k2] ≺ γ[k1])
  /\ n ∈ ω /\ β = Sum (f α δ ∘ γ) n.
Proof.
  intros. generalize dependent β.
  eapply (R_Transfinite_Induction
  (fun x => PlusOne Φ ≼ x ->
    ∃ γ n,(∀ k1 k2, k1 ∈ dom(γ) /\ k2 ∈ dom(γ) /\ k1 ≺ k2 -> γ [k2] ≺ γ [k1])
   /\ n ∈ ω /\ x = Sum (f α δ ∘ γ) n)); eauto.
  intro β. intros. destruct H4.
  - (* 1 ≺ β *)
    assert( MaxinExp α β ∈ β ). admit.
    pose proof (CNF_1 α β H H0 H2) as []. left. auto.
    assert( Ordinal_Number (α ^ MaxinExp α β) ).
    { destruct H7. eapply trans_Ord_Num; eauto. rewrite H7. auto. }
    destruct H7.
    + (* α ^ MaxinExp α β ∈ β *)
      New (Mult_R_PrOrder_c (α ^ MaxinExp α β) β H8 H0 H6 H7).
      destruct H9,H9. clear H10. deand.
      assert( Second x ≺ β ). eapply Ord_Num_trans; eauto.
      apply H3 in H12. clear H3.
      destruct H12 as [γ [n]]. deand. rewrite H13 in H11.

      set( γ' := \{\ λ u v, u ∈ ω /\ ((u = Φ /\ v = (MaxinExp α β)) \/
         (u = PlusOne n /\ v = γ[n])) \}\ ).
      exists γ', (PlusOne n).
      split. intros. deand. appA2H H15.
      rdeHex. appoA2H H17. deand. destruct H19. deand.
      rewrite H19 in H16. red in H16. emf. appA2H H14. rdeHex.
      appoA2H H20. deand. destruct H23. deand. subst k1 k2. admit.
      deand. subst. NSym. split. admit.
      eqext. appA2G. intros. appA2H H15. deand. apply CNF_f in H16.
      destruct H16 as [h[H16 _]]. specialize H17 with h. deand.
      apply H17 in H16; auto. clear H17. subst y. admit.

      appA2H H14. apply H15. clear H15. appA2G. split. admit.
      intros. apply H17 in H12. rewrite H12. clear H17. admit. admit.
    + (* α ^ MaxinExp α β = β *)
      set( γ := \{\ λ u v, u = Φ /\ v = (MaxinExp α β) \}\ ).
      exists γ, Φ. split. intros. deand. appA2H H9. appA2H H10. rdeHex.
      appoA2H H12. appoA2H H13. deand; subst; try NSym.
      split. apply MKT135a.
      eqext. appA2G. intros. appA2H H10. deand. admit.
      admit.
  - exists \{\ λ u v, u = Φ /\ v = Φ \}\, Φ. split.
    intros. deand. appA2H H5. appA2H H6. rdeHex. admit.
    split. admit. eqext.
    + appA2G. intros. appA2H H6. deand. (* apply H8 in H6; auto. clear H8.
      subst y. appA2G. intros. appA2H H6. appoA2H H8. rdeHex. appoA2H H9.
      appoA2H H10. deand. subst x. admit. intros. *) admit.
    + appA2H H5. apply H6. clear H6. appA2G. admit.
Admitted.










