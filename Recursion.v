Require Export OrdinalNum.Ordinal_Number.

(**********************************************************************)
(* 限制相关推论 *)

Corollary Property_res_dom : ∀ F u, Function F -> Ordinal dom(F) -> u ∈ dom(F)
  -> Ensemble (F | (u)) /\ dom(F | (u)) = u.
Proof.
  intros. New H. eapply (MKT126a F u) in H2; eauto.
  eapply (MKT126b F u) in H; eauto.
  destruct H0 as [_ H0]. New H1. apply H0 in H1. apply MKT30 in H1.
  rewrite H1 in H. appA2H H3. split. apply MKT75; auto. rewrite H. auto. auto.
Qed.

Corollary Property_res : ∀ F u n, Function F -> Ordinal dom(F) -> u ∈ dom(F)
  -> n ∈ u -> (F | (u))[n] = F[n] /\ (F | (u)) | (n) = F | (n).
Proof.
  intros. split.
  - eapply MKT126c; eauto. eapply Property_res_dom in H; eauto.
    destruct H; rewrite H3; auto.
  - unfold Restriction. eqext; deHin; deGin; auto.
    appA2H H4. destruct H5 as [x0 [y0 [H5 [H6 H7]]]].
    subst z. appA2G. exists x0,y0; try repeat (split; auto).
    eapply (MKT111 dom(F) u) in H0; eauto. destruct H0 as [_ H0].
    apply H0 in H2. auto.
Qed.

(**********************************************************************)
(* 关于序数的超限递归定理 *)

(* 定义 A->B的函数F *) (* 郝书p20 MK78-80 *)
Definition OnTo F A B := Function F /\ dom(F) = A /\ ran(F) ⊂ B.

(**********************************************************************)
(* Theorem MKT128a :  ∀ g, ∃ f, Function f /\ Ordinal dom(f) 
  /\ (∀ x, Ordinal_Number x -> f[x] = g[f|(x)]). *)

(* Theorem MKT128b :  ∀ g, ∀ f, Function f /\ Ordinal dom(f) 
  /\ (∀ x, Ordinal_Number x -> f [x] = g[f|(x)]) 
  -> ∀ h, Function h /\ Ordinal dom(h) 
  /\ (∀ x, Ordinal_Number x -> h [x] = g[h|(x)]) -> f = h. *)

(**********************************************************************)
(* 超限递归 *)

Theorem Recursion : ∀ G, OnTo G μ μ -> exists ! F, OnTo F R μ /\
  (∀ a, Ordinal_Number a -> F[a] = G[F | (a)]).
Proof.
  intros. destruct H,H0. New MKT128a. specialize H2 with G.
  destruct H2 as [F H2]. exists F. split.
  - split. red. destruct H2,H3.
    split. apply H2. split.
    + eqext. appA2G. eapply MKT111; eauto.
      pose proof H5 as H5'. appA2H H5.
      eapply (@ Th110ano z dom(F)) in H6; eauto. destruct H6; eauto.
      pose proof H4 z H5'.
      New H2. eapply (frebig F z) in H2; eauto. rewrite H2 in H7.
      TF ( z ∈ dom(F) ); auto. apply MKT69a in H9. rewrite H9 in H7.
      symmetry in H7. apply MKT69a' in H7. rewrite H0 in H7.
      pose proof MKT33 z dom(F) H5 H6.
      eapply MKT75 in H10; eauto. apply MKT19 in H10; contradiction.
    + auto.
    + eapply H2.
  - intros. New MKT128b. specialize H4 with (g:=G)(f:=F)(h:=x').
    destruct H4. auto. destruct H3,H3,H5. split; auto.
    New MKT113a. rewrite H5. auto. auto.
Qed.


(**********************************************************************)
(* 超限递归 ω *)

Module Recursion_ω.

Definition G G1 G2 := \{\ λ u v, u ∈ μ /\
  ( ( dom(u) ∉ ω /\ v = Φ )
 \/ ( dom(u) ∈ ω /\
    ( ( dom(u) = Φ /\ v = G1[Φ] )
   \/ ( dom(u) ≠ Φ /\ v = G2[u[∪dom(u)]] ) ) ) ) \}\.

Fact Fun_G : ∀ G1 G2, OnTo G1 μ μ -> OnTo G2 μ μ
  -> OnTo (G G1 G2) μ μ.
Proof.
  repeat split. eapply PisRel.
  - intros. appoA2H H1. destruct H3. appoA2H H2. destruct H5 as [_ H5].
    destruct H4,H5; try repeat (destruct H4,H5; subst; auto; contradiction).
    destruct H4,H5; try repeat (destruct H6,H7; subst; auto).
  - eqext. eapply MKT19; eauto. TF ( dom( z ) = Φ ).
    + appA2G. exists G1[Φ]. appA2G. apply MKT49a; auto.
      destruct H,H3. New EnEm. apply MKT19 in H5. rewrite <- H3 in H5.
      apply MKT69b in H5. auto.
      exists z,G1[Φ]. try repeat split; auto.
      TF( (dom(z)) ∈ ω ). right; split; auto. rewrite H2 in H3.
      New MKT135a; contradiction.
    + TF( (dom(z)) ∈ ω ). appA2G. exists G2[z[∪dom(z)]].
      assert( Ensemble G2[z[∪dom(z)]] ).
      { New H3. appA2H H3. destruct H5,H6.
        specialize H7 with dom(z); eauto.
        pose proof (MKT26a dom(z)). eapply H7 in H8; eauto.
        destruct H8 as [z0 H8]. assert( dom(z) ∈ R ). appA2G. New H9.
        eapply (@ MKT133 z0 dom(z)) in H9; eauto. rewrite H9.
        assert( z0 ∈ R ). destruct H8. eapply trans_Ord_Num; eauto.
        rewrite MKT124; auto.
        assert( z0 ∈ dom(z) ). rewrite H9; appA2G.
        apply MKT69b in H12. destruct H0,H13. rewrite <- H13 in H12.
        apply MKT69b in H12; auto. }
      appA2G. exists z,G2[z[∪dom(z)]]. try repeat split; auto.
      appA2G. exists Φ. appoA2G.
  - red. intros. eapply MKT19; eauto.
Qed.

Fact G_G1 : ∀ G1 G2, OnTo G1 μ μ -> OnTo G2 μ μ
  -> ∀u, u ∈ μ -> dom(u) = Φ -> (G G1 G2)[u] = G1[Φ] .
Proof.
  intros G1 G2 F_G1 F_G2.
  New F_G1. eapply (Fun_G G1 G2) in H; eauto.
  intros. eqext. appA2H H2. apply H3.
  assert( Ensemble G1[Φ] ).
  { destruct F_G1,H5. New EnEm. apply MKT19 in H7.
    rewrite <- H5 in H7. apply MKT69b in H7. auto. }
  appA2G. appoA2G. split; auto. right.
  split; subst; eauto. rewrite H1. apply MKT135a.
  appA2G. intros. appA2H H3. appoA2H H4. destruct H5.
  destruct H6,H6. rewrite H1 in H6. New MKT135a; contradiction.
  destruct H7,H7. subst; auto. contradiction.
Qed.

Fact G_G2 : ∀ G1 G2, OnTo G1 μ μ -> OnTo G2 μ μ
  -> ∀u, u ∈ μ -> dom(u) ∈ ω -> dom(u) ≠ Φ
  -> (G G1 G2)[u] = G2[u[∪dom(u)]] .
Proof.
  intros G1 G2 F_G1 F_G2.
  New F_G1. eapply (Fun_G G1 G2) in H; eauto. intros.
  eqext.
  + appA2H H3. apply H4. clear H4.
    assert( Ensemble G2[u[∪dom(u)]] ).
    { New H1. appA2H H1. destruct H5,H6.
      specialize H7 with dom(u); eauto.
      pose proof (MKT26a dom(u)). eapply H7 in H8; eauto.
      destruct H8 as [u0 H8]. assert( dom(u) ∈ R ). appA2G.
      New H9. eapply (@ MKT133 u0 dom(u)) in H9; eauto. rewrite H9.
      assert( u0 ∈ R ). destruct H8. eapply trans_Ord_Num; eauto.
      rewrite MKT124; auto. assert( u0 ∈ dom(u) ). rewrite H9; appA2G.
      apply MKT69b in H12. destruct F_G2,H14. rewrite <- H14 in H12.
      apply MKT69b in H12; auto. }
    appA2G. appoA2G. split; auto.
  + appA2G. intros. appA2H H4. appoA2H H5. destruct H6 as [_ H6].
    destruct H6,H6. contradiction.
    destruct H7,H7; try contradiction; subst; auto.
Qed.

Theorem Recursion_ω : ∀ G1 G2, OnTo G1 μ μ -> OnTo G2 μ μ
  -> exists ! F, OnTo F ω μ
  /\ F[Φ] = G1[Φ]
  /\ ∀n, n ∈ ω -> F[PlusOne n] = G2[F[n]].
Proof.
  intros G1 G2 F_G1 F_G2. New F_G1. eapply (Fun_G G1 G2) in H; eauto.
  eapply Recursion in H.
  assert( exists ! F', OnTo F' ω μ
    /\ (∀ a, a ∈ ω -> F'[a] = (G G1 G2)[F' | (a)]) ).
  { destruct H as [F [H H0]]. exists (F | (ω)). split.
    - clear H0. destruct H. destruct H,H1.
      New MKT138. rewrite <- H1 in H3. New MKT113a.
      rewrite <- H1 in H4. pose proof H as H'.
      eapply (Property_res_dom F ω) in H; eauto. destruct H. split.
      split; auto. apply MKT126a; auto.
      intros. eapply Property_res in H'; eauto. destruct H'.
      rewrite H7,H8. rewrite H1 in H3,H4. destruct H4 as [_ H4].
      eapply H4 in H3. apply H3 in H6. apply H0 in H6. auto.
    - intros. destruct H,H1,H,H1,H4,H5. pose proof H as H'.
      eapply (MKT126a F ω) in H. New H'. eapply (MKT126b F ω) in H8.
      rewrite H4 in H8. New MKT113a. New H9. destruct H9 as [_ H9].
      New MKT138. New H11. apply H9 in H11. apply MKT30 in H11.
      rewrite H11 in H8. clear H11. appA2H H12. clear H11.
      assert( x' ⊂ F | (ω) \/ F | (ω) ⊂ x' ).
      { eapply (@ MKT127 (F | (ω)) x' (G G1 G2)); eauto.
        rewrite H8. auto. intros. eapply Property_res in H'; eauto.
        destruct H'. rewrite H8 in H11,H13,H14. rewrite H13,H14.
        New MKT138. apply H9 in H15. apply H15 in H11.
        apply H2 in H11; auto. rewrite H4; auto.
        rewrite H8,H4; apply MKT138; auto. rewrite H5; auto.
        intros. rewrite H5 in H11. eapply H3; eauto. }
      destruct H11.
      + apply MKT71; auto; intros. TF( x ∈ dom(x') ).
        * symmetry. apply subval; auto.
        * rewrite (@ MKT69a x); auto. rewrite MKT69a; auto.
          rewrite H8. rewrite H5 in H13. auto.
      + apply MKT71; auto; intros. TF( x ∈ dom(F | (ω)) ).
        * apply subval; auto.
        * rewrite (@MKT69a x); auto. rewrite MKT69a; auto.
          rewrite H5. rewrite H8 in H13. auto. }
  clear H. destruct H0 as [F [H H0]]. exists F. destruct H.
  pose proof H as H'. split; intros.
  - clear H0. split; auto. destruct H,H0. split. New MKT135a.
    apply H1 in H3. rewrite H3. New MKT135a. rewrite <- H0 in H4.
    eapply (Property_res_dom F Φ) in H; eauto. destruct H.
    eapply G_G1; eauto. rewrite H0. New MKT138. appA2H H5; auto.
    intros. pose proof H3 as H_n. apply MKT134 in H3.
    pose proof H3 as H_n'. New H.
    eapply (Property_res_dom F (PlusOne n)) in H; try rewrite H0; eauto.
    destruct H. apply H1 in H_n'. rewrite H_n'.
    assert( H'': ∪( dom(F | (PlusOne n)) ) = ∪(PlusOne n) ).
    rewrite H5; auto.
    assert( F[n] = (F | (PlusOne n))[∪(PlusOne n)] ).
    { New MKT113a. New H_n. New MKT138. eapply trans_Ord_Num in H7; eauto.
      apply MKT124 in H7. rewrite H7. symmetry.
      eapply MKT126c; eauto. rewrite H5; appA2G. }
    rewrite <- H'' in H6. rewrite H6.
    eapply (G_G2 G1 G2); eauto; try repeat rewrite H5; auto.
    eapply MKT135b in H_n. red. auto.
  - apply H0; clear H H' H0 H1. destruct H2. split; auto.
    intros. destruct H,H0,H2. pose proof H as H'.
    eapply Property_res_dom in H'; try rewrite H2; eauto.
    destruct H'.
    TF( a = Φ ). subst a. rewrite H0. symmetry. eapply G_G1; eauto.
    pose proof H1 as H'. appA2H H1. destruct H8 as [_ [_ H8]].
    specialize H8 with a. pose proof (MKT26a a); eauto.
    eapply H8 in H9; eauto. clear H8. destruct H9 as [a0].
    assert( a ∈ R ). New MKT138. eapply trans_Ord_Num; eauto.
    assert( a = PlusOne a0 ). eapply MKT133; eauto.
    subst a. destruct H8 as [H8 _]. pose proof H' as H_a.
    appA2H H'. assert( a0 ∈ ω ). appA2G. eapply MKT132; eauto.
    apply H3 in H12; clear H3. rewrite H12. symmetry.
    assert( H': ∪( dom(x' | (PlusOne a0)) ) = ∪(PlusOne a0) ).
    rewrite H6; auto.
    assert( x'[a0] = (x' | (PlusOne a0))[∪(PlusOne a0)] ).
    { New MKT113a. New H8. eapply trans_Ord_Num in H8; eauto.
      apply MKT124 in H8. rewrite H8. symmetry. rewrite <- H6 in H13.
      eapply MKT126c; eauto. }
    rewrite <- H' in H3. rewrite H3. eapply G_G2; eauto.
    rewrite H6; auto. rewrite H6. auto.
Qed.

End Recursion_ω.

(**********************************************************************)
(* 超限递归 R *)

Module Recursion_R.

Definition G G1 G2 G3 := \{\ λ u v, u ∈ μ /\
  ( ( dom(u) ∉ R /\ v = Φ )
  \/ ( dom(u) ∈ R /\ ( ( dom(u) = Φ /\ v = G1[Φ] )
      \/ ( Suc_Ord dom(u) /\ v = G2[u[∪dom(u)]] )
      \/ ( Lim_Ord dom(u) /\ dom(u) ≠ Φ /\ v = G3[u] ) ) ) ) \}\.

Fact Fun_G : ∀ G1 G2 G3, OnTo G1 μ μ -> OnTo G2 μ μ -> OnTo G3 μ μ
  -> OnTo (G G1 G2 G3) μ μ.
Proof.
  repeat split. eapply PisRel.
  - intros. appoA2H H2. destruct H4. appoA2H H3. destruct H6.
    TF ( dom(x) ∈ R ).
    + destruct H5,H5; try contradiction.
      destruct H7,H7; try contradiction.
      apply OrdNum_classic in H5. destruct H5.
      * New Φ_is_Lim_Ord. destruct H9,H9.
        rewrite <- H9 in H11; Suc_not_Lim.
        destruct H10,H10. rewrite <- H10 in H11; Suc_not_Lim.
        destruct H9,H10; subst; auto.
        destruct H10; Suc_not_Lim. destruct H9; Suc_not_Lim.
      * destruct H9,H9,H10,H10; try repeat (destruct H9; Suc_not_Lim);
        try repeat (destruct H10; Suc_not_Lim). subst; auto.
        destruct H10 as [_ [H10 _]]; contradiction.
        destruct H9 as [_ [H9 _]]; contradiction.
        destruct H9 as [_ [_ H9]]; destruct H10 as [_ [_ H10]].
        subst; auto.
    + destruct H5. destruct H7. destruct H5,H7. rewrite H10. auto.
      destruct H7. contradiction. destruct H5. contradiction.
  - eqext. eapply MKT19; eauto. TF ( dom(z) ∈ R ).
    + pose proof H3 as H3'. apply OrdNum_classic in H3. destruct H3.
      appA2G. exists G2[z[∪dom(z)]].
      assert( Ensemble G2[z[∪dom(z)]] ).
      { New H3. red in H3. destruct H3 as [z0 [H3 H5]].
        rewrite H5. New H3. eapply MKT124 in H3; eauto. rewrite H3.
        assert( z0 ∈ dom(z) ). rewrite H5; appA2G.
        apply MKT69b in H7. destruct H0,H8. rewrite <- H8 in H7.
        apply MKT69b in H7. auto. }
      appA2G. exists z,G2[z[∪dom(z)]]. try repeat split; auto.
      right. split; auto.
      TF( dom(z) = Φ ).
      appA2G. exists G1[Φ]. assert( Ensemble G1[Φ] ).
      { destruct H,H5. New EnEm. apply MKT19 in H7.
        rewrite <- H5 in H7. apply MKT69b in H7. auto. }
      appA2G. exists z,G1[Φ]. try repeat split; auto.
      appA2G. exists G3[z]. appA2G. apply MKT49a.
      auto. destruct H1,H5. rewrite <- H5 in H2.
      apply MKT69b in H2. auto. exists z,G3[z]. try repeat split; auto.
      right. split; auto.
    + appA2G. exists Φ. appA2G.
      exists z,Φ. try repeat split; auto.
  - red. intros. eapply MKT19; eauto.
Qed.

Fact G_G1 : ∀ G1 G2 G3, OnTo G1 μ μ -> OnTo G2 μ μ -> OnTo G3 μ μ
  -> ∀ u, Ensemble u -> dom(u) = Φ -> (G G1 G2 G3)[u] = G1[Φ] .
Proof.
  intros G1 G2 G3 F_G1 F_G2 F_G3.
  New F_G1. eapply (Fun_G G1 G2 G3) in H; eauto.
  intros. eqext. appA2H H2. apply H3.
  assert( Ensemble G1[Φ] ).
  { destruct F_G1,H5. New EnEm. apply MKT19 in H7.
    rewrite <- H5 in H7. apply MKT69b in H7. auto. }
  appA2G. appoA2G. split; auto. right. split; auto.
  New Φ_is_Ord. rewrite <- H1 in H5. appA2H H5; appA2G; auto.
  appA2G. intros. appA2H H3. appoA2H H4. destruct H5.
  destruct H6,H6. rewrite H1 in H6. New Φ_is_Ord. contradiction.
  destruct H7,H7. subst y. appA2G. intros. appA2H H8.
  destruct F_G1. apply Property_Fun in H9; eauto. subst; auto.
  New Φ_is_Lim_Ord. destruct H7. rewrite <- H1 in H8. Suc_not_Lim.
  destruct H7 as [_ [H7 _]]. contradiction.
Qed.

Fact G_G2 : ∀ G1 G2 G3, OnTo G1 μ μ -> OnTo G2 μ μ -> OnTo G3 μ μ
  -> ∀ u, Ensemble u -> Suc_Ord dom(u)
  -> (G G1 G2 G3)[u] = G2[u[∪dom(u)]] .
Proof.
  intros G1 G2 G3 F_G1 F_G2 F_G3.
  New F_G1. eapply (Fun_G G1 G2 G3) in H; eauto. intros. eqext.
  + appA2H H2. apply H3. clear H3.
    assert( Ensemble G2[u[∪dom(u)]] ).
    { New H1. red in H1. destruct H1 as [u0 [H1 H4]].
      rewrite H4. New H1. eapply MKT124 in H1; eauto. rewrite H1.
      assert( u0 ∈ dom(u) ). rewrite H4; appA2G.
      apply MKT69b in H6. destruct F_G2,H8. rewrite <- H8 in H6.
      apply MKT69b in H6. auto. }
    appA2G. appoA2G. split; auto. right. split.
    apply Suc_is_Ord in H1; auto. right. left. split; auto.
  + appA2G. intros. appA2H H3. appoA2H H4. destruct H5 as [_ H5].
    destruct H5,H5. apply Suc_is_Ord in H1; contradiction.
    destruct H6,H6. rewrite H6 in H1. New Φ_is_Ord.
    New Φ_is_Lim_Ord. Suc_not_Lim.
    destruct H6; subst; auto.
    destruct H6. Suc_not_Lim.
Qed.

Fact G_G3 : ∀ G1 G2 G3, OnTo G1 μ μ -> OnTo G2 μ μ -> OnTo G3 μ μ
  -> ∀ u, Ensemble u -> Lim_Ord dom(u) -> dom(u) ≠ Φ
  -> (G G1 G2 G3)[u] = G3[u] .
Proof.
  intros G1 G2 G3 F_G1 F_G2 F_G3.
  New F_G1. eapply (Fun_G G1 G2 G3) in H; eauto. intros. eqext.
  - appA2H H3. apply H4.
    assert( Ensemble G3[u] ).
    { destruct F_G3,H6. apply MKT19 in H0. rewrite <- H6 in H0.
      apply MKT69b in H0; auto. }
    appA2G. appoA2G. split; auto. right. split. destruct H1; auto.
    right. right. split; auto.
  - appA2G. intros. appA2H H4. appoA2H H5. destruct H6.
    destruct H7,H7. destruct H1; contradiction.
    destruct H8,H8. contradiction. destruct H8. Suc_not_Lim.
    destruct H8 as [_ [_ H8]]. subst y. auto.
Qed.

(* 序数递归定理 *)
Theorem Recursion_R : ∀ G1 G2 G3, OnTo G1 μ μ -> OnTo G2 μ μ -> OnTo G3 μ μ
  -> exists ! F, OnTo F R μ
  /\ F[Φ] = G1[Φ]
  /\ ∀n, Ordinal_Number n -> F[PlusOne n] = G2[F[n]]
  /\ ∀n, Ordinal_Number n -> Lim_Ord n -> n ≠ Φ -> F[n] = G3[F | (n)].
Proof.
  New Recursion. intros G1 G2 G3 F_G1 F_G2 F_G3.
  New F_G1. eapply (Fun_G G1 G2 G3) in H0; eauto.
  apply H in H0. destruct H0 as [F H0]. exists F. destruct H0. split.
  (* 存在性 *)
  - clear H1. destruct H0. split; eauto.
    (* dom(u) = Φ *)
    split. New Φ_is_Ord. apply H1 in H2. rewrite H2. destruct H0,H3.
    assert( F | (Φ) = Φ ). eqE. appA2H H5. destruct H6.
    appA2H H7. repeat destruct H8. destruct H9. emf.
    eapply (G_G1); try rewrite H5; eauto.
    eqE. appA2H H6. destruct H7. emf. intros; split.
    (* Suc_Ord dom(u) *)
    + pose proof H2 as H2'. apply Lem123 in H2. apply H1 in H2.
      rewrite H2. clear H1 H2. New H0. pose proof H2' as H''.
      apply Lem123 in H2'. destruct H0,H2. pose proof H0 as H'.
      eapply (Property_res_dom F (PlusOne n)) in H0; try rewrite H2; eauto.
      destruct H0. assert( H''': ∪( dom(F | (PlusOne n)) ) = ∪(PlusOne n) ).
      rewrite H4; auto.
      assert( F[n] = (F | (PlusOne n))[∪(PlusOne n)] ).
      { pose proof H'' as H2''. apply MKT124 in H2''. rewrite H2''.
        symmetry. eapply MKT126c; eauto. rewrite H4; appA2G. }
      rewrite <- H''' in H5. rewrite H5. eapply G_G2; eauto.
      rewrite H4. unfold Suc_Ord. exists n. split; auto.
    (* Lim_Ord dom(u) *)
    + intros. apply H1 in H3. rewrite H3. New H4. destruct H4,H0,H8.
      New H0. eapply (Property_res_dom F n0) in H0; try rewrite H8; eauto.
      destruct H0. eapply (G_G3 G1 G2 G3) in F_G1; try rewrite H11; eauto.
  (* 唯一性 *)
  - intros. specialize H1 with x'. destruct H2,H3. apply H1. clear H1.
    split; auto. intros. New H1.
    apply OrdNum_classic in H5. destruct H5.
    (* Suc_Ord *)
    destruct H5,H5. subst a. pose proof H5 as H2'. apply H4 in H5.
    destruct H5 as [H5 _]. rewrite H5. symmetry. clear H4 H5.
    New H2. pose proof H2' as H''. apply Lem123 in H2'. destruct H2,H5.
    eapply (Property_res_dom x' (PlusOne x)) in H2; try rewrite H5; eauto.
    destruct H2. assert( H''': ∪( dom(x' | (PlusOne x)) ) = ∪(PlusOne x) ).
    rewrite H7; auto.
    assert( x'[x] = (x' | (PlusOne x))[∪(PlusOne x)] ).
    { pose proof H'' as H2''. apply MKT124 in H2''. rewrite H2''.
      symmetry. destruct H4. eapply MKT126c; eauto.
      rewrite H7; appA2G. }
    rewrite <- H''' in H8. rewrite H8.
    New F_G2. eapply (G_G2 G1 G2 G3) in H9; eauto. red.
    exists x. split; auto.
    (* Lim_Ord *)
    TF ( a = Φ ).
  * subst a. rewrite H3. symmetry. New Φ_is_Ord. destruct H2,H7.
    eapply (Property_res_dom x' Φ) in H2; try rewrite H7; eauto.
    destruct H2. New F_G1. eapply (G_G1 G1 G2 G3) in F_G1; eauto.
  * symmetry. pose proof H1 as H2'. apply H4 in H1.
    destruct H1 as [_ H1]. apply H1 in H2'; auto.
    rewrite H2'. clear H H1 H2' H4.
    New H5. destruct H2,H2,H5.
    eapply (Property_res_dom x' a) in H1; try rewrite H2; eauto.
    destruct H1.
    eapply (G_G3 G1 G2 G3) in F_G3; try rewrite H8; eauto.
Qed.
End Recursion_R.
