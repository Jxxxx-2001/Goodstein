Require Export OrdinalNum.Cantor_Normal_Form1.

Notation One := (PlusOne Φ).
Notation Two := (PlusOne (PlusOne Φ)).

Lemma uni_m : ∀ m n, n ∈ ω -> Two ≼ n -> n ≼ m
  -> let t := (MaxinExp n m) in One ≼ t
  /\ exists! m_p, m_p ∈ (ω × ω)
  /\ let k := (First m_p) in let b := (Second m_p) in
     m = n ^ t ⋅ k + b /\ k ≺ n /\ b ≺ n ^ t.
Proof.
  intros. split. admit. pose proof (CNF_1 n m). pose proof Mult_R_PrOrder_c.
Admitted.