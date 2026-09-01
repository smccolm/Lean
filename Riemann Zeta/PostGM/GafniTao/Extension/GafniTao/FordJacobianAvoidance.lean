import GafniTao.FordPowerResidueFiber

/-!
# Ford Lemma 3.2: Jacobian prime avoidance

This file isolates the exact integral quantity used before Ford equation
(3.3).  Its size bound retains the source exponent
`d + (k-d)(k-d-1)`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordVandermondeNatAbs {n P : ℕ} (z : FordBox n P) : ℕ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
    Int.natAbs ((fordBoxValue z j : ℤ) - (fordBoxValue z i : ℤ))

def FordTuplePairwiseDistinct {n P : ℕ} (z : FordBox n P) : Prop :=
  Function.Injective z

theorem int_natAbs_natCast_sub_lt
    {a b P : ℕ} (ha : 0 < a) (hb : 0 < b)
    (haP : a ≤ P) (hbP : b ≤ P) (hab : a ≠ b) :
    Int.natAbs ((a : ℤ) - (b : ℤ)) < P := by
  by_cases hle : a ≤ b
  · have hlt : a < b := lt_of_le_of_ne hle hab
    rw [Int.natAbs_of_nonpos (by exact_mod_cast hle)]
    norm_cast
    omega
  · have hlt : b < a := Nat.lt_of_not_ge hle
    rw [Int.natAbs_of_nonneg (by exact_mod_cast hlt.le)]
    norm_cast
    omega

theorem ford_vandermonde_factor_lt
    {n P : ℕ} (z : FordBox n P) (hz : FordTuplePairwiseDistinct z)
    {i j : Fin n} (hij : i < j) :
    Int.natAbs ((fordBoxValue z j : ℤ) - (fordBoxValue z i : ℤ)) < P := by
  apply int_natAbs_natCast_sub_lt
  · exact (fordBoxValue_mem_Icc z j).1
  · exact (fordBoxValue_mem_Icc z i).1
  · exact (fordBoxValue_mem_Icc z j).2
  · exact (fordBoxValue_mem_Icc z i).2
  · intro h
    apply hz (Fin.ext ?_)
    simpa [fordBoxValue] using h

theorem ford_sum_card_Ioi (n : ℕ) :
    (∑ i : Fin n, (Finset.Ioi i).card) = n * (n - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  simp_rw [Fin.card_Ioi]
  rw [Finset.sum_range_reflect (fun i => i) n, Finset.sum_range_id]

theorem ford_vandermondeNatAbs_le
    {n P : ℕ} (z : FordBox n P) (hz : FordTuplePairwiseDistinct z) :
    fordVandermondeNatAbs z ≤ P ^ (n * (n - 1) / 2) := by
  unfold fordVandermondeNatAbs
  calc
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        Int.natAbs ((fordBoxValue z j : ℤ) - (fordBoxValue z i : ℤ))) ≤
        ∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, P := by
      apply Finset.prod_le_prod
      intro i hi
      apply Finset.prod_le_prod
      intro j hj
      exact (ford_vandermonde_factor_lt z hz (Finset.mem_Ioi.mp hj)).le
    _ = P ^ (n * (n - 1) / 2) := by
      simp only [Finset.prod_const, nsmul_eq_mul]
      rw [← Finset.prod_pow_eq_pow_sum, ford_sum_card_Ioi]

def fordJacobianAvoidanceNat
    {k d T P : ℕ} (z w : FordBox (k - d) P) : ℕ :=
  T * fordVandermondeNatAbs z * fordVandermondeNatAbs w

theorem fordJacobianAvoidanceNat_pos
    {k d T P : ℕ} (hT : 0 < T)
    (z w : FordBox (k - d) P)
    (hz : FordTuplePairwiseDistinct z)
    (hw : FordTuplePairwiseDistinct w) :
    0 < fordJacobianAvoidanceNat (T := T) z w := by
  unfold fordJacobianAvoidanceNat fordVandermondeNatAbs
  apply mul_pos (mul_pos hT ?_) ?_
  · apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    rw [Int.natAbs_pos]
    intro h
    apply hz (Fin.ext ?_)
    exact_mod_cast sub_eq_zero.mp h
  · apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    rw [Int.natAbs_pos]
    intro h
    apply hw (Fin.ext ?_)
    exact_mod_cast sub_eq_zero.mp h

theorem fordJacobianAvoidanceNat_le_source_power
    {k d T P : ℕ} (hT : T ≤ P ^ d)
    (z w : FordBox (k - d) P)
    (hz : FordTuplePairwiseDistinct z)
    (hw : FordTuplePairwiseDistinct w) :
    fordJacobianAvoidanceNat (T := T) z w ≤
      P ^ (d + (k - d) * (k - d - 1)) := by
  let n := k - d
  have hzle := ford_vandermondeNatAbs_le z hz
  have hwle := ford_vandermondeNatAbs_le w hw
  unfold fordJacobianAvoidanceNat
  calc
    T * fordVandermondeNatAbs z * fordVandermondeNatAbs w ≤
        P ^ d * P ^ (n * (n - 1) / 2) * P ^ (n * (n - 1) / 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul hT hzle) hwle
    _ = P ^ (d + n * (n - 1)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      have heven : 2 ∣ n * (n - 1) := n.even_mul_pred_self.two_dvd
      omega
    _ = P ^ (d + (k - d) * (k - d - 1)) := rfl

theorem exists_ford_prime_avoiding_jacobian
    {k d T P : ℕ} {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (z w : FordBox (k - d) P)
    (hz : FordTuplePairwiseDistinct z)
    (hw : FordTuplePairwiseDistinct w) :
    ∃ p ∈ S, ¬p ∣ fordJacobianAvoidanceNat (T := T) z w := by
  apply exists_prime_not_dvd_of_lt_prod hprime
    (fordJacobianAvoidanceNat_pos hTpos z w hz hw)
  exact (fordJacobianAvoidanceNat_le_source_power hT z w hz hw).trans_lt hsource

#print axioms int_natAbs_natCast_sub_lt
#print axioms ford_sum_card_Ioi
#print axioms ford_vandermondeNatAbs_le
#print axioms fordJacobianAvoidanceNat_le_source_power
#print axioms exists_ford_prime_avoiding_jacobian

end

end GafniTao
