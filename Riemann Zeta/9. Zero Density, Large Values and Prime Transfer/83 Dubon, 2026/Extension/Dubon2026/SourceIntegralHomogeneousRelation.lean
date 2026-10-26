import Dubon2026.SourceInverseJLevelOneIntegral

/-! DUB-17/18 -> actual Gamma1 differential comparison -> cusp integral
bound -> normalize the existing modular norm relation over the integral
closure. This exact homogeneous relation is consumed by the inverse-j
modular quotient theorem; it assumes neither the desired integrality nor
a Galois realization.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le. -/
namespace Dubon2026.SourceFunctionField.InverseJIntegral
noncomputable section

theorem isIntegral_div_of_relation {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (d : ℕ) (β : ℕ → L) (g e : L) (he : e ≠ 0)
    (hsum : ∑ m ∈ Finset.range (d + 1), β m * g ^ m * e ^ (d - m) = 0)
    (hlead : β d = (-e) ^ d)
    (hint : ∀ m ∈ Finset.range d, IsIntegral R (β m / e ^ d)) :
    IsIntegral R (g / e) := by
  have hed : (-e) ^ d ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr he)
  have hsign : ∀ b : L, b / (-e) ^ d = (-1) ^ d * (b / e ^ d) := fun b ↦ by
    rw [neg_pow, div_mul_eq_div_div_swap, div_eq_mul_inv (b / e ^ d), ← inv_pow, inv_neg_one,
      mul_comm]
  have hint' : ∀ m ∈ Finset.range d, β m / (-e) ^ d ∈ integralClosure R L := fun m hm ↦ by
    rw [mem_integralClosure_iff, hsign]
    exact ((isIntegral_one.neg).pow d).mul (hint m hm)
  classical
  let c : ℕ → integralClosure R L := fun m ↦
    if hm : m ∈ Finset.range d then ⟨β m / (-e) ^ d, hint' m hm⟩ else 0
  let p : Polynomial (integralClosure R L) :=
    ∑ m ∈ Finset.range d, Polynomial.C (c m) * Polynomial.X ^ m
  have hp : p.degree < d := by
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun m hm ↦ ?_
    refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hm)
  have hc : ∀ m ∈ Finset.range d,
      (algebraMap (integralClosure R L) L (c m) : L) = β m / (-e) ^ d := by
    intro m hm
    simp only [c, dif_pos hm]
    rfl
  have key : ∀ m ∈ Finset.range (d + 1),
      β m / (-e) ^ d * (g / e) ^ m = (β m * g ^ m * e ^ (d - m)) / ((-e) ^ d * e ^ d) := by
    intro m hm
    have hmd : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hmd
    rw [hj, Nat.add_sub_cancel_left, div_pow, div_mul_div_comm, pow_add e m j,
      ← mul_assoc ((-e) ^ (m + j)), mul_div_mul_right _ _ (pow_ne_zero j he)]
  have hA : IsIntegral (integralClosure R L) (g / e) := by
    refine ⟨Polynomial.X ^ d + p, Polynomial.monic_X_pow_add hp, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
    rw [Finset.sum_congr rfl fun m hm ↦ by rw [hc m hm]]
    calc (g / e) ^ d + ∑ m ∈ Finset.range d, β m / (-e) ^ d * (g / e) ^ m
        = ∑ m ∈ Finset.range (d + 1), β m / (-e) ^ d * (g / e) ^ m := by
          rw [Finset.sum_range_succ, hlead, div_self hed, one_mul, add_comm]
      _ = ∑ m ∈ Finset.range (d + 1), (β m * g ^ m * e ^ (d - m)) / ((-e) ^ d * e ^ d) :=
          Finset.sum_congr rfl key
      _ = 0 := by rw [← Finset.sum_div, hsum, zero_div]
  exact isIntegral_trans (g / e) hA

end
end Dubon2026.SourceFunctionField.InverseJIntegral
