import Dubon2026.SourceCurveOrderUnitPerturbation

/-! DUB-17/18 -> full original Picard-period Hecke compatibility ->
moving every divisor class away from the cusps -> finite prescribed orders.
Adapted from S_AlgebraicCurve_Place_exists_forall_ord_eq,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing actual place separation, uniformizers and valuation/order identities
supply the foundations. No global approximation hypothesis is introduced.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_indicator (T : Finset (Place K F)) {v : Place K F} {z : F} (hzv : v.ord z < 0)
    (hzT : ∀ w ∈ T, w ≠ v → 0 < w.ord z) (N : ℤ) :
    ∃ e : F, v.adicValuation (e - 1) ≤ WithZero.exp (-N) ∧
      ∀ w ∈ T, w ≠ v → w.adicValuation e ≤ WithZero.exp (-N) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [ord_zero] at hzv
    exact lt_irrefl _ hzv
  obtain ⟨k, hkN, hk1⟩ : ∃ k : ℕ, N ≤ k ∧ (1 : ℤ) ≤ k :=
    ⟨N.toNat + 1, by have := Int.self_le_toNat N; push_cast; omega, by push_cast; omega⟩
  have hy0 : z ^ k ≠ 0 := pow_ne_zero _ hz0
  have hordy : ∀ w : Place K F, w.ord (z ^ k) = k * w.ord z := fun w => by
    rw [← zpow_natCast, ord_zpow]
  have hvy : v.ord (z ^ k) < 0 := by
    rw [hordy]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hk1) hzv
  have hvy' : 1 < v.adicValuation (z ^ k) := (v.one_lt_adicValuation_iff_ord_neg hy0).mpr hvy
  have h1y : v.adicValuation (1 + z ^ k) = v.adicValuation (z ^ k) :=
    Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])
  have h1y0 : 1 + z ^ k ≠ 0 := by
    intro h
    rw [h, map_zero] at h1y
    exact v.adicValuation_ne_zero hy0 h1y.symm
  refine ⟨z ^ k / (1 + z ^ k), ?_, fun w hw hwv => ?_⟩
  · have he : z ^ k / (1 + z ^ k) - 1 = -(1 + z ^ k)⁻¹ := by
      rw [div_sub_one h1y0, show z ^ k - (1 + z ^ k) = -1 by ring, neg_div, one_div]
    rw [he, Valuation.map_neg, map_inv₀, h1y, v.adicValuation_eq_exp_neg_ord hy0,
      ← WithZero.exp_neg, neg_neg, WithZero.exp_le_exp, hordy]
    nlinarith
  · have hwy : 0 < w.ord (z ^ k) := by
      rw [hordy]
      exact mul_pos (by exact_mod_cast hk1) (hzT w hw hwv)
    have hwy' : w.adicValuation (z ^ k) < 1 := (w.adicValuation_lt_one_iff_ord_pos hy0).mpr hwy
    rw [map_div₀, Valuation.map_one_add_of_lt _ hwy', div_one, w.adicValuation_eq_exp_neg_ord hy0,
      WithZero.exp_le_exp, neg_le_neg_iff, hordy]
    have hwz : 0 < w.ord z := hzT w hw hwv
    nlinarith

end
end Dubon2026.SourceCurve.Place
