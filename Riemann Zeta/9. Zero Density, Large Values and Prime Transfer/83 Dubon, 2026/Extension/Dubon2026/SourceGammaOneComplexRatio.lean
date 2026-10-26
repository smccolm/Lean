import Dubon2026.SourceGammaOneComplexRelation

/-! DUB-17/18 -> finite arithmetic Gamma1 realization -> finite function field.
Multiplying numerator and denominator by the eleventh power of the same
nonzero modular form changes their common weight to a multiple of twelve and
preserves their literal Laurent ratio. The existing norm relation therefore
applies in every weight; no restriction of source weights is made. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Polynomial
open scoped MatrixGroups

theorem exists_complex_j_relation_of_ratio
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hg : g ≠ 0) :
    ∃ (m : ℕ)
      (P : Fin (Nat.card (𝒮ℒ ⧸
        (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) + 1) → Polynomial ℂ),
      (∀ i, (P i).natDegree ≤ m) ∧
      (∃ i, P i ≠ 0) ∧
      ∑ i, Polynomial.aeval (jqModC ℂ) (P i) *
        ((qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) /
          (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ)) ^ (i : ℕ) = 0 := by
  have hk : 0 ≤ k := by
    by_contra h
    exact hg (ModularForm.isZero_of_neg_weight (not_le.mp h) g)
  have hw : (11 : ℕ) * k + k = 12 * (k.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hk]
    ring
  let f' := ((g.pow 11).mul f).mcast hw
  let g' := ((g.pow 11).mul g).mcast hw
  have hf' : qExpansion 1 (f' : ℍ → ℂ) =
      qExpansion 1 (g : ℍ → ℂ) ^ 11 * qExpansion 1 (f : ℍ → ℂ) := by
    simp only [f', ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos (hper hT),
      ModularForm.qExpansion_pow one_pos (hper hT)]
  have hqg' : qExpansion 1 (g' : ℍ → ℂ) =
      qExpansion 1 (g : ℍ → ℂ) ^ 11 * qExpansion 1 (g : ℍ → ℂ) := by
    simp only [g', ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos (hper hT),
      ModularForm.qExpansion_pow one_pos (hper hT)]
  have hqg : qExpansion 1 (g : ℍ → ℂ) ≠ 0 := by
    rwa [Ne, ModularForm.qExpansion_eq_zero_iff one_pos (hper hT)]
  have hg' : g' ≠ 0 := by
    intro hz
    have hqzero : qExpansion 1 (g' : ℍ → ℂ) = 0 := by
      rw [hz, ModularForm.coe_zero, qExpansion_zero]
    rw [hqg'] at hqzero
    exact (mul_ne_zero (pow_ne_zero _ hqg) hqg) hqzero
  obtain ⟨P, hdeg, htop, hsum⟩ := exists_complex_j_relation (hper hT) f' g' hg'
  refine ⟨_, P, hdeg, ⟨_, htop⟩, ?_⟩
  have hqgL : (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ) ≠ 0 := by
    intro hz
    exact hqg (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using hz))
  have hratio :
      (qExpansion 1 (f' : ℍ → ℂ) : LaurentSeries ℂ) /
        (qExpansion 1 (g' : ℍ → ℂ) : LaurentSeries ℂ) =
      (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) /
        (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ) := by
    rw [hf', hqg', PowerSeries.coe_mul, PowerSeries.coe_mul,
      PowerSeries.coe_pow, mul_div_mul_left _ _ (pow_ne_zero 11 hqgL)]
  rwa [hratio] at hsum

end
end Dubon2026.SourceFunctionField.GammaOne
