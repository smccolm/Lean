import Dubon2026.SourceGammaOneNormalizedCuspRatios
import Dubon2026.SourceGammaOneModularRatios
import Dubon2026.ModularDegeneracy

/-! DUB-17/18 -> actual Gamma1 global charts -> analytic-place orbits.
The original integral-ratio field contains every actual complex modular
ratio. Multiply by the same eleventh denominator power and discriminant
to reach the already proved normalized cusp case. The actual field,
Fourier series and all source weights are preserved. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem modular_ratio_mem (N : ℕ) [NeZero N] {k : ℤ}
    (f g : ModularForm (Gamma1 N) k) (hg : g ≠ 0) :
    (qExpansion 1 f : LaurentSeries ℂ) / (qExpansion 1 g : LaurentSeries ℂ) ∈
      functionFieldOver (Gamma1 N) ℂ := by
  have hT : ModularGroup.T ∈ Gamma1 N := by simp [Gamma1_mem, ModularGroup.T]
  have hk : 0 ≤ k := by
    by_contra h
    exact hg (ModularForm.isZero_of_neg_weight (not_le.mp h) g)
  let m := k.toNat + 1
  have hw : 12 + ((11 : ℕ) * k + k) = (m : ℤ) * 12 := by
    dsimp [m]
    rw [Int.toNat_of_nonneg hk]
    ring
  let D : CuspForm (Gamma1 N) 12 :=
    cuspRestrictSubgroup (Subgroup.map_le_range _ (Gamma1 N)) CuspForm.discriminant
  let F : CuspForm (Gamma1 N) ((m : ℤ) * 12) :=
    (D.mulModularForm ((g.pow 11).mul f)).mcast hw
  let H : CuspForm (Gamma1 N) ((m : ℤ) * 12) :=
    (D.mulModularForm ((g.pow 11).mul g)).mcast hw
  have hF : (qExpansion 1 F : LaurentSeries ℂ) =
      (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) *
        ((qExpansion 1 g : LaurentSeries ℂ) ^ 11 *
          (qExpansion 1 f : LaurentSeries ℂ)) := by
    change (qExpansion 1 ((D : ℍ → ℂ) * ⇑((g.pow 11).mul f)) : LaurentSeries ℂ) = _
    rw [ModularForm.qExpansion_mul_coe one_pos (hper hT),
      ModularForm.qExpansion_mul one_pos (hper hT),
      ModularForm.qExpansion_pow one_pos (hper hT),
      PowerSeries.coe_mul, PowerSeries.coe_mul, PowerSeries.coe_pow]
    rfl
  have hH : (qExpansion 1 H : LaurentSeries ℂ) =
      (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) *
        ((qExpansion 1 g : LaurentSeries ℂ) ^ 11 *
          (qExpansion 1 g : LaurentSeries ℂ)) := by
    change (qExpansion 1 ((D : ℍ → ℂ) * ⇑((g.pow 11).mul g)) : LaurentSeries ℂ) = _
    rw [ModularForm.qExpansion_mul_coe one_pos (hper hT),
      ModularForm.qExpansion_mul one_pos (hper hT),
      ModularForm.qExpansion_pow one_pos (hper hT),
      PowerSeries.coe_mul, PowerSeries.coe_mul, PowerSeries.coe_pow]
    rfl
  rw [functionFieldOver_eq_qExpFunctionFieldC]
  have hm := div_mem (normalized_cusp_ratio_mem N m F) (normalized_cusp_ratio_mem N m H)
  have hqg : (qExpansion 1 g : LaurentSeries ℂ) ≠ 0 := ModularRatios.qL_ne_zero hT g hg
  rw [div_div_div_cancel_right₀ (pow_ne_zero m discriminant_expansion_ne_zero),
    hF, hH, mul_div_mul_left _ _ discriminant_expansion_ne_zero,
    mul_div_mul_left _ _ (pow_ne_zero 11 hqg)] at hm
  exact hm

end
end Dubon2026.SourceFunctionField.GammaOne
