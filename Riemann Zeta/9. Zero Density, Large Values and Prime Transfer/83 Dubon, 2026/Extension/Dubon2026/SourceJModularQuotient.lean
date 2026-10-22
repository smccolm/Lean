import Dubon2026.SourceModularJBaseChange
import Dubon2026.SourceEisensteinFourExpansion
import Dubon2026.SourceDiscriminantIntegralExpansion

/-! DUB-17/18 -> matching cusp-form lower dimension -> analytic
realization of the original field. The literal j series is the quotient
of the actual E4-cube and discriminant expansions. Existing integral
coefficient identities prove this directly, so no additional convergence
or Laurent-product uniqueness infrastructure is needed here.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane

theorem jqModC_mul_discriminant_expansion :
    jqModC ℂ * (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) =
      (qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) : LaurentSeries ℂ) ^ 3 := by
  rw [qExpansion_E4_eq_map_eisenstein4,
    qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit]
  let φ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map (Int.castRingHom ℂ))
  have hX : φ PowerSeries.X = HahnSeries.single 1 1 := by
    simp [φ, HahnSeries.ofPowerSeries_X]
  change (HahnSeries.single (-1 : ℤ) 1 * φ jNum) *
    φ (PowerSeries.X * dedekindEtaUnit) = (φ eisenstein4) ^ 3
  rw [map_mul, hX]
  have hmul : jNum * dedekindEtaUnit = eisenstein4 ^ 3 := by
    rw [jNum, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one]
  calc
    _ = (HahnSeries.single (-1 : ℤ) 1 * HahnSeries.single 1 1) *
        φ (jNum * dedekindEtaUnit) := by rw [map_mul]; ring
    _ = (φ eisenstein4) ^ 3 := by
      rw [HahnSeries.single_mul_single, neg_add_cancel, one_mul,
        HahnSeries.single_zero_one, one_mul, hmul, map_pow]

theorem discriminant_expansion_ne_zero :
    (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) ≠ 0 := by
  intro h
  have hq : qExpansion 1 ModularForm.discriminant = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using h)
  have hc := ModularForm.discriminant_qExpansion_coeff_one
  rw [hq, map_zero] at hc
  exact zero_ne_one hc

theorem jqModC_eq_modular_quotient :
    jqModC ℂ = (qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) : LaurentSeries ℂ) ^ 3 /
      (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) :=
  (eq_div_iff discriminant_expansion_ne_zero).mpr jqModC_mul_discriminant_expansion

end
end Dubon2026.SourceFunctionField
