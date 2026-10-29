import Dubon2026.SourcePeakedSeriesOperations
import Dubon2026.SourcePeakedShiftedCoefficients

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> exact adjusted product series.
The actual series is the literal phase times a monomial shift of the proved
Siegel series and the proved discriminant unit series. The source order
identity cancels all exponential factors. No realization premise is used.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Coefficients
noncomputable section
open Complex UpperHalfPlane PowerSeries Filter Topology FiniteExpansion
open scoped MatrixGroups ModularForm
local notation "𝕢" => Function.Periodic.qParam

/-- The actual Siegel and discriminant series shifted by a specified cusp order. -/
def shiftedSeries (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t M : ℕ) : PowerSeries ℂ :=
  phase N m • (PowerSeries.X ^ M * (productSeries N m * deltaN N ^ t))

/-- The actual shifted series when the infinity order is N times the width-one order. -/
def adjustedSeries (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t m₀ : ℕ) : PowerSeries ℂ :=
  shiftedSeries N m t (N * m₀)

theorem hasSum_shiftedSeries (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t M : ℕ)
    (hm₀ : (M : ℤ) = orderSum N m + (N : ℤ) * t) (τ : ℍ) :
    HasSum (fun k : ℕ => coeff k (shiftedSeries N m t M) * 𝕢 (N : ℝ) τ ^ k)
      ((∏ r : ZMod N, ∏ s : ZMod N,
        siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hC0 := phase_ne_zero N m
  set q := 𝕢 (N : ℝ) τ with hqdef
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  set u : ℍ → ℂ := fun τ => ∏ r : ZMod N, ∏ s : ZMod N,
    siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s) with hu
  set e : ℍ → ℂ := fun τ => cexp (2 * Real.pi * Complex.I * (orderSum N m : ℂ) * (τ : ℂ) / (N : ℂ)) with he
  have hD : Expands (N : ℝ) (productSeries N m) (fun τ => u τ / (phase N m * e τ)) :=
    hasSum_productSeries N m
  have hall := (Expands.mul hNR (expands_X_pow (N : ℝ) (M))
    (Expands.mul hNR hD (Expands.pow hNR (expands_deltaN N) t))).smul (phase N m) τ
  have he' : e τ * q ^ (N * t) = q ^ (M) := by
    have h1 : e τ = q ^ orderSum N m := by rw [he, hqdef, qParam_natCast_zpow]
    have h2 : orderSum N m + ((N * t : ℕ) : ℤ) = ((M : ℕ) : ℤ) := by push_cast; linarith
    rw [h1, ← zpow_natCast, ← zpow_add₀ hq0, h2, zpow_natCast]
  have he0 : e τ ≠ 0 := Complex.exp_ne_zero _
  have hval : phase N m * (q ^ (M) *
      (u τ / (phase N m * e τ) * (ModularForm.discriminant τ / q ^ N) ^ t)) =
      u τ * ModularForm.discriminant τ ^ t := by
    rw [div_pow, ← pow_mul, ← he']
    field_simp
  change HasSum _ (u τ * ModularForm.discriminant τ ^ t)
  rw [← hval]
  exact hall


theorem hasSum_adjustedSeries (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t m₀ : ℕ)
    (hm₀ : (N : ℤ) * m₀ = orderSum N m + (N : ℤ) * t) (τ : ℍ) :
    HasSum (fun k : ℕ => coeff k (adjustedSeries N m t m₀) * 𝕢 (N : ℝ) τ ^ k)
      ((∏ r : ZMod N, ∏ s : ZMod N,
        siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) :=
  hasSum_shiftedSeries N m t (N * m₀) (by simpa only [Nat.cast_mul] using hm₀) τ

theorem integral_shiftedSeries (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t M k : ℕ) :
    IsIntegral ℤ (coeff k (shiftedSeries N m t M)) := by
  simp only [shiftedSeries, coeff_smul, smul_eq_mul, coeff_X_pow_mul']
  split_ifs
  · exact (isIntegral_phase N m).mul (integral_product_delta N m t _)
  · rw [mul_zero]; exact isIntegral_zero

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Coefficients
