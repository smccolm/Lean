import Dubon2026.RadialTailIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Gaussian and annular radial integrals with dimension-independent constants -/

namespace Dubon2026

open MeasureTheory Set

theorem integral_radial_gaussian {b : ℝ} (hb : 0 < b) :
    (∫ r : ℝ in Ioi 0, r * Real.exp (-b * r ^ 2)) = (2 * b)⁻¹ := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have he (r : ℝ) : ((r * Real.exp (-b * r ^ 2) : ℝ) : ℂ) =
      (r : ℂ) * Complex.exp (-(b : ℂ) * (r : ℂ) ^ 2) := by
    push_cast
    rfl
  simp_rw [he]
  simpa only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) hb

theorem exists_dimension_geometric_bound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, (m : ℝ) * ρ ^ m ≤ D := by
  have hs : Summable (fun m : ℕ => (m : ℝ) * ρ ^ m) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖ρ‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0])
  refine ⟨∑' m : ℕ, (m : ℝ) * ρ ^ m, tsum_nonneg (fun m => by positivity), ?_⟩
  intro m
  exact hs.le_tsum m (fun n _ => by positivity)

theorem integral_radial_constant {B d : ℝ} (hB : 0 ≤ B) :
    (∫ r : ℝ in Ioc 0 B, r * d) = B ^ 2 * d / 2 := by
  rw [← intervalIntegral.integral_of_le hB, intervalIntegral.integral_mul_const, integral_id]
  ring

theorem integral_radial_annulus_bound {K R ρ D : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hD : ∀ m : ℕ, (m : ℝ) * ρ ^ m ≤ D) (m : ℕ) :
    (∫ r : ℝ in Ioc 0 (R * K * Real.sqrt m), r * ρ ^ m) ≤ R ^ 2 * K ^ 2 * D / 2 := by
  rw [integral_radial_constant (by positivity)]
  have hs : (R * K * Real.sqrt m) ^ 2 = R ^ 2 * K ^ 2 * (m : ℝ) := by
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  rw [hs]
  calc
    _ = (R ^ 2 * K ^ 2 / 2) * ((m : ℝ) * ρ ^ m) := by ring
    _ ≤ (R ^ 2 * K ^ 2 / 2) * D := mul_le_mul_of_nonneg_left (hD m) (by positivity)
    _ = _ := by ring

end Dubon2026
