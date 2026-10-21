import Dubon2026.SourcePowerSeriesProduct
import Mathlib.RingTheory.LaurentSeries

/-! DUB-17/18 -> cusp-form lower dimension bound -> regular differential
realization -> original finite function-field extension -> modular polynomial
relations -> rational coefficient descent. This selects the literal Laurent
principal-part removal and the actual analytic realization argument, reusing
pinned weight-zero constancy and q-expansion coefficient uniqueness. No
polynomial relation or coefficient descent is postulated.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_hasSum_qParam_mul_laurent.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups ModularForm
local notation "𝕢" => Function.Periodic.qParam

namespace Realized

theorem hasSum_single_mul_coe_iff (k : ℤ) (P : PowerSeries ℂ) {q : ℂ} (hq : q ≠ 0) (t : ℂ) :
    HasSum (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m * q ^ m) (t * q ^ k) ↔
      HasSum (fun n : ℕ => PowerSeries.coeff n P * q ^ n) t := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + k) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m * q ^ m) ∘
        (fun n : ℕ => (n : ℤ) + k) = fun n : ℕ => (PowerSeries.coeff n P * q ^ n) * q ^ k := by
      funext n
      simp only [Function.comp_apply]
      rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.coeff_coe_powerSeries, zpow_add₀ hq,
        zpow_natCast]
      ring
    rw [hfg]
    exact hasSum_mul_right_iff (zpow_ne_zero k hq)
  · intro m hm
    have hmk : m - k < 0 := by
      by_contra hge
      push Not at hge
      exact hm ⟨(m - k).toNat, by simp only; omega⟩
    rw [← sub_add_cancel m k, HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe, if_pos hmk,
      zero_mul]

theorem hasSum_qParam_mul_laurent (h : ℝ) (hh : 0 < h) (A B : LaurentSeries ℂ) (F G : ℍ → ℂ)
    (hA : ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (hB : ∀ τ : ℍ, HasSum (fun m : ℤ => B.coeff m * 𝕢 h (τ : ℂ) ^ m) (G τ)) (τ : ℍ) :
    HasSum (fun m : ℤ => (A * B).coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ * G τ) := by
  have hq0 : ∀ τ : ℍ, 𝕢 h (τ : ℂ) ≠ 0 := fun τ => Periodic.qParam_ne_zero _

  set F' : ℍ → ℂ := fun τ => F τ * (𝕢 h (τ : ℂ) ^ A.order)⁻¹ with hF'
  set G' : ℍ → ℂ := fun τ => G τ * (𝕢 h (τ : ℂ) ^ B.order)⁻¹ with hG'
  have hA' : ∀ τ : ℍ, HasSum (fun n : ℕ => PowerSeries.coeff n A.powerSeriesPart * 𝕢 h (τ : ℂ) ^ n) (F' τ) := by
    intro τ
    rw [← hasSum_single_mul_coe_iff A.order A.powerSeriesPart (hq0 τ), A.single_order_mul_powerSeriesPart,
      hF', inv_mul_cancel_right₀ (zpow_ne_zero _ (hq0 τ))]
    exact hA τ
  have hB' : ∀ τ : ℍ, HasSum (fun n : ℕ => PowerSeries.coeff n B.powerSeriesPart * 𝕢 h (τ : ℂ) ^ n) (G' τ) := by
    intro τ
    rw [← hasSum_single_mul_coe_iff B.order B.powerSeriesPart (hq0 τ), B.single_order_mul_powerSeriesPart,
      hG', inv_mul_cancel_right₀ (zpow_ne_zero _ (hq0 τ))]
    exact hB τ
  have H := hasSum_qParam_mul h hh A.powerSeriesPart B.powerSeriesPart F' G' hA' hB' τ

  have hAB : HahnSeries.single (A.order + B.order) (1 : ℂ) *
      ((A.powerSeriesPart * B.powerSeriesPart : PowerSeries ℂ) : LaurentSeries ℂ) = A * B := by
    conv_rhs => rw [← A.single_order_mul_powerSeriesPart, ← B.single_order_mul_powerSeriesPart]
    rw [PowerSeries.coe_mul, ← one_mul (1 : ℂ), ← HahnSeries.single_mul_single, one_mul]
    ring
  have hFG : F τ * G τ = F' τ * G' τ * 𝕢 h (τ : ℂ) ^ (A.order + B.order) := by
    have hqτ := hq0 τ
    simp only [hF', hG']
    rw [zpow_add₀ hqτ]
    field_simp
  rw [← hAB, hFG]
  exact (hasSum_single_mul_coe_iff _ _ (hq0 τ) _).mpr H

end Realized

end
end Dubon2026.SourceFunctionField
