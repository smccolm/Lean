import Dubon2026.SourceCuspWeightFactors
import Dubon2026.SourceHolomorphicMonicQuotient

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> exact cusp-image characterization. Power divisibility by E4 or E6
produces literal holomorphic division by the corresponding original factor.
The already proved local monic quotient theorem discharges the external
analytic dependency. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff. -/
namespace Dubon2026.SourceFunctionField.CuspWeightCriterion
noncomputable section
open UpperHalfPlane ModularForm
open scoped Manifold ModularForm
local notation "Δ" => ModularForm.discriminant

theorem exists_div_E4 {a m : ℕ} {F : ℍ → ℂ} (hF : MDiff F) (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧
      ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) :
    ∃ H : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H ∧ ∀ τ : ℍ, H τ * E₄ τ ^ a = F τ * Δ τ ^ m := by
  classical
  obtain ⟨G, hG, hrel⟩ := h
  let P : ℍ → ℂ := fun τ => F τ * Δ τ ^ m
  let B : ℍ → ℂ := fun τ => E₄ τ ^ a
  let c : ℕ → ℍ → ℂ := fun i => if i = 0 then -G else 0
  have hP : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := hF.mul (JMultiplicity.mdiff_Δ.pow m)
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := JMultiplicity.mdiff_E₄.pow a
  have hB0 : B ≠ 0 := by
    obtain ⟨τ, hτ⟩ := exists_E4_ne_zero
    intro hB0
    exact pow_ne_zero a hτ (by simpa [B] using congrFun hB0 τ)
  have hc : ∀ i < 3, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [c, hi] using hG.neg
    · simpa only [c, hi, if_false] using
        (mdifferentiable_const : MDiff (fun _ : ℍ => (0 : ℂ)))
  have hmonic : P ^ 3 + ∑ i ∈ Finset.range 3, c i * B ^ (3 - i) * P ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, c, P, B]
    simp only [if_true, show (1 : ℕ) ≠ 0 from one_ne_zero, show (2 : ℕ) ≠ 0 from two_ne_zero, if_false,
      Pi.neg_apply, Pi.zero_apply]
    rw [hrel τ]; ring
  obtain ⟨H, hH, hHB⟩ := exists_mdifferentiable_quotient_of_monic hP hB hB0 hc hmonic
  exact ⟨H, hH, fun τ => by simpa [P, B] using congrFun hHB τ⟩

theorem exists_div_E6 {b m : ℕ} {F : ℍ → ℂ} (hF : MDiff F) (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧
      ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) :
    ∃ H : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H ∧ ∀ τ : ℍ, H τ * E₆ τ ^ b = F τ * Δ τ ^ m := by
  classical
  obtain ⟨G, hG, hrel⟩ := h
  let P : ℍ → ℂ := fun τ => F τ * Δ τ ^ m
  let B : ℍ → ℂ := fun τ => E₆ τ ^ b
  let c : ℕ → ℍ → ℂ := fun i => if i = 0 then -G else 0
  have hP : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := hF.mul (JMultiplicity.mdiff_Δ.pow m)
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := JMultiplicity.mdiff_E₆.pow b
  have hB0 : B ≠ 0 := by
    obtain ⟨τ, hτ⟩ := exists_E6_ne_zero
    intro hB0
    exact pow_ne_zero b hτ (by simpa [B] using congrFun hB0 τ)
  have hc : ∀ i < 2, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [c, hi] using hG.neg
    · simpa only [c, hi, if_false] using
        (mdifferentiable_const : MDiff (fun _ : ℍ => (0 : ℂ)))
  have hmonic : P ^ 2 + ∑ i ∈ Finset.range 2, c i * B ^ (2 - i) * P ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, c, P, B]
    simp only [if_true, show (1 : ℕ) ≠ 0 from one_ne_zero, if_false, Pi.neg_apply, Pi.zero_apply]
    rw [hrel τ]; ring
  obtain ⟨H, hH, hHB⟩ := exists_mdifferentiable_quotient_of_monic hP hB hB0 hc hmonic
  exact ⟨H, hH, fun τ => by simpa [P, B] using congrFun hHB τ⟩

end
end Dubon2026.SourceFunctionField.CuspWeightCriterion
