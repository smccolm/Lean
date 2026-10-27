import Dubon2026.SourceFrickeEllipticCoordinateTwist

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> exact cusp-image characterization. Holomorphic divisions by two factors
with no common zero glue to division by their product. Adapted from
anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff. Native manifold-local
congruence removes the source's separate chart and identity helpers. -/
namespace Dubon2026.SourceFunctionField.CuspWeightCriterion
noncomputable section
open UpperHalfPlane Filter
open scoped Topology Manifold

theorem exists_mul_eq_of_coprime {P b c H₁ H₂ : ℍ → ℂ}
    (hb : MDiff b) (hc : MDiff c) (hH₁ : MDiff H₁) (hH₂ : MDiff H₂)
    (hcop : ∀ τ : ℍ, b τ ≠ 0 ∨ c τ ≠ 0)
    (h₁ : ∀ τ : ℍ, H₁ τ * b τ = P τ) (h₂ : ∀ τ : ℍ, H₂ τ * c τ = P τ) :
    ∃ f : ℍ → ℂ, MDiff f ∧ ∀ τ : ℍ, f τ * (b τ * c τ) = P τ := by
  classical
  let f : ℍ → ℂ := fun τ => if c τ = 0 then H₂ τ / b τ else H₁ τ / c τ
  refine ⟨f, fun τ => ?_, fun τ => ?_⟩
  · by_cases hc0 : c τ = 0
    · have hb0 : b τ ≠ 0 := (hcop τ).resolve_right (not_not_intro hc0)
      apply ((hH₂ τ).div (hb τ) hb0).congr_of_eventuallyEq
      filter_upwards [hb.continuous.continuousAt.eventually_ne hb0] with z hz
      by_cases hcz : c z = 0
      · simp only [f, hcz, if_true, Pi.div_apply]
      · simp only [f, hcz, if_false]
        apply (div_eq_div_iff hcz hz).mpr
        exact (h₁ z).trans (h₂ z).symm
    · apply ((hH₁ τ).div (hc τ) hc0).congr_of_eventuallyEq
      filter_upwards [hc.continuous.continuousAt.eventually_ne hc0] with z hz
      simp only [f, hz, if_false, Pi.div_apply]
  · by_cases hcz : c τ = 0
    · simp only [f, hcz, if_true, mul_zero]
      rw [← h₂ τ, hcz, mul_zero]
    · simp only [f, hcz, if_false]
      rw [← h₁ τ]
      field_simp

end
end Dubon2026.SourceFunctionField.CuspWeightCriterion