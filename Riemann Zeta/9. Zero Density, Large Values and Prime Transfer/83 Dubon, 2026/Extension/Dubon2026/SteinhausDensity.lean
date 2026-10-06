import Dubon2026.SteinhausFourierL1
import Dubon2026.PlanarSmallBall

/-! # One actual density bound and translated small-ball constant for all admissible sums -/

namespace Dubon2026

open MeasureTheory

/-- The constant is chosen before the dimension, coefficients, translation and radius. -/
theorem exists_uniform_steinhaus_density_smallBall {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K →
      let μ := steinhausLaw (normalizedSteinhausCoefficients b)
      Continuous (planarCharDensity μ) ∧
      (∀ x, 0 ≤ planarCharDensity μ x ∧ planarCharDensity μ x ≤ C) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (planarCharDensity μ x)) ∧
      (∀ a : ℂ, ∀ r : ℝ, 0 ≤ r →
        μ {z : ℂ | ‖a + z‖ ≤ r} ≤ ENNReal.ofReal (C * Real.pi * r ^ 2)) ∧
      (∀ a : ℂ, ∀ᵐ z ∂μ, a + z ≠ 0) := by
  obtain ⟨L, hL, hbnd⟩ := exists_uniform_steinhaus_charFun_L1 hK
  refine ⟨((2 * Real.pi) ^ 2)⁻¹ * L, by positivity, ?_⟩
  intro κ _ _ b hb hm hcomp
  obtain ⟨hi, hbound⟩ := hbnd κ b hb hm hcomp
  have hd : ∀ x, planarCharDensity (steinhausLaw (normalizedSteinhausCoefficients b)) x ≤
      ((2 * Real.pi) ^ 2)⁻¹ * L := fun x =>
    (planarCharDensity_le _ x).trans (mul_le_mul_of_nonneg_left hbound (by positivity))
  refine ⟨continuous_planarCharDensity hi,
    fun x => ⟨planarCharDensity_nonneg hi x, hd x⟩,
    measure_eq_withDensity_planarCharDensity hi, ?_, ?_⟩
  · exact fun a r hr => planar_translated_smallBall hi (by positivity) hd a hr
  · exact planar_translated_ne_zero_ae hi

end Dubon2026
