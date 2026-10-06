import Dubon2026.SteinhausDensity
import Dubon2026.BoundedLogExpectation

/-! # The translated logarithmic estimate for the normalized actual Haar sum -/

namespace Dubon2026

open MeasureTheory

noncomputable section

theorem norm_steinhausSum_le {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (z : ι → UnitAddCircle) : ‖steinhausSum c z‖ ≤ ∑ i, |c i| := by
  unfold steinhausSum
  calc
    ‖∑ i, (c i : ℂ) * fourier 1 (z i)‖ ≤ ∑ i, ‖(c i : ℂ) * fourier 1 (z i)‖ :=
      norm_sum_le _ _
    _ = ∑ i, |c i| := by simp [fourier_apply]

theorem steinhausLaw_translated_smallBall_eq {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (a : ℂ) (r : ℝ) :
    (steinhausLaw c) {w : ℂ | ‖a + w‖ ≤ r} =
      (steinhausHaar ι) {z | ‖a + steinhausSum c z‖ ≤ r} := by
  unfold steinhausLaw
  rw [Measure.map_apply (continuous_steinhausSum c).measurable
    (measurableSet_le (by fun_prop : Measurable (fun w : ℂ => ‖a + w‖)) measurable_const)]
  rfl

/-- One constant for all normalized Haar sums, including every complex translation. -/
theorem exists_uniform_normalized_steinhaus_log {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K → ∀ a : ℂ,
      Integrable (fun z => Real.log ‖a + steinhausSum (normalizedSteinhausCoefficients b) z‖)
        (steinhausHaar κ) ∧
      -C ≤ ∫ z, Real.log ‖a + steinhausSum (normalizedSteinhausCoefficients b) z‖
        ∂steinhausHaar κ ∧
      ∀ᵐ z ∂steinhausHaar κ, a + steinhausSum (normalizedSteinhausCoefficients b) z ≠ 0 := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_steinhaus_density_smallBall hK
  refine ⟨D * Real.pi, by positivity, ?_⟩
  intro κ _ _ b hb hm hcomp a
  obtain ⟨_, _, _, hball, hne⟩ := hbound κ b hb hm hcomp
  have hbounded : ∀ᵐ z ∂steinhausHaar κ,
      ‖a + steinhausSum (normalizedSteinhausCoefficients b) z‖ ≤
        ‖a‖ + ∑ i, |normalizedSteinhausCoefficients b i| :=
    Filter.Eventually.of_forall (fun z => (norm_add_le _ _).trans
      (add_le_add le_rfl (norm_steinhausSum_le _ z)))
  obtain ⟨hi, he⟩ := integrable_log_norm_of_bounded_smallBall
    (continuous_const.add (continuous_steinhausSum (normalizedSteinhausCoefficients b))).measurable
    hbounded (show 0 ≤ D * Real.pi by positivity)
    (fun r hr => by
      simp only [Pi.add_apply]
      rw [← steinhausLaw_translated_smallBall_eq]
      exact hball a r hr.le)
  refine ⟨hi, he, ?_⟩
  exact ae_of_ae_map (continuous_steinhausSum (normalizedSteinhausCoefficients b)).measurable.aemeasurable
    (hne a)

end

end Dubon2026
