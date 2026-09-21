import TaoTrudgianYang2025.AtkinsonCarrierBounds

/-!
# Physical zeta consumers of the exact signed-carrier source

The complete arithmetic series is retained. The separate uniform
summand estimates do not replace it by a divergent absolute majorant.
The stationary main-value evaluation remains a further obligation.
-/

noncomputable section

open Complex Filter MeasureTheory
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def atkinsonTwoTermCarrierSum (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, divisorWeight n * (-(2 * Real.pi) : ℂ) * atkinsonTwoTermCarrierIntegral T G L n

theorem eventually_zetaAtkinsonTwoTermSum_eq_carriers {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G →
      zetaAtkinsonTwoTermSum T G (Real.log T) = atkinsonTwoTermCarrierSum T G (Real.log T) := by
  filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ] with T hscale
  intro G hG
  obtain ⟨hG0, hlog, hwidth, _⟩ := hscale.2 G hG
  exact zetaAtkinsonTwoTermSum_eq_carrierIntegrals (by linarith [hscale.1]) hG0 hlog hwidth

theorem exists_zetaSquarePhysicalGaussian_carrier_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (atkinsonTwoTermCarrierSum T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ :=
    exists_zetaSquarePhysicalGaussian_atkinson_twoTerm_approximation hδ
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp (eventually_zetaAtkinsonTwoTermSum_eq_carriers hδ)
  refine ⟨C, hC, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper
  rw [← hB₁ T ((le_max_right _ _).trans hT) G hlower]
  exact hsource T G ((le_max_left _ _).trans hT) hlower hupper

theorem exists_zetaSquareLocalMean_le_carriers {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (atkinsonTwoTermCarrierSum T G (Real.log T)).re +
          C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_twoTerm hδ
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp (eventually_zetaAtkinsonTwoTermSum_eq_carriers hδ)
  refine ⟨C, hC, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper
  rw [← hB₁ T ((le_max_right _ _).trans hT) G hlower]
  exact hsource T G ((le_max_left _ _).trans hT) hlower hupper

end TaoTrudgianYang2025

