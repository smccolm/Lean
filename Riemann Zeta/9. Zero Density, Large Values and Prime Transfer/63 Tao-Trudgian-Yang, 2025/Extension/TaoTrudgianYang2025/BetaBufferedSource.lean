import TaoTrudgianYang2025.BetaBufferedBoundary
import TaoTrudgianYang2025.BetaBufferedStationary

/-!
# Uniform buffered Poisson entry from the original lattice parameters

The single stationary constant is chosen before N, both integer endpoints,
and eta. The genuine original source sum and its endpoint loss are retained.
-/

noncomputable section

open Set Expdb
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem modelPhase_buffered_poisson_stationary
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ → 0 < T →
        Summable (fun q : ℤ => ‖modelPhaseFourierMode
          (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖) ∧
        ‖exponentialSumAt F T N a b-
          ∑' q : ℤ, modelPhaseFourierMode
            (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤ 4*N*η+2 ∧
        ∀ q : ℤ, (q : ℝ)*N/T ∈ modelPhaseSlopeRange F →
          ‖modelPhaseFourierMode
              (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q-
            (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η
              (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
                modelPhaseStationaryMainTerm F T N q‖ ≤
            C*(η⁻¹)^bufferedStationaryWidthDegree*N/T := by
  obtain ⟨C,hC,hmode⟩ := modelPhaseBufferedFourierMode_stationary_uniform hσ
  refine ⟨C,hC,?_⟩
  intro N η a b hN hη hη₁ ha hb F δ T hδ hF hT
  have hsource := modelPhase_buffered_poisson hF hN hη ha hb T
  refine ⟨hsource.1,hsource.2,?_⟩
  intro q hq
  exact hmode ((a : ℝ)/N) ((b : ℝ)/N) η
    ((one_le_div hN).mpr ha) ((div_le_iff₀ hN).mpr hb)
    hη hη₁ F δ T N q hδ hF hT hN hq

end TaoTrudgianYang2025
