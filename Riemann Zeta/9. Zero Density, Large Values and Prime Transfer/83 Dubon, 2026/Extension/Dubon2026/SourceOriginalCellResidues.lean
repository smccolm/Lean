import Dubon2026.SourceOriginalCellPuncturedCoefficient
import Dubon2026.SourceComplexSimplePolePullback
import Dubon2026.SourceOriginalLogarithmicReading
import Dubon2026.SourceOriginalCellCoefficientPullback

/-! DUB-17/18 -> raw reciprocity -> actual cell coefficient calculus.
The original simple-pole decomposition and nonsingular coordinate pullback
produce the exact original residue divided by the cell coordinate difference,
plus an analytic remainder. The final theorem assembles both source clauses:
regular coefficient calculus and the simple-pole residue expansion.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Manifold Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem AnalyticCoord.coeff_simple_pole (A : AnalyticCoord N) {Q : Place ℂ F}
    (hQ : Q ∈ A.ζ.source) (θ : Ω[F⁄ℂ]) (hθ : -1 ≤ Q.ordDifferential θ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (A.ζ Q) ∧ ∀ᶠ w in 𝓝[≠] (A.ζ Q),
      coeffIn A.ζ θ w =
        originalPlaceEval N ℂ Q (Q.uniformizer * Q.differentialCoeff θ) / (w - A.ζ Q) + G w := by
  let σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm
  let r := originalPlaceEval N ℂ Q (Q.uniformizer * Q.differentialCoeff θ)
  have hσa : AnalyticAt ℂ σ (A.ζ Q) := A.analyticAt_inverse hQ
  have hσ0 : σ (A.ζ Q) = 0 := by
    change (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) (A.ζ Q) = 0
    rw [(A.local_inverse hQ).2.2.2, OriginalChart.extPlaceChart_self]
  have hσd : deriv σ (A.ζ Q) ≠ 0 := by
    have h := (A.local_inverse hQ).2.1.self_of_nhds
    rw [h.2.2.deriv]
    exact inv_ne_zero h.2.1
  obtain ⟨b, hb, hread⟩ := OriginalChart.exists_original_logarithmic_reading N Q θ hθ r rfl
  obtain ⟨G, hGa, hmodel⟩ := exists_simple_pole_pullback_remainder σ
    (OriginalChart.chartRead N Q b) (A.ζ Q) r hσa hσ0 hσd
      (OriginalChart.analyticAt_place_reading N Q hb)
  have ht : Tendsto σ (𝓝[≠] (A.ζ Q)) (𝓝[≠] (0 : ℂ)) := by
    have h := A.inverse_tendsto_punctured hQ
    rwa [OriginalChart.extPlaceChart_self] at h
  refine ⟨G, hGa, ?_⟩
  filter_upwards [A.coeff_eq_near_punctured hQ θ, ht.eventually hread, hmodel]
    with w hw hwr hwm
  rw [hw, hwr]
  exact (by simpa only [div_eq_mul_inv] using hwm)

theorem AnalyticCoord.local_calculus (A : AnalyticCoord N) {Q : Place ℂ F}
    (hQ : Q ∈ A.ζ.source) (θ : Ω[F⁄ℂ]) :
    (0 ≤ Q.ordDifferential θ →
      (∀ᶠ w in 𝓝 (A.ζ Q), coeffIn A.ζ θ w =
        OriginalChart.readDifferential N Q θ ((extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) w) *
          deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) w) ∧
      AnalyticAt ℂ (coeffIn A.ζ θ) (A.ζ Q) ∧
      ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
        coeffIn A.ζ θ ((A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y) *
          deriv (A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y = OriginalChart.readDifferential N Q θ y) ∧
    (-1 ≤ Q.ordDifferential θ →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G (A.ζ Q) ∧ ∀ᶠ w in 𝓝[≠] (A.ζ Q),
        coeffIn A.ζ θ w =
          originalPlaceEval N ℂ Q (Q.uniformizer * Q.differentialCoeff θ) / (w - A.ζ Q) + G w) := by
  refine ⟨fun hθ => ?_, A.coeff_simple_pole hQ θ⟩
  have hreg := Q.mem_of_ord_nonneg hθ
  exact ⟨(A.coeff_eq_near hQ hreg).1, (A.coeff_eq_near hQ hreg).2,
    A.coeff_comp_mul_deriv hQ hreg⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
