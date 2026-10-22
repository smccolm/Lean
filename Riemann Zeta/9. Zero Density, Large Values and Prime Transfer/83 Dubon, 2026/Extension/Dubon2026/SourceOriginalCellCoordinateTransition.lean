import Dubon2026.SourceOriginalCellCoordinateInverse

/-! DUB-17/18 -> raw reciprocity -> paired-edge cancellation.
Transitions between two genuine cell coordinates are analytic. Their derivative
is obtained through the same original centered chart and the proved inverse
coordinate derivative, giving the exact chain rule needed on paired boundaries.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter
open scoped Manifold Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem AnalyticCoord.transition_eventuallyEq (A B : AnalyticCoord N) {Q : Place ℂ F}
    (hA : Q ∈ A.ζ.source) :
    (B.ζ ∘ A.ζ.symm) =ᶠ[𝓝 (A.ζ Q)]
      (B.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) ∘ (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) := by
  filter_upwards [(A.local_inverse hA).1] with z hz
  dsimp only [Function.comp_apply]
  rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv hz.2]

theorem AnalyticCoord.analyticAt_transition (A B : AnalyticCoord N) {Q : Place ℂ F}
    (hA : Q ∈ A.ζ.source) (hB : Q ∈ B.ζ.source) :
    AnalyticAt ℂ (B.ζ ∘ A.ζ.symm) (A.ζ Q) := by
  have hc := (B.analytic Q hB).comp_of_eq (A.analyticAt_inverse hA) (A.local_inverse hA).2.2.2
  exact hc.congr (A.transition_eventuallyEq B hA).symm

theorem AnalyticCoord.deriv_transition (A B : AnalyticCoord N) {Q : Place ℂ F}
    (hA : Q ∈ A.ζ.source) (hB : Q ∈ B.ζ.source) :
    deriv (B.ζ ∘ A.ζ.symm) (A.ζ Q) =
      deriv (B.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) *
        deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) (A.ζ Q) := by
  rw [(A.transition_eventuallyEq B hA).deriv_eq]
  have hd : HasDerivAt (B.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm)
      (deriv (B.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
      ((extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) (A.ζ Q)) := by
    rw [(A.local_inverse hA).2.2.2]
    exact (B.analytic Q hB).differentiableAt.hasDerivAt
  exact (hd.comp (A.ζ Q) (A.analyticAt_inverse hA).differentiableAt.hasDerivAt).deriv

end
end Dubon2026.SourceFunctionField.CellGeometry
