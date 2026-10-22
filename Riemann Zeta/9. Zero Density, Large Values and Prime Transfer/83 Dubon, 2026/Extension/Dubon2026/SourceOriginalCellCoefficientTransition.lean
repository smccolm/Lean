import Dubon2026.SourceOriginalCellCoordinateTransition

/-! DUB-17/18 -> raw reciprocity -> paired-edge cancellation.
The same original centered differential reading gives the exact coefficient
change between genuine cell coordinates. The reciprocal derivative cancels
against the transition derivative. This pointwise identity introduces no
regularity premise; regularity is used separately for boundary continuity.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Manifold Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem AnalyticCoord.coeff_transition (A B : AnalyticCoord N)
    {Q : Place ℂ (modularFunctionFieldOver N ℂ)} (hA : Q ∈ A.ζ.source) (hB : Q ∈ B.ζ.source)
    (θ : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) :
    coeffIn A.ζ θ (A.ζ Q) = coeffIn B.ζ θ (B.ζ Q) * deriv (B.ζ ∘ A.ζ.symm) (A.ζ Q) := by
  unfold coeffIn
  rw [A.ζ.left_inv hA, B.ζ.left_inv hB, A.deriv_transition B hA hB]
  have hBder := (B.local_inverse hB).2.1.self_of_nhds.2.2.deriv
  rw [B.ζ.left_inv hB] at hBder
  rw [hBder]
  have hn := B.deriv_ne Q hB
  field_simp

end
end Dubon2026.SourceFunctionField.CellGeometry
