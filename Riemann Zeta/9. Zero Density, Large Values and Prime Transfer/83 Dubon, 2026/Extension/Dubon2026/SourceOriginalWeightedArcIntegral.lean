import Dubon2026.SourceCellArcIntegralExtension
import Dubon2026.SourceOriginalCellBoundaryIntegrability

/-! DUB-17/18 -> raw reciprocity -> weighted paired-edge integrals.
The actual weighted differential integrand agrees off the arc endpoints with
its continuous extension. This supplies both integrability and exact integral
equality needed by reversed-edge substitution.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set MeasureTheory KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.weighted_arc_integral_extension (C : Cell N) (k : Fin C.R.N)
    (θ : Ω[F⁄ℂ]) (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ)
    (W : ℝ → ℂ) (hW : ContinuousOn W (C.R.arcIcc k)) :
    IntervalIntegrable (fun s => W s * C.bdryIntegrand θ s) volume
        (C.R.φs k.castSucc) (C.R.φs k.succ) ∧
      (∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), W s * C.bdryIntegrand θ s) =
        ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ),
          W s * (coeffIn C.ζ θ (C.R.loop s) * C.R.loopDerivOnArc k s) := by
  apply arc_integral_eq_of_continuous_extension (C.R.hmono Fin.castSucc_lt_succ).le
    (hW.mul ((C.continuousOn_boundary_coefficient k θ hθ).mul
      (C.R.continuous_loopDerivOnArc k).continuousOn))
  intro s hs
  change W s * (coeffIn C.ζ θ (C.R.loop s) * C.R.loop' s) = _
  rw [C.R.loop'_eq_loopDerivOnArc k hs]
  rfl

end
end Dubon2026.SourceFunctionField.CellGeometry
