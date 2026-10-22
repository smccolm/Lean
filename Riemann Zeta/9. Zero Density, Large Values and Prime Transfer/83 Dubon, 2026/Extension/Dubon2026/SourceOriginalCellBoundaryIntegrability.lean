import Dubon2026.SourceOriginalCellPrimitives
import Dubon2026.SourceCellBoundaryDifferentiation

/-! DUB-17/18 -> raw reciprocity -> paired-edge integral cancellation.
Actual cell boundaries stay in their coordinate domains. When an original
differential is regular along an arc, its coefficient is continuous there;
the continuous arc derivative extension proves integrability of the genuine
boundary integrand, including both endpoints of the source arc.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter MeasureTheory KaehlerDifferential
open scoped Topology Interval
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.bdry_coordinates (C : Cell N) (s : ℝ) :
    C.bdry s ∈ C.ζ.source ∧ C.ζ (C.bdry s) = C.R.loop s :=
  ⟨C.ζ.map_target (C.hKt (C.R.loop_mem_K s)), C.ζ.right_inv (C.hKt (C.R.loop_mem_K s))⟩

theorem Cell.continuous_bdry (C : Cell N) : Continuous C.bdry :=
  continuous_iff_continuousAt.mpr fun s =>
    (C.ζ.continuousAt_symm (C.hKt (C.R.loop_mem_K s))).comp C.R.continuous_loop.continuousAt

theorem Cell.continuousOn_boundary_coefficient (C : Cell N) (k : Fin C.R.N) (θ : Ω[F⁄ℂ])
    (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) :
    ContinuousOn (fun s => coeffIn C.ζ θ (C.R.loop s)) (C.R.arcIcc k) := by
  intro s hs
  have ha := C.toAnalyticCoord.analyticAt_coeff θ (C.hKt (C.R.loop_mem_K s))
    ((C.bdry s).mem_of_ord_nonneg (hθ s hs))
  exact (ha.continuousAt.comp C.R.continuous_loop.continuousAt).continuousWithinAt

theorem Cell.arc_integrable (C : Cell N) (k : Fin C.R.N) (θ : Ω[F⁄ℂ])
    (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) :
    IntervalIntegrable (C.bdryIntegrand θ) volume (C.R.φs k.castSucc) (C.R.φs k.succ) := by
  let a := C.R.φs k.castSucc
  let b := C.R.φs k.succ
  have hab : a < b := C.R.hmono Fin.castSucc_lt_succ
  have hc : ContinuousOn (fun s => coeffIn C.ζ θ (C.R.loop s) * C.R.loopDerivOnArc k s) (Icc a b) :=
    (C.continuousOn_boundary_coefficient k θ hθ).mul (C.R.continuous_loopDerivOnArc k).continuousOn
  apply (hc.intervalIntegrable_of_Icc hab.le).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  have hb : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({b} : Set ℝ) :=
    compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [hb] with s hsb hs
  rw [uIoc_of_le hab.le] at hs
  change _ = coeffIn C.ζ θ (C.R.loop s) * C.R.loop' s
  rw [C.R.loop'_eq_loopDerivOnArc k ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩]

end
end Dubon2026.SourceFunctionField.CellGeometry
