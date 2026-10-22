import Dubon2026.SourceOriginalMeromorphicBoundaryValues
import Dubon2026.SourceOriginalDissectionSkeletonRegularity

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The existing centered-pole geometry makes the whole skeleton regular. Reuse
the proved arc integrability and the native fundamental theorem of calculus
to identify logarithmic boundary increments with actual differential integrals.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem regular_bdry {D : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos D S) (r : R) (C : D.ιC) (k : Fin (D.cell C).R.N)
    {s : ℝ} (hs : s ∈ (D.cell C).R.arcIcc k) :
    0 ≤ ((D.cell C).bdry s).ordDifferential (θ r) := by
  apply D.regular_on_skeleton S (fun v hv => ⟨_, (hS.hd5 v hv).choose_spec.1⟩)
    (θ r) (fun v hv => (hθ r v).2 hv)
  exact D.bdry_mem_skeleton C k hs

theorem arc_ftc_hfun {D : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos D S) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (r : R) (C : D.ιC) (k : Fin (D.cell C).R.N) :
    (∫ s in ((D.cell C).R.φs k.castSucc)..((D.cell C).R.φs k.succ),
      (D.cell C).bdryIntegrand (θ r) s) =
      hfun S θ Ψ C ((D.cell C).R.φs k.succ) r -
        hfun S θ Ψ C ((D.cell C).R.φs k.castSucc) r := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    ((D.cell C).R.hmono Fin.castSucc_lt_succ).le (continuous_hfun S θ hP r C).continuousOn
  · exact fun s hs => hasDerivAt_hfun S θ hP r C k hs
  · exact (D.cell C).arc_integrable k (θ r) (fun s hs => regular_bdry S θ hθ hS r C k hs)

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
