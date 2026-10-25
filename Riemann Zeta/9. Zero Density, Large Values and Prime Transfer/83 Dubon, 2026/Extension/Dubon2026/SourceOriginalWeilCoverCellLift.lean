import Dubon2026.SourceCoverLiftedCoordinate
import Dubon2026.SourceOriginalWeilCoverLiftedCoordinateAnalytic
import Dubon2026.SourceOriginalAnalyticCells

/-! DUB-17/18 -> cover raw reciprocity -> literal lifted original cells.
Every existing original radial cell lifts through every point over its center
on an open star-convex neighborhood of its entire compact carrier. The lift
is an actual analytic nonsingular coordinate with the exact restriction map.
Finite global dissection and the reciprocity identities are still separate. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem exists_cover_cell_lift (C : CellGeometry.Cell N) (w : Place ℂ EE)
    (hw : w.restrict FF = C.ζ.symm C.R.q) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ (V : Set ℂ) (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ),
      IsOpen V ∧ C.R.q ∈ V ∧ StarConvex ℝ C.R.q V ∧ C.R.K ⊆ V ∧ V ⊆ C.ζ.target ∧
      ζ.target = V ∧ w ∈ ζ.source ∧ ζ w = C.R.q ∧
      (∀ z ∈ V, (ζ.symm z).restrict FF = C.ζ.symm z) ∧
      (∀ P ∈ ζ.source, P.restrict FF ∈ C.ζ.source ∧ ζ P = C.ζ (P.restrict FF)) ∧
      (∀ P ∈ ζ.source,
        AnalyticAt ℂ (ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv (ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  obtain ⟨V, hV, hq, hc, hK, hVe⟩ := C.exists_primitive_domain
  have hl := SheetCover.exists_open_lift_of_starConvex (fun P : Place ℂ EE => P.restrict FF)
    (isCoveringMap_restriction N n radicand baseDivisor hRadicand hOrders)
    C.ζ hV hq hc hVe w hw
  obtain ⟨s, hsq, hsp, hs⟩ := hl
  obtain ⟨ζ, hsource, htarget, hforward, hinverse, hmap⟩ :=
    SheetCover.exists_coordinate_of_open_lift (fun P : Place ℂ EE => P.restrict FF)
      C.ζ hV hq hVe s hs hsp
  refine ⟨V, ζ, hV, hq, hc, hK, hVe, htarget, ?_, ?_, ?_, hmap, ?_⟩
  · rw [hsource]
    exact ⟨⟨C.R.q, hq⟩, hsq⟩
  · rw [← hsq]
    exact hforward ⟨C.R.q, hq⟩
  · intro z hz
    rw [hinverse z hz]
    exact hsp ⟨z, hz⟩
  · exact analytic_lifted_coordinate N n radicand baseDivisor hRadicand hOrders C.toAnalyticCoord ζ hmap

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
