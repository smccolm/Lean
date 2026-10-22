import Dubon2026.SourceOriginalBoundaryArcCoordinates

/-! DUB-17/18 -> original Abel-Jacobi -> C1 arc reversal.
Exact affine boundary presentations for the actual global cells. Interior
arcs have positive parameter slope; exterior arcs have negative slope.
These are intermediate geometric statements, proved for every actual arc
in the following modules, not additional inputs to the final pairing.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace

theorem RadialRegion.arc_parameters_cast {R R' : RadialRegion} (h : R = R') (k : Fin R.N) :
    R'.φs (Fin.cast (congrArg RadialRegion.N h) k).castSucc = R.φs k.castSucc ∧
    R'.φs (Fin.cast (congrArg RadialRegion.N h) k).succ = R.φs k.succ := by
  cases h
  exact ⟨rfl, rfl⟩

namespace OriginalGlobalCellCover
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- Exact positively parametrized square-side presentation of an actual arc. -/
structure SquareArcPresentation (a : A.Arc) (p : ℤ × ℤ) (k : Fin (A.G.region p).N)
    (m c : ℝ) : Prop where
  /-- The actual cell is assigned to this square. -/
  region : A.regionOf a.1 = some p
  /-- The boundary coordinate increases along the base square. -/
  positive : 0 < m
  /-- Exact initial endpoint. -/
  start : m * (A.cell a.1).R.φs a.2.castSucc + c = (A.G.region p).φs k.castSucc
  /-- Exact final endpoint. -/
  stop : m * (A.cell a.1).R.φs a.2.succ + c = (A.G.region p).φs k.succ
  /-- Actual j-evaluation along the whole arc. -/
  read : ∀ t ∈ (A.cell a.1).R.arcIcc a.2,
    originalPlaceEval N ℂ ((A.cell a.1).bdry t) (jOver N ℂ) = (A.G.region p).loop (m * t + c)
  /-- The actual arc covers the full planar side. -/
  lies : LiesOver (A.arcPlaces a) ((A.G.region p).arcSet k)

/-- Exact negatively parametrized outer-side presentation of an actual pole arc. -/
structure ExteriorArcPresentation (a : A.Arc) (k : Fin A.W.R.N) (m c : ℝ) : Prop where
  /-- The actual cell is assigned to the exterior. -/
  region : A.regionOf a.1 = none
  /-- The boundary coordinate decreases along the outer perimeter. -/
  negative : m < 0
  /-- Reversed initial endpoint. -/
  start : m * (A.cell a.1).R.φs a.2.castSucc + c = A.W.R.φs k.succ
  /-- Reversed final endpoint. -/
  stop : m * (A.cell a.1).R.φs a.2.succ + c = A.W.R.φs k.castSucc
  /-- Actual j-evaluation along the whole arc. -/
  read : ∀ t ∈ (A.cell a.1).R.arcIcc a.2,
    originalPlaceEval N ℂ ((A.cell a.1).bdry t) (jOver N ℂ) = A.W.R.loop (m * t + c)
  /-- The actual arc covers the full outer side. -/
  lies : LiesOver (A.arcPlaces a) (A.W.R.arcSet k)

end OriginalGlobalCellCover
end
end Dubon2026.SourceFunctionField.CellGeometry
