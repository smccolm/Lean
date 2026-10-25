import Dubon2026.SourceOriginalWeilCoverArcPathIntegral
import Dubon2026.SourceRadialDissectionEdgePaths

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
Define the literal oriented-edge integral from the actual cover coefficient.
The proved arc comparison supplies its path-integral identity, with primitives,
under regularity only along the actual edge. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open CellGeometry.RadialEdgePaths
open scoped Topology Interval
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders

/-- Coordinate integral along the actual positively oriented edge. -/
def coverEdgeIntegral :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → Ω[EE⁄ℂ] → D.ιE → ℂ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D θ e =>
    let C := D.cell (D.arcOf (e, true)).1
    let k := (D.arcOf (e, true)).2
    ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ),
      coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders C θ s

theorem cover_pathIntegral_edgePath :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source → AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧
        deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (e : D.ιE) (θ : Ω[EE⁄ℂ]),
      (∀ s ∈ (D.cell (D.arcOf (e, true)).1).R.arcIcc (D.arcOf (e, true)).2,
        0 ≤ ((D.cell (D.arcOf (e, true)).1).bdry s).ordDifferential θ) →
      (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (edgePath D e) g) ∧
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (edgePath D e) =
          coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD e θ hθ
  obtain ⟨⟨g, hg⟩, hi⟩ := cover_pathIntegral_arcPath N n radicand baseDivisor hRadicand hOrders
    (D.cell (D.arcOf (e, true)).1) (hD _) (D.arcOf (e, true)).2 θ hθ
  exact ⟨⟨g, hg⟩, hi⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
