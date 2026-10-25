import Dubon2026.SourceOriginalWeilCoverCoordinatePrimitiveComparison
import Dubon2026.SourceRadialPolygonPrimitiveData

/-! DUB-17/18 -> cover Abel converse -> regular loop generation -> arbitrary
path-to-jump comparison. Reuse the actual cover coefficient pullback and native
uniqueness of analytic primitives. The original path-atlas argument is adapted
from the already proved original-curve modules and their documented FLT source.
All coordinate and regularity inputs are supplied by the actual dissection. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology
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


open CellGeometry

/-- The explicit local analytic data used in path comparison. The actual
consumer supplies these fields from the constructed cells and primitives. -/
def CoverPrimData {κ : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → (κ → Ω[EE⁄ℂ]) →
      (D.ιC → Set ℂ) → (κ → D.ιC → ℂ → ℂ) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D η V Ψ =>
    (∀ C Q, Q ∈ (D.cell C).ζ.source →
      AnalyticAt ℂ ((D.cell C).ζ ∘ PF Q) 0 ∧ deriv ((D.cell C).ζ ∘ PF Q) 0 ≠ 0) ∧
    (∀ C, IsOpen (V C)) ∧
    (∀ C, (D.cell C).R.K ⊆ V C) ∧
    (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (CF (D.cell C).ζ (η i) w) w) ∧
    (∀ i, η i ∈ regularDifferentials ℂ EE)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
