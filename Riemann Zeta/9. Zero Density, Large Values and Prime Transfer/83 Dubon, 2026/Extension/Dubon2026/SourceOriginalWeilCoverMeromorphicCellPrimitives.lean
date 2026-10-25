import Dubon2026.SourceOriginalWeilCoverRegularizedCoefficient
import Dubon2026.SourceRadialMeromorphicCellPrimitives

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse ->
meromorphic loop generation. Construct common cell domains and primitives
from the actual residue-subtracted coefficients. Analyticity is proved by
the preceding actual cover theorem, not an assumption of this consumer. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
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


theorem exists_cover_regPrimData {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
        (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
        RadialMeromorphicPeriods.PolePos D S →
        ∃ (V : D.ιC → Set ℂ) (Ψ : R → D.ιC → ℂ → ℂ),
          RadialMeromorphicPeriods.RegPrimData D S
            (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS
  apply RadialMeromorphicPeriods.exists_regPrimData D S _ hS
  exact fun r C w hw =>
    cover_analyticAt_regCoeff N n radicand baseDivisor hRadicand hOrders D hD S θ hθ hS r C hw

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
