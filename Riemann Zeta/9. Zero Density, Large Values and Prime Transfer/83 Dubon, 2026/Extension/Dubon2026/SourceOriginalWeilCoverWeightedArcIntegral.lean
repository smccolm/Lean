import Dubon2026.SourceOriginalWeilCoverBoundaryCoefficient
import Dubon2026.SourceCellArcIntegralExtension

/-! DUB-17/18 -> cover Abel converse -> bilinear/third-kind reciprocity ->
weighted paired-edge cancellation. Reuse native continuous arc extension,
derivative uniqueness and reversed C1 integration on the actual cover cells.
The actual dissection supplies forward coordinate and paired-overlap inputs. -/
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

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

theorem cover_weighted_arc_integral_extension :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N) (θ : Ω[EE⁄ℂ]),
      (∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) →
      ∀ (W : ℝ → ℂ), ContinuousOn W (C.R.arcIcc k) →
      IntervalIntegrable (fun s => W s * BI C θ s) volume (C.R.φs k.castSucc) (C.R.φs k.succ) ∧
        (∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), W s * BI C θ s) =
          ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ),
            W s * (CF C.ζ θ (C.R.loop s) * C.R.loopDerivOnArc k s) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C hC k θ hθ W hW
  apply arc_integral_eq_of_continuous_extension (C.R.hmono Fin.castSucc_lt_succ).le
    (hW.mul ((cover_continuousOn_boundary_coefficient N n radicand baseDivisor hRadicand hOrders C hC k θ hθ).mul
      (C.R.continuous_loopDerivOnArc k).continuousOn))
  intro s hs
  change W s * (CF C.ζ θ (C.R.loop s) * C.R.loop' s) = _
  rw [C.R.loop'_eq_loopDerivOnArc k hs]
  rfl

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
