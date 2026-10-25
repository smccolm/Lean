import Dubon2026.SourceOriginalWeilCoverMeromorphicCellPrimitives
import Dubon2026.SourceRadialMeromorphicBoundaryValues
import Dubon2026.SourceOriginalWeilCoverBoundaryCoefficient

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The restored logarithmic boundary primitive has exactly the actual cover
differential integrand as its derivative. No formal coefficient is substituted. -/
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


/-- Boundary reading of the actual residue-subtracted primitive plus its residue logarithm. -/
def coverMeromorphicBoundaryValue {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → Finset (Place ℂ EE) →
      (R → Ω[EE⁄ℂ]) → (R → D.ιC → ℂ → ℂ) → D.ιC → ℝ → R → ℂ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D S θ Ψ
  exact RadialMeromorphicPeriods.hfun S (fun v r =>
    v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))) Ψ

theorem cover_hasDerivAt_meromorphicBoundary {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (S : Finset (Place ℂ EE))
      (θ : R → Ω[EE⁄ℂ]) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RadialMeromorphicPeriods.RegPrimData D S
        (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ (r : R) (C : D.ιC) (k : Fin (D.cell C).R.N) {s : ℝ},
        s ∈ Ioo ((D.cell C).R.φs k.castSucc) ((D.cell C).R.φs k.succ) →
        HasDerivAt (fun s => coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ C s r)
          (coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders (D.cell C) (θ r) s) s := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D S θ V Ψ hP r C k s hs
  exact RadialMeromorphicPeriods.hasDerivAt_hfun S _
    (fun r C => CF (D.cell C).ζ (θ r)) hP r C k hs

theorem cover_continuous_meromorphicBoundary {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (S : Finset (Place ℂ EE))
      (θ : R → Ω[EE⁄ℂ]) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RadialMeromorphicPeriods.RegPrimData D S
        (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ (r : R) (C : D.ιC),
        Continuous (fun s => coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ C s r) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D S θ V Ψ hP r C
  exact RadialMeromorphicPeriods.continuous_hfun S _
    (fun r C => CF (D.cell C).ζ (θ r)) hP r C

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
