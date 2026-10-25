import Dubon2026.SourceRadialMeromorphicQuotientArcValues
import Dubon2026.SourceOriginalWeilCoverMeromorphicBoundaryFTC
import Dubon2026.SourceOriginalWeilCoverEdgePathIntegral

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Supply the additive quotient polygon with actual logarithmic readings and
actual edge integrals. FTC gives the positive increment; the already proved
paired jumps give the negative sign without another arc substitution proof. -/
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



theorem cover_meromorphic_quotient_arc_values {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      Function.Injective D.vert → ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, v ∉ S → 0 ≤ v.ordDifferential (θ r)) →
      RadialMeromorphicPeriods.PolePos D S →
      ∀ {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RadialMeromorphicPeriods.RegPrimData D S
        (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ {J : D.ιE → R → ℂ}, RadialMeromorphicPeriods.IsJumpH D
        (coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ) J →
      let residue : Place ℂ EE → R → ℂ := fun v r =>
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff (θ r))
      RadialArcPeriods.ArcValues D (RadialMeromorphicPeriods.Aq S residue Ψ)
        (RadialMeromorphicPeriods.Bq S residue Ψ)
        (RadialMeromorphicPeriods.Iq S residue
          (fun e r => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (θ r) e))
        (fun e => QuotientAddGroup.mk' _ (J e))
        (fun C => DissectionTrees.nxt (N := (D.cell C).R.N)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD hinj S θ hθ hS V Ψ hP J hJ
  apply RadialMeromorphicPeriods.arcValuesH S _ Ψ hinj hJ
  intro e
  funext r
  exact (cover_meromorphic_boundary_ftc N n radicand baseDivisor hRadicand hOrders
    D hD S θ hθ hS hP r (D.arcOf (e, true)).1 (D.arcOf (e, true)).2).symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
