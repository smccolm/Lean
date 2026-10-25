import Dubon2026.SourceOriginalWeilCoverMeromorphicQuotientArcValues
import Dubon2026.SourceRadialMeromorphicJumpPeriodClosure

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The actual normalized logarithmic jumps are reduced to complementary integer
cycle integrals and literal cell residue periods. The proved actual boundary
calculus supplies the additive arc-value clauses; the constructed polygon
and fundamental cycles supply both required circulation decompositions. -/
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



open RadialArcPeriods RadialDissectionTrees

theorem cover_meromorphic_jump_mem_sup {d : ℕ} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      Function.Injective D.vert → ∀ (S : Finset (Place ℂ EE)) (θ : Fin d → Ω[EE⁄ℂ]),
      (∀ r v, v ∉ S → 0 ≤ v.ordDifferential (θ r)) →
      RadialMeromorphicPeriods.PolePos D S →
      ∀ {V : D.ιC → Set ℂ} {Ψ : Fin d → D.ιC → ℂ → ℂ},
      RadialMeromorphicPeriods.RegPrimData D S
        (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ {J : D.ιE → Fin d → ℂ}, RadialMeromorphicPeriods.IsJumpH D
        (coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ) J →
      ∀ (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ),
        (∀ e ∈ Ts, J e = 0) → FundamentalCycleSystem D T Z →
        RadialDissectionPolygon.PolygonWordConclusion D Ts →
      let residue : Place ℂ EE → Fin d → ℂ := fun v r =>
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff (θ r))
      ∀ e, J e ∈ AddSubgroup.closure
        ((RadialDissectionPeriods.zv Z (fun e r =>
          coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (θ r) e)) ''
          ((T ∪ Ts)ᶜ : Finset D.ιE)) ⊔ RadialMeromorphicPeriods.Λres D S residue := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD hinj S θ hθ hS V Ψ hP J hJ T Ts Z hJ0 hZ hW
  let residue : Place ℂ EE → Fin d → ℂ := fun v r =>
    v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))
  let I : D.ιE → Fin d → ℂ := fun e r =>
    coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (θ r) e
  have hAV := cover_meromorphic_quotient_arc_values N n radicand baseDivisor hRadicand hOrders
    D hD hinj S θ hθ hS hP hJ
  have hi : FlowDecomp ℤ D T Z := RadialDissectionPeriods.integer_decomposition_of_lift D hZ.2.2.2
  have hq : FlowDecomp ((Fin d → ℂ) ⧸ RadialMeromorphicPeriods.Λres D S residue) D T Z :=
    RadialMeromorphicPeriods.residue_quotient_decomposition_of_lift D S residue hZ.2.2.2
  exact fun e => RadialMeromorphicPeriods.jump_mem_sup S residue Ψ I hAV hJ0 hi hq hW e

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
