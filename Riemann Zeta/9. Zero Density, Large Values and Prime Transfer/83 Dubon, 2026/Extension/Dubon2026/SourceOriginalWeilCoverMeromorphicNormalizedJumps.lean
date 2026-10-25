import Dubon2026.SourceOriginalWeilCoverMeromorphicBoundaryJumps
import Dubon2026.SourceRadialMeromorphicNormalizedJumps

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Construct actual paired jumps, then apply the proved exact dual-tree transport.
Only primitive constants change; domains and coefficients remain the same. -/
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



open IntegerEdgeChains RadialDissectionTrees

theorem cover_normalize_meromorphic_primitives {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ])
        {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RadialMeromorphicPeriods.RegPrimData D S
        (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ (Ts : Finset D.ιE), IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts →
      ∀ (_ : D.ιC), ∃ (Ψ' : R → D.ιC → ℂ → ℂ) (J : D.ιE → R → ℂ),
        RadialMeromorphicPeriods.RegPrimData D S
          (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ' ∧
        RadialMeromorphicPeriods.IsJumpH D
          (coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ') J ∧
        ∀ e ∈ Ts, J e = 0 := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ V Ψ hP Ts hTs C₀
  obtain ⟨J, hJ⟩ := exists_cover_meromorphic_boundary_jumps N n radicand baseDivisor hRadicand hOrders D hD S θ hP
  exact RadialMeromorphicPeriods.normalize_regPrimData S _ hP hJ Ts hTs C₀

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
