import Dubon2026.SourceOriginalWeilCoverMeromorphicBoundaryValues

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The actual boundary reading increments by its literal cell residue period. -/
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



open scoped Real

theorem cover_meromorphic_boundary_period {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (S : Finset (Place ℂ EE))
      (θ : R → Ω[EE⁄ℂ]) (Ψ : R → D.ιC → ℂ → ℂ) (C : D.ιC) (s : ℝ),
      coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ C (s + 2 * π) =
        coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ C s +
          (2 * π * Complex.I) • RadialMeromorphicPeriods.ρ D S (fun v r =>
            v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
              (v.uniformizer * v.differentialCoeff (θ r))) C := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D S θ Ψ C s
  exact RadialMeromorphicPeriods.hfun_add_two_pi S _ Ψ C s

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
