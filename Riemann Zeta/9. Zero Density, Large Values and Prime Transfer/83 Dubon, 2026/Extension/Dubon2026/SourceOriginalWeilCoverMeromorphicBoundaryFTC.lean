import Dubon2026.SourceOriginalWeilCoverMeromorphicBoundaryValues
import Dubon2026.SourceOriginalWeilCoverWeightedResidueJumpSum
import Dubon2026.SourceOriginalWeilCoverPrimitiveArcIntegral

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Actual marked-pole geometry proves regularity on every boundary arc. Existing
arc integrability and FTC identify each logarithmic primitive increment with
the actual cover differential integral. -/
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


theorem cover_meromorphic_boundary_regular {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (S : Finset (Place ℂ EE))
      (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, v ∉ S → 0 ≤ v.ordDifferential (θ r)) →
      RadialMeromorphicPeriods.PolePos D S →
      ∀ (r : R) (C : D.ιC) (k : Fin (D.cell C).R.N) {s : ℝ}, s ∈ (D.cell C).R.arcIcc k →
        0 ≤ ((D.cell C).bdry s).ordDifferential (θ r) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D S θ hθ hS r C k s hs
  apply cover_regular_on_skeleton N n radicand baseDivisor hRadicand hOrders D S
    (fun v hv => ⟨_, (hS.hd5 v hv).choose_spec.1⟩) (θ r) (hθ r)
  exact D.bdry_mem_skeleton C k hs

theorem cover_meromorphic_boundary_ftc {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, v ∉ S → 0 ≤ v.ordDifferential (θ r)) →
      RadialMeromorphicPeriods.PolePos D S →
      ∀ {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RadialMeromorphicPeriods.RegPrimData D S
        (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ (r : R) (C : D.ιC) (k : Fin (D.cell C).R.N),
        (∫ s in ((D.cell C).R.φs k.castSucc)..((D.cell C).R.φs k.succ),
          coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders (D.cell C) (θ r) s) =
        coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ C ((D.cell C).R.φs k.succ) r -
          coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ C ((D.cell C).R.φs k.castSucc) r := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS V Ψ hP r C k
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    ((D.cell C).R.hmono (Fin.castSucc_lt_succ (i := k))).le
    (cover_continuous_meromorphicBoundary N n radicand baseDivisor hRadicand hOrders D S θ hP r C).continuousOn
  · exact fun s hs => cover_hasDerivAt_meromorphicBoundary N n radicand baseDivisor hRadicand hOrders D S θ hP r C k hs
  · exact cover_arc_integrable N n radicand baseDivisor hRadicand hOrders (D.cell C) (hD C) k (θ r)
      (fun s hs => cover_meromorphic_boundary_regular N n radicand baseDivisor hRadicand hOrders D S θ hθ hS r C k hs)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
