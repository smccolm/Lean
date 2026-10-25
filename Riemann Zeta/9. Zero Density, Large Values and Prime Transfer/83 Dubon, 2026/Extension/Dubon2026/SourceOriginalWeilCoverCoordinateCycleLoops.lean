import Dubon2026.SourceOriginalWeilCoverCycleLoopFamily
import Dubon2026.SourceOriginalWeilCoverEdgePathIntegral

/-! DUB-17/18 -> actual cover Abel converse -> geometric cycle integrals.
The integer fundamental cycles on the actual cover dissection are realized
by paths in its actual skeleton. The loop is chosen before the differential;
all regular-along-skeleton integral laws are discharged by proved cover laws.
The proved edge comparison now gives the coordinate-integral formula on
the same loops, uniformly for all differentials regular on the skeleton. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set CellGeometry CellGeometry.RadialEdgePaths KaehlerDifferential
open CellGeometry.IntegerEdgeChains CellGeometry.RadialDissectionTrees
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

/-- Actual loops and their integral identities for all skeleton-regular differentials.
The coordinate formula is derived from the actual cycle loops below. -/
def CoverCoordinateCycleLoops :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → (D.ιE → D.ιE → ℤ) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D Z =>
    ∃ γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1),
      (∀ j t, γ j t ∈ D.skeleton) ∧
      ∀ j (θ : Ω[EE⁄ℂ]), (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
        (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (γ j) g) ∧
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) =
          ∑ e, (Z j e : ℂ) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e

theorem cover_coordinate_cycle_loops :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
        deriv ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) →
      ∀ Z : D.ιE → D.ιE → ℤ,
      CoverCycleLoops N n radicand baseDivisor hRadicand hOrders D Z →
      CoverCoordinateCycleLoops N n radicand baseDivisor hRadicand hOrders D Z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD Z hloops
  obtain ⟨γ, hγ, hint⟩ := hloops
  refine ⟨γ, hγ, fun j θ hθ => ⟨(hint j θ hθ).1, ?_⟩⟩
  rw [(hint j θ hθ).2]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  apply (cover_pathIntegral_edgePath N n radicand baseDivisor hRadicand hOrders D hD e θ ?_).2
  intro s hs
  apply hθ
  exact mem_iUnion.2 ⟨D.arcOf (e, true), ⟨_, ⟨s, hs, rfl⟩, rfl⟩⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
