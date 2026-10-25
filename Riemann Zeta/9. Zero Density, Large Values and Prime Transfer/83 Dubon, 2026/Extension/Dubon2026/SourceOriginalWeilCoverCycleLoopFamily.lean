import Dubon2026.SourceOriginalWeilCoverFundamentalLoops

/-! DUB-17/18 -> actual cover Abel converse -> geometric cycle integrals.
The integer fundamental cycles on the actual cover dissection are realized
by paths in its actual skeleton. The loop is chosen before the differential;
all regular-along-skeleton integral laws are discharged by proved cover laws.
The subsequent coordinate-integral comparison and period generation remain. -/
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
Existence is proved from the actual cycle system below. -/
def CoverCycleLoops :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → (D.ιE → D.ιE → ℤ) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D Z =>
    ∃ γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1),
      (∀ j t, γ j t ∈ D.skeleton) ∧
      ∀ j (θ : Ω[EE⁄ℂ]), (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
        (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (γ j) g) ∧
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) =
          ∑ e, (Z j e : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders θ (edgePath D e)

theorem cover_cycle_loops_of_cycle_system :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (T : Finset D.ιE)
      (Z : D.ιE → D.ιE → ℤ), FundamentalCycleSystem D T Z →
      IsTree (hdΓ D) (tlΓ D) T → IsWalkConn (hdΓ D) (tlΓ D) T →
      CoverCycleLoops N n radicand baseDivisor hRadicand hOrders D Z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D T Z hZ hT hw
  have h := fun j => exists_cover_fundamental_cycle_loop N n radicand baseDivisor hRadicand hOrders
    D T Z hZ hT hw j
  choose γ hγ using h
  exact ⟨γ, fun j => (hγ j).1, fun j => (hγ j).2⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
