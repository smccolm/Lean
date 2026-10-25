import Dubon2026.SourceOriginalWeilCoverSkeletonIntegrals

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

theorem exists_cover_fundamental_cycle_loop :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (T : Finset D.ιE)
      (Z : D.ιE → D.ιE → ℤ), FundamentalCycleSystem D T Z →
      IsTree (hdΓ D) (tlΓ D) T → IsWalkConn (hdΓ D) (tlΓ D) T → ∀ j : D.ιE,
      ∃ γ : Path (D.vert (D.ends j).1) (D.vert (D.ends j).1),
        (∀ t, γ t ∈ D.skeleton) ∧
        ∀ θ : Ω[EE⁄ℂ], (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
          (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ γ g) ∧
          pathIntegral N n radicand baseDivisor hRadicand hOrders θ γ =
            ∑ e, (Z j e : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders θ (edgePath D e) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D T Z hZ hT hw j
  obtain ⟨γ, hγ, hint⟩ := RadialEdgePaths.exists_fundamental_cycle_loop D
    hZ.1 hZ.2.1 hZ.2.2.1 hT hw j
  refine ⟨γ, hγ, fun θ hθ => ⟨?_, ?_⟩⟩
  · exact exists_isPrimitiveAlong_of_coeff_mem N n radicand baseDivisor hRadicand hOrders θ γ
      (fun t => (γ t).mem_of_ord_nonneg (hθ _ (hγ t)))
  · exact hint (fun {_ _} p => pathIntegral N n radicand baseDivisor hRadicand hOrders θ p)
      (cover_skeleton_integral N n radicand baseDivisor hRadicand hOrders D θ hθ)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
