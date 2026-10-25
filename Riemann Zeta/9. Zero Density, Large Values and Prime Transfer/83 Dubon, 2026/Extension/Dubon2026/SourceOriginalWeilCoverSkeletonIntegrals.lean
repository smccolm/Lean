import Dubon2026.SourceRadialFundamentalCycleLoops
import Dubon2026.SourceOriginalWeilCoverRegularPathIntegralLaws

/-! DUB-17/18 -> actual cover Abel converse -> geometric loop integrals.
Every actual cover differential regular on the skeleton satisfies the three
elementary path laws used by the radial tree-walk proof. The inputs are the
proved cover regular-along-path integral laws, not global regularity. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set CellGeometry CellGeometry.RadialEdgePaths KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem cover_skeleton_integral :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (θ : Ω[EE⁄ℂ]),
      (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
      SkeletonIntegral D (fun {_ _} p => pathIntegral N n radicand baseDivisor hRadicand hOrders θ p) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D θ hθ
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    have he := pathIntegral_symm_of_coeff_mem N n radicand baseDivisor hRadicand hOrders
      (Path.refl P) (fun _ => P.mem_of_ord_nonneg (hθ P hP))
    change pathIntegral N n radicand baseDivisor hRadicand hOrders θ (Path.refl P) =
      -pathIntegral N n radicand baseDivisor hRadicand hOrders θ (Path.refl P) at he
    linear_combination (1 / 2 : ℂ) * he
  · intro P Q p hp
    exact pathIntegral_symm_of_coeff_mem N n radicand baseDivisor hRadicand hOrders p
      (fun t => (p t).mem_of_ord_nonneg (hθ _ (hp t)))
  · intro P Q R p q hp hq
    exact pathIntegral_trans_of_coeff_mem N n radicand baseDivisor hRadicand hOrders p q
      (fun t => (p t).mem_of_ord_nonneg (hθ _ (hp t)))
      (fun t => (q t).mem_of_ord_nonneg (hθ _ (hq t)))

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
