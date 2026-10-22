import Dubon2026.SourceOriginalMeromorphicRealization

/-! DUB-17/18 -> normalized analytic places -> order on the actual
original function field. Its proved modular quotients make realization
preserve addition and multiplication on punctured germs, and constants
pointwise. These are the exact algebraic identities needed to turn native
meromorphic order into a valuation; no homomorphism premise is supplied.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter ModularRatios
open scoped MatrixGroups Topology Manifold

theorem realize_algebraMap (N : ℕ) (c : ℂ) (τ : ℍ) :
    realize N (algebraMap ℂ (LaurentSeries ℂ) c) τ = c := by
  have he : algebraMap ℂ (LaurentSeries ℂ) c * qL (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) =
      qL (c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)) := by
    rw [qL_one, mul_one, qL_const]
  rw [realize_eq_div N (c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)) 1 _ he τ (by simp)]
  simp

theorem original_realize_mul_eventuallyEq (N : ℕ) [NeZero N]
    (x y : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    (fun z : ℂ => realize N ((x * y : modularFunctionFieldOver N ℂ) : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) *
        fun z => realize N (y : LaurentSeries ℂ) (ofComplex z) := by
  obtain ⟨a, g, h, hh, hx⟩ := original_field_modular_ratio N x
  obtain ⟨b, g', h', hh', hy⟩ := original_field_modular_ratio N y
  change (x : LaurentSeries ℂ) * qL h = qL g at hx
  change (y : LaurentSeries ℂ) * qL h' = qL g' at hy
  have he : ((x * y : modularFunctionFieldOver N ℂ) : LaurentSeries ℂ) * qL (h.mul h') =
      qL (g.mul g') := by
    change (x : LaurentSeries ℂ) * (y : LaurentSeries ℂ) * qL (h.mul h') = _
    rw [qL_mul, qL_mul, ← hx, ← hy]
    ring
  filter_upwards [realize_eventuallyEq_of_ratio (g.mul g') (h.mul h') _
    (mul_ne_zero' h h' hh hh') he τ,
    realize_eventuallyEq_of_ratio g h x hh hx τ,
    realize_eventuallyEq_of_ratio g' h' y hh' hy τ] with z hxy hxe hye
  rw [Pi.mul_apply, hxy, hxe, hye]
  change (g (ofComplex z) * g' (ofComplex z)) / (h (ofComplex z) * h' (ofComplex z)) = _
  exact mul_div_mul_comm _ _ _ _

theorem original_realize_add_eventuallyEq (N : ℕ) [NeZero N]
    (x y : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    (fun z : ℂ => realize N ((x + y : modularFunctionFieldOver N ℂ) : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) +
        fun z => realize N (y : LaurentSeries ℂ) (ofComplex z) := by
  obtain ⟨a, g, h, hh, hx⟩ := original_field_modular_ratio N x
  obtain ⟨b, g', h', hh', hy⟩ := original_field_modular_ratio N y
  change (x : LaurentSeries ℂ) * qL h = qL g at hx
  change (y : LaurentSeries ℂ) * qL h' = qL g' at hy
  have he : ((x + y : modularFunctionFieldOver N ℂ) : LaurentSeries ℂ) * qL (h.mul h') =
      qL (g.mul h' + h.mul g') := by
    change ((x : LaurentSeries ℂ) + (y : LaurentSeries ℂ)) * qL (h.mul h') = _
    rw [qL_add, qL_mul, qL_mul, qL_mul, ← hx, ← hy]
    ring
  filter_upwards [realize_eventuallyEq_of_ratio (g.mul h' + h.mul g') (h.mul h') _
    (mul_ne_zero' h h' hh hh') he τ,
    realize_eventuallyEq_of_ratio g h x hh hx τ,
    realize_eventuallyEq_of_ratio g' h' y hh' hy τ,
    eventually_ne_zero_ofComplex h hh τ,
    eventually_ne_zero_ofComplex h' hh' τ] with z hxy hxe hye hz hz'
  rw [Pi.add_apply, hxy, hxe, hye]
  change (g (ofComplex z) * h' (ofComplex z) + h (ofComplex z) * g' (ofComplex z)) /
    (h (ofComplex z) * h' (ofComplex z)) = _
  rw [div_add_div _ _ hz hz']

end
end Dubon2026.SourceFunctionField
