import Dubon2026.SourceOriginalAnalyticJValues
import Mathlib.Order.Filter.Germ.Basic

/-! DUB-17/18 -> regular-differential cusp forms -> analytic cusp decay.
The inverse-j integrality relation must hold for the actual analytic
quotient. Package the already proved germ identities as a ring homomorphism
so a finite monic polynomial relation transfers directly. This is used only
for that relation; no new abstract meromorphic-field construction is needed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology

/-- The proved analytic realization of the original field on a punctured germ. -/
def originalRealizeGerm (N : ℕ) [NeZero N] (τ : ℍ) :
    modularFunctionFieldOver N ℂ →+* Germ (𝓝[≠] (τ : ℂ)) ℂ where
  toFun x := ((fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) :
    Germ (𝓝[≠] (τ : ℂ)) ℂ)
  map_zero' := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => by
      simpa only [map_zero] using realize_algebraMap N 0 (ofComplex z)
  map_one' := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => by
      simpa only [map_one] using realize_algebraMap N 1 (ofComplex z)
  map_add' x y := Germ.coe_eq.mpr (original_realize_add_eventuallyEq N x y τ)
  map_mul' x y := Germ.coe_eq.mpr (original_realize_mul_eventuallyEq N x y τ)

theorem originalRealizeGerm_algebraMap (N : ℕ) [NeZero N] (τ : ℍ) (c : ℂ) :
    originalRealizeGerm N τ (algebraMap ℂ (modularFunctionFieldOver N ℂ) c) =
      ((fun _ : ℂ => c) : Germ (𝓝[≠] (τ : ℂ)) ℂ) := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun z => realize_algebraMap N c (ofComplex z)

theorem originalRealizeGerm_j (N : ℕ) [NeZero N] (τ : ℍ) :
    originalRealizeGerm N τ (jOver N ℂ) =
      ((fun z : ℂ => ModularForm.E₄ (ofComplex z) ^ 3 / ModularForm.discriminant (ofComplex z)) :
        Germ (𝓝[≠] (τ : ℂ)) ℂ) := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun z => realize_jOver N (ofComplex z)

theorem original_realize_inv_eventuallyEq (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0) (τ : ℍ) :
    (fun z : ℂ => realize N (x⁻¹ : modularFunctionFieldOver N ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => (realize N (x : LaurentSeries ℂ) (ofComplex z))⁻¹ := by
  have h := original_realize_mul_eventuallyEq N x⁻¹ x τ
  rw [inv_mul_cancel₀ hx] at h
  filter_upwards [h] with z hz
  have h1 : realize N ((1 : modularFunctionFieldOver N ℂ) : LaurentSeries ℂ) (ofComplex z) = 1 := by
    simpa only [map_one] using realize_algebraMap N 1 (ofComplex z)
  rw [Pi.mul_apply, h1] at hz
  exact eq_inv_of_mul_eq_one_left hz.symm

end
end Dubon2026.SourceFunctionField
