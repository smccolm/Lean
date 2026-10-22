import Dubon2026.SourceOriginalRealizationGermHom
import Dubon2026.SourceAnalyticJTransformation

/-! DUB-17/18 -> regular-differential cusp forms -> cusp decay.
Coefficients in the actual inverse-j chart evaluate on analytic germs as
the same scalar polynomials in the analytic inverse j. This is the exact
coefficient bridge needed to transfer the proved monic integrality relation.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter Polynomial
open scoped Topology

theorem originalRealizeGerm_j_inv (N : ℕ) [NeZero N] (τ : ℍ) :
    originalRealizeGerm N τ (jOver N ℂ)⁻¹ =
      ((fun z : ℂ => (JMultiplicity.jf (ofComplex z))⁻¹) : Germ (𝓝[≠] (τ : ℂ)) ℂ) := by
  have hj : jOver N ℂ ≠ 0 := by
    intro he
    exact transcendental_jOver N ℂ (he ▸ isAlgebraic_zero)
  apply Germ.coe_eq.mpr
  filter_upwards [original_realize_inv_eventuallyEq N (jOver N ℂ) hj τ] with z hz
  rw [hz, realize_jOver]
  rfl

theorem originalRealizeGerm_aeval_inverse_j (N : ℕ) [NeZero N] (τ : ℍ) (p : ℂ[X]) :
    originalRealizeGerm N τ (aeval (jOver N ℂ)⁻¹ p) =
      ((fun z : ℂ => p.eval ((JMultiplicity.jf (ofComplex z))⁻¹)) : Germ (𝓝[≠] (τ : ℂ)) ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => Polynomial.eval_add.symm
  | monomial n a =>
    rw [aeval_monomial, map_mul, map_pow,
      originalRealizeGerm_algebraMap, originalRealizeGerm_j_inv]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => Polynomial.eval_monomial.symm

end
end Dubon2026.SourceFunctionField
