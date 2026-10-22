import Dubon2026.SourceOriginalAnalyticJMultiplicity
import Dubon2026.SourceOriginalRegularCoefficientOrders

/-! DUB-17/18 -> regular-differential cusp forms -> local analytic regularity.
The native analytic derivative-order identity and the proved normalized
original j-order give the exact order of the actual analytic derivative.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve
open scoped Topology

theorem meromorphicOrderAt_deriv_jf_add_one (τ : ℍ) :
    meromorphicOrderAt (deriv (JMultiplicity.jf ∘ ofComplex)) (τ : ℂ) + 1 =
      meromorphicOrderAt (fun z : ℂ => JMultiplicity.jf (ofComplex z) - JMultiplicity.jf τ)
        (τ : ℂ) := by
  have ha := JMultiplicity.analyticAt_comp JMultiplicity.mdifferentiable_jf τ
  have hd := ha.deriv
  have hs : AnalyticAt ℂ (fun z : ℂ => JMultiplicity.jf (ofComplex z) - JMultiplicity.jf τ)
      (τ : ℂ) := ha.sub (analyticAt_const (v := JMultiplicity.jf τ))
  rw [hd.meromorphicOrderAt_eq, hs.meromorphicOrderAt_eq]
  have h := JMultiplicity.order_deriv_add_one τ
  rw [← h]
  exact (ENat.map_add (Nat.castAddMonoidHom ℤ) _ 1).symm

theorem original_analytic_derivative_order (N : ℕ) [NeZero N] (τ : ℍ) :
    meromorphicOrderAt (deriv (JMultiplicity.jf ∘ ofComplex)) (τ : ℂ) =
      (((originalAnalyticRamification N τ : ℤ) * (originalAnalyticPlace N τ).ord
        (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) - 1 : ℤ) :
          WithTop ℤ) := by
  have hx : jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ) ≠ 0 :=
    Place.transcendental_sub_algebraMap_ne_zero (transcendental_jOver N ℂ) _
  have h := meromorphicOrderAt_deriv_jf_add_one τ
  rw [← originalAnalyticOrder_j_sub N τ, originalAnalyticPlace_order N τ _ hx] at h
  cases ho : meromorphicOrderAt (deriv (JMultiplicity.jf ∘ ofComplex)) (τ : ℂ) with
  | top => simp only [ho, top_add, WithTop.top_ne_coe] at h
  | coe n =>
    rw [ho] at h
    have hi : n + 1 = (originalAnalyticRamification N τ : ℤ) * (originalAnalyticPlace N τ).ord
        (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) := by
      exact_mod_cast h
    congr 1
    omega

end
end Dubon2026.SourceFunctionField
