import Dubon2026.SourceOriginalAnalyticDerivativeOrder

/-! DUB-17/18 -> cusp-form lower dimension -> regular-differential realization.
Pulling x D(j) back at the original analytic place has order at least e-1.
The coefficient-order bound and exact analytic derivative order derive
local boundedness, which feeds the existing removable-singularity quotient
extension. Cusp decay is a separate remaining obligation.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve KaehlerDifferential Filter
open scoped Topology

theorem original_regular_analytic_differential_order (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) (τ : ℍ) :
    (((originalAnalyticRamification N τ : ℤ) - 1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt
        ((fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) *
          deriv (JMultiplicity.jf ∘ ofComplex)) (τ : ℂ) := by
  have ha := JMultiplicity.analyticAt_comp JMultiplicity.mdifferentiable_jf τ
  rw [meromorphicOrderAt_mul (meromorphicAt_original_realize N x τ) ha.deriv.meromorphicAt]
  change _ ≤ originalAnalyticOrder N τ x + _
  rw [originalAnalyticPlace_order N τ x hx, original_analytic_derivative_order N τ,
    ← WithTop.coe_add, WithTop.coe_le_coe]
  have h := original_regular_coefficient_order_bound N x hx hreg (originalAnalyticPlace N τ)
    (JMultiplicity.jf τ) (originalAnalyticPlace_j_sub_pos N τ)
  have he : (0 : ℤ) ≤ originalAnalyticRamification N τ := Int.natCast_nonneg _
  nlinarith [mul_nonneg he (sub_nonneg.mpr h)]

theorem original_regular_analytic_differential_bounded (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) (τ : ℍ) :
    ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      ‖realize N (x : LaurentSeries ℂ) (ofComplex z) *
        deriv (JMultiplicity.jf ∘ ofComplex) z‖ ≤ M := by
  have ha := JMultiplicity.analyticAt_comp JMultiplicity.mdifferentiable_jf τ
  have hmer := (meromorphicAt_original_realize N x τ).mul ha.deriv.meromorphicAt
  have he : (0 : ℤ) ≤ (originalAnalyticRamification N τ : ℤ) - 1 := by
    have := originalAnalyticRamification_pos N τ
    omega
  have hord : 0 ≤ meromorphicOrderAt
      ((fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) *
        deriv (JMultiplicity.jf ∘ ofComplex)) (τ : ℂ) :=
    (show (0 : WithTop ℤ) ≤ (((originalAnalyticRamification N τ : ℤ) - 1 : ℤ) : WithTop ℤ)
      by exact_mod_cast he).trans (original_regular_analytic_differential_order N x hx hreg τ)
  obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer).mpr hord
  exact ⟨‖c‖ + 1, (hc.norm.eventually (eventually_le_nhds (by linarith : ‖c‖ < ‖c‖ + 1)))⟩

end
end Dubon2026.SourceFunctionField
