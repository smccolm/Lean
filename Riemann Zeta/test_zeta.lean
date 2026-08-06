import Mathlib
import RiemannZeta.GuthMaynard.ZeroCount

open Complex

namespace RiemannZeta.GuthMaynard

-- We decompose zeta_lower_bound_native into a simpler Euler product bound lemma

/-- Euler product implies the zeta function is bounded away from zero on Re(s) = 2. -/
lemma euler_product_lower_bound_2 (y : ℝ) :
  (0.6 : ℝ) ≤ ‖riemannZeta (2 + I * (y : ℂ))‖ := by
  sorry

theorem zeta_lower_bound_proof : ZetaLowerBoundProp := by
  use 0.6
  constructor
  · norm_num
  · intro T t hT ht
    exact euler_product_lower_bound_2 (t + 1/2)

end RiemannZeta.GuthMaynard
