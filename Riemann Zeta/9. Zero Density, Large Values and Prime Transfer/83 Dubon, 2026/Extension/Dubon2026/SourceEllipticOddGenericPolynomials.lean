import Dubon2026.SourceEllipticOddNormCoordinates
import Dubon2026.SourceEllipticRationalTranscendence

/-! The already proved odd-quotient numerator/denominator at a transcendental coordinate.
These comparisons discharge nonconstancy of the actual quotient pullback rather
than assuming it. The quotient equation and finite separable degree remain open
on the DUB-17/18 cyclic-subgroup root interpretation chain. -/

open Polynomial Finset

namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

variable {F L : Type*} [Field F] [Field L]
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → F)

omit [DecidableEq ι] in
/-- The actual kernel denominator commutes with scalar extension. -/
theorem hP_map (f : F →+* L) : (hP S x).map f = hP S (fun i => f (x i)) := by
  simp [hP, Polynomial.map_prod]

/-- The actual cleared quotient numerator commutes with scalar extension. -/
theorem AP_map (f : F →+* L) :
    (AP S x t u).map f = AP S (fun i => f (x i)) (fun i => f (t i)) (fun i => f (u i)) := by
  simp [AP, hP_map, Polynomial.map_sum, Polynomial.map_prod]

variable [Algebra F L] {z : L}

/-- The explicit quotient numerator over its squared kernel denominator is transcendental. -/
theorem transcendental_AP_div (hz : Transcendental F z) :
    Transcendental F (aeval z (AP S x t u) / aeval z (hP S x) ^ 2) := by
  have hdeg : (hP S x ^ 2).natDegree < (AP S x t u).natDegree := by
    rw [(hP_monic S x).natDegree_pow, natDegree_hP, natDegree_AP]
    omega
  simpa only [map_pow] using
    Dubon2026.SourceEllipticFunctionField.transcendental_aeval_div_of_natDegree_lt hz
      ((hP_monic S x).pow 2).ne_zero hdeg

/-- This rational function is exactly the original finite quotient-coordinate sum. -/
theorem aeval_AP_div_eq_Xv (hz : Transcendental F z) :
    aeval z (AP S x t u) / aeval z (hP S x) ^ 2 =
      Xv S (fun i => algebraMap F L (x i)) (fun i => algebraMap F L (t i))
        (fun i => algebraMap F L (u i)) z := by
  have hv : ∀ i ∈ S, z ≠ algebraMap F L (x i) := by
    intro i _ he
    exact hz (he ▸ isAlgebraic_algebraMap (x i))
  simp only [aeval_def, eval₂_eq_eval_map, hP_map, AP_map]
  rw [AP_eval S _ _ _ z hv]
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (hP_eval_ne_zero S _ z hv))

end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
