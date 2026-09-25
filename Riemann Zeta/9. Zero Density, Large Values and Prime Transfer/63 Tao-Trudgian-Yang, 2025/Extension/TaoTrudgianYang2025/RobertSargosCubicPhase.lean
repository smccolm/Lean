import TaoTrudgianYang2025.FiniteSmoothTaylor
import TaoTrudgianYang2025.RobertSargosFourthGeometry

/-! Exact cubic expansion of the actual mixed symmetric difference.
The r-cubic term is a constant in the three inner variables; its
negative sign is retained in the exact identity. -/

noncomputable section
open scoped ContDiff
namespace TaoTrudgianYang2025

def robertSargosSymmetricDifference (f : ℝ → ℝ) (m h : ℝ) : ℝ :=
  f (m+h)-f (m-h)

def robertSargosCubicRemainder (f : ℝ → ℝ) (m y : ℝ) : ℝ :=
  f (m+y)-finiteTaylorPolynomial f 3 m (m+y)

def robertSargosMixedRemainder (f : ℝ → ℝ) (m r q h n : ℝ) : ℝ :=
  robertSargosCubicRemainder f m (n+q+h)-
    robertSargosCubicRemainder f m (n+q-h)-
    robertSargosCubicRemainder f m (n+h+r)+
    robertSargosCubicRemainder f m (n-h-r)

theorem robertSargos_cubic_polynomial (f : ℝ → ℝ) (m y : ℝ) :
    finiteTaylorPolynomial f 3 m (m+y) =
      f m+deriv f m*y+iteratedDeriv 2 f m*y^2/2+
        iteratedDeriv 3 f m*y^3/6 := by
  norm_num [finiteTaylorPolynomial,taylor_within_apply,Finset.sum_range_succ,
    iteratedDerivWithin_univ,iteratedDeriv_zero,iteratedDeriv_one,smul_eq_mul]
  ring

theorem robertSargos_mixed_taylor_identity (f : ℝ → ℝ) (m r q h n : ℝ) :
    robertSargosSymmetricDifference f (m+n+q) h-
      robertSargosSymmetricDifference f (m+n) (h+r) =
      -2*r*deriv f m+2*iteratedDeriv 2 f m*robertSargosLinear (-r) q h n+
        iteratedDeriv 3 f m*robertSargosTaylorQuadratic r q h n-
        r^3/3*iteratedDeriv 3 f m+robertSargosMixedRemainder f m r q h n := by
  unfold robertSargosSymmetricDifference robertSargosMixedRemainder
    robertSargosCubicRemainder
  simp only [robertSargos_cubic_polynomial,robertSargosLinear,robertSargosTaylorQuadratic]
  rw [show m+n+q+h = m+(n+q+h) by ring,
    show m+n+q-h = m+(n+q-h) by ring,
    show m+n+(h+r) = m+(n+h+r) by ring,
    show m+n-(h+r) = m+(n-h-r) by ring]
  ring

theorem abs_robertSargosCubicRemainder_le {f : ℝ → ℝ} {m y B : ℝ}
    (hf : ∀ x ∈ Set.uIcc m (m+y), ContDiffAt ℝ 4 f x)
    (hb : ∀ x ∈ Set.uIcc m (m+y), |iteratedDeriv 4 f x| ≤ B) :
    |robertSargosCubicRemainder f m y| ≤ B*|y|^4/24 := by
  have ht := abs_finiteTaylorPolynomial_remainder_le_finite
    (f := f) (a := m) (x := m+y) (M := B) 3 hf hb
  simpa only [robertSargosCubicRemainder,add_sub_cancel_left] using ht

end TaoTrudgianYang2025

