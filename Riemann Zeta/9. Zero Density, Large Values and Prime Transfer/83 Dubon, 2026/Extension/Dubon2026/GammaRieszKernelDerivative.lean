import Dubon2026.GammaRieszWeightedConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Actual derivatives of the conditionally convergent Riesz Gamma kernels -/

namespace Dubon2026

open Complex Set Filter
open scoped Topology

noncomputable section

/-- The adjacent-order derivative identity passes through the genuine compact-uniform cutoff limit. -/
theorem hasDerivAt_gammaRieszWeightedKernel {k r c x : ℝ} (hk : 2 ≤ k)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ((y ^ r : ℝ) : ℂ) * gammaRieszKernel k r (c * y))
      (((x ^ (r - 1) : ℝ) : ℂ) * gammaRieszKernel k (r - 1) (c * x)) x := by
  have hu := tendstoUniformlyOn_gammaRieszWeightedCutoff hk
    (by linarith : 0 ≤ r - 1) (by linarith : r - 1 ≤ 2) hc
    (by linarith : 0 < x / 2) (by linarith : x / 2 ≤ 3 * x / 2)
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hu.mono Ioo_subset_Icc_self)
    (f := fun T y : ℝ => ((y ^ r : ℝ) : ℂ) * gammaRieszVerticalCutoff k r (c * y) (3 / 8) T)
  · exact Eventually.of_forall fun T y hy => hasDerivAt_gammaRieszWeightedCutoff hk hr1 hc (by linarith [hy.1]) T
  · intro y hy
    exact (tendsto_gammaRieszVerticalCutoff hk (by linarith) hr2
      (mul_pos hc (by linarith [hy.1]))
      (by unfold gammaRieszLine; linarith : gammaRieszLine r ≤ 3 / 8) (le_refl (3 / 8 : ℝ))).const_mul _
  · exact ⟨by linarith, by linarith⟩

/-- The derivative of the actual weighted order-one kernel is exactly the order-zero kernel. -/
theorem hasDerivAt_gammaRieszKernel_one {k c x : ℝ} (hk : 2 ≤ k) (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * gammaRieszKernel k 1 (c * y))
      (gammaRieszKernel k 0 (c * x)) x := by
  simpa only [Real.rpow_one, sub_self, Real.rpow_zero, Complex.ofReal_one, one_mul] using
    hasDerivAt_gammaRieszWeightedKernel hk (le_refl (1 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2) hc hx

/-- The derivative of the actual weighted order-two kernel is exactly the weighted order-one kernel. -/
theorem hasDerivAt_gammaRieszKernel_two {k c x : ℝ} (hk : 2 ≤ k) (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * gammaRieszKernel k 2 (c * y))
      ((x : ℂ) * gammaRieszKernel k 1 (c * x)) x := by
  have hh := hasDerivAt_gammaRieszWeightedKernel hk (by norm_num : (1 : ℝ) ≤ 2) (le_refl (2 : ℝ)) hc hx
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Complex.ofReal_pow] at hh
  exact hh

end
end Dubon2026
