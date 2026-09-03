import GafniTao.PintzGaussianResidue

/-!
# Finite rectangle form of Pintz equation (4.1)

The limit to complete vertical lines is postponed.  At every finite height
the normalized rectangle integral is exactly the residue one, with all four
oriented edges visible.
-/

open Complex Set

namespace GafniTao

noncomputable section

/-- The bare Pintz Gaussian kernel has normalized rectangle integral one
whenever the rectangle straddles the origin. -/
theorem pintzGaussian_rectangleIntegral_eq_one
    {lambda left right R : ℝ}
    (hleft : left < 0) (hright : 0 < right) (hR : 0 < R) :
    RectangleIntegral' (pintzGaussianKernel lambda)
      ((left : ℂ) - (R : ℂ) * Complex.I)
      ((right : ℂ) + (R : ℂ) * Complex.I) = 1 := by
  apply ResidueTheoremOnRectangleWithSimplePole'
      (p := 0) (A := 1)
  · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      sub_zero, Complex.add_re]
    linarith
  · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, zero_add,
      Complex.add_im]
    linarith
  · rw [rectangle_mem_nhds_iff, mem_reProdIm]
    have hreLeft :
        ((left : ℂ) - (R : ℂ) * Complex.I).re = left := by simp
    have hreRight :
        ((right : ℂ) + (R : ℂ) * Complex.I).re = right := by simp
    have himLeft :
        ((left : ℂ) - (R : ℂ) * Complex.I).im = -R := by simp
    have himRight :
        ((right : ℂ) + (R : ℂ) * Complex.I).im = R := by simp
    rw [hreLeft, hreRight, himLeft, himRight]
    simp only [Complex.zero_re, Complex.zero_im]
    rw [uIoo_of_le (hleft.le.trans hright.le),
      uIoo_of_le (by linarith : -R ≤ R)]
    exact ⟨⟨hleft, hright⟩, ⟨neg_lt_zero.mpr hR, hR⟩⟩
  · exact (differentiableOn_pintzGaussianKernel_off_origin lambda).mono
      (by
        intro s hs
        simpa only [mem_compl_iff, mem_singleton_iff] using hs.2)
  · simpa only [sub_zero] using
      pintzGaussianKernel_sub_principal_isBigO_one lambda

/-- Exact finite-height edge decomposition underlying Pintz (4.1). -/
theorem pintzGaussian_rightVertical_eq_one_add_edges
    {lambda left right R : ℝ}
    (hleft : left < 0) (hright : 0 < right) (hR : 0 < R) :
    VIntegral' (pintzGaussianKernel lambda) right (-R) R =
      1 - HIntegral' (pintzGaussianKernel lambda) left right (-R) +
        HIntegral' (pintzGaussianKernel lambda) left right R +
          VIntegral' (pintzGaussianKernel lambda) left (-R) R := by
  have hrect := pintzGaussian_rectangleIntegral_eq_one
    (lambda := lambda) (left := left) (right := right) (R := R)
    hleft hright hR
  have hreLeft :
      ((left : ℂ) - (R : ℂ) * Complex.I).re = left := by simp
  have hreRight :
      ((right : ℂ) + (R : ℂ) * Complex.I).re = right := by simp
  have himLeft :
      ((left : ℂ) - (R : ℂ) * Complex.I).im = -R := by simp
  have himRight :
      ((right : ℂ) + (R : ℂ) * Complex.I).im = R := by simp
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLeft, hreRight, himLeft, himRight] at hrect
  linear_combination hrect

#print axioms pintzGaussian_rectangleIntegral_eq_one
#print axioms pintzGaussian_rightVertical_eq_one_add_edges

end

end GafniTao
