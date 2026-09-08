import GafniTao.FordZeroDetectorZetaResidues

/-!
# Holomorphy of the translated cotangent weight in Ford's strip

The detector strip has real width `2η`.  Hence the scaled cotangent argument
has real part in `[-π/2,π/2]`; its only possible sine zero is the central
point.  This elementary fact supplies the differentiability premise at every
zeta zero and every regular contour point away from the center.
-/

open Complex Set

namespace GafniTao

noncomputable section

/-- Inside Ford's closed strip, the sine denominator of the cotangent kernel
can vanish only at the central point. -/
theorem ford_sin_ne_zero_of_abs_re_le
    {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hre : |z.re| ≤ eta) (hz : z ≠ 0) :
    Complex.sin
      ((((Real.pi / (2 * eta) : ℝ) : ℂ) * z)) ≠ 0 := by
  let c : ℝ := Real.pi / (2 * eta)
  intro hsin
  change Complex.sin ((c : ℂ) * z) = 0 at hsin
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  have hc : 0 < c := div_pos Real.pi_pos (mul_pos two_pos heta)
  have him : c * z.im = 0 := by
    have := congrArg Complex.im hk
    simpa [Complex.mul_im] using this
  have hzim : z.im = 0 := (mul_eq_zero.mp him).resolve_left hc.ne'
  have hreEq : c * z.re = (k : ℝ) * Real.pi := by
    have := congrArg Complex.re hk
    simpa [Complex.mul_re] using this
  have habsScaled : |c * z.re| ≤ c * eta := by
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hre hc.le
  have hcEta : c * eta = Real.pi / 2 := by
    dsimp [c]
    field_simp [heta.ne']
  have hkBound : |(k : ℝ)| ≤ 1 / 2 := by
    rw [hreEq, abs_mul, abs_of_pos Real.pi_pos, hcEta] at habsScaled
    nlinarith [Real.pi_pos]
  have hkZero : k = 0 := by
    by_contra hk0
    have hone : (1 : ℝ) ≤ |(k : ℝ)| := by
      exact_mod_cast Int.one_le_abs hk0
    linarith
  have hzre : z.re = 0 := by
    rw [hkZero] at hreEq
    norm_num at hreEq
    exact hreEq.resolve_left hc.ne'
  apply hz
  exact Complex.ext hzre hzim

/-- Differentiability of the unshifted Ford kernel at every noncentral point
of its closed strip. -/
theorem differentiableAt_fordCotKernel_of_abs_re_le
    {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hre : |z.re| ≤ eta) (hz : z ≠ 0) :
    DifferentiableAt ℂ (fordCotKernel eta) z :=
  (hasDerivAt_fordCotKernel
    (ford_sin_ne_zero_of_abs_re_le heta hre hz)).differentiableAt

/-- Translated form used at actual zeta zeros in the detector rectangle. -/
theorem differentiableAt_fordCotKernel_translate_of_abs_re_le
    {eta : ℝ} (heta : 0 < eta) {z z₀ : ℂ}
    (hre : |(z - z₀).re| ≤ eta) (hz : z ≠ z₀) :
    DifferentiableAt ℂ (fun w : ℂ => fordCotKernel eta (w - z₀)) z := by
  have hout : DifferentiableAt ℂ (fordCotKernel eta) (z - z₀) :=
    differentiableAt_fordCotKernel_of_abs_re_le heta hre
      (sub_ne_zero.mpr hz)
  have hin : DifferentiableAt ℂ (fun w : ℂ => w - z₀) z :=
    differentiableAt_id.sub_const z₀
  simpa only [Function.comp_apply] using hout.comp z hin

end

end GafniTao
