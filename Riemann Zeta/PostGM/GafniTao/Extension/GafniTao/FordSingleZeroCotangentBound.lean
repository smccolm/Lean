import GafniTao.FordDetectorExistentialBounds

/-!
# The prescribed zero's cotangent contribution

This module converts the literal selected-zero term retained by the Ford
contour into the negative reciprocal term used in the trigonometric
zero-free-region argument.  Analytic multiplicity is not discarded: it is
proved to be at least one from the frozen zeta-order theorem.
-/

open Complex
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

/-- A genuine zeta zero away from the pole has positive natural analytic
multiplicity. -/
theorem one_le_analyticVanishingOrder_riemannZeta
    {rho : ℂ} (hrhoOne : rho ≠ 1) (hrhoZero : riemannZeta rho = 0) :
    1 ≤ analyticVanishingOrder riemannZeta rho := by
  unfold analyticVanishingOrder
  have hAnalytic : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho (by simpa using hrhoOne)
  have hFinite : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    riemannZeta_analyticOrderAt_ne_top hrhoOne
  have hOrderNe : analyticOrderAt riemannZeta rho ≠ 0 :=
    hAnalytic.analyticOrderAt_ne_zero.mpr hrhoZero
  have hNatNe : analyticOrderNatAt riemannZeta rho ≠ 0 := by
    intro hzero
    apply hOrderNe
    rw [← Nat.cast_analyticOrderNatAt hFinite, hzero]
    simp
  exact Nat.one_le_iff_ne_zero.mpr hNatNe

/-- The exact one-zero term is bounded by the negative reciprocal of its
horizontal displacement, with the explicit cotangent correction retained. -/
theorem fordSingleZero_cotangentContribution_le
    {sigma eta t : ℝ} {rho : ℂ}
    (heta : 0 < eta) (ht : 0 < t) (hrhoZero : riemannZeta rho = 0)
    (hrhoUpper : rho.re ≤ 1) (hrhoIm : rho.im = t)
    (hdispPos : 0 < sigma - rho.re)
    (hdispEta : sigma - rho.re < eta) :
    ((analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel eta
          (rho - fordShiftedDetectorCenter sigma t)).re ≤
      -(1 / (sigma - rho.re)) + (sigma - rho.re) / eta ^ 2 := by
  let x : ℝ := sigma - rho.re
  have hx : 0 < x := hdispPos
  have hxeta : x < eta := hdispEta
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrhoIm
    linarith
  have hmNat : 1 ≤ analyticVanishingOrder riemannZeta rho :=
    one_le_analyticVanishingOrder_riemannZeta hrhoOne hrhoZero
  have hdiff :
      rho - fordShiftedDetectorCenter sigma t = -(x : ℂ) := by
    apply Complex.ext
    · simp [fordShiftedDetectorCenter, x]
    · simp [fordShiftedDetectorCenter, hrhoIm]
  have hnorm : ‖(x : ℂ)‖ ≤ eta := by
    simpa [Complex.norm_real, abs_of_pos hx] using hxeta.le
  have hcorr := fordCotKernel_sub_inv_re_lower heta
    (z := (x : ℂ)) (by simpa using hx.le) hnorm
  have hkernelPos :
      1 / x - x / eta ^ 2 ≤ (fordCotKernel eta (x : ℂ)).re := by
    simpa using hcorr
  have hkernelNeg :
      (fordCotKernel eta (-(x : ℂ))).re ≤
        -(1 / x) + x / eta ^ 2 := by
    rw [fordCotKernel_neg]
    simp only [neg_re]
    linarith
  have hboundNeg : -(1 / x) + x / eta ^ 2 < 0 := by
    have hetaSq : 0 < eta ^ 2 := sq_pos_of_pos heta
    have hfrac : x / eta ^ 2 < 1 / x := by
      apply (div_lt_div_iff₀ hetaSq hx).mpr
      have hsq : x ^ 2 < eta ^ 2 := by nlinarith
      nlinarith
    linarith
  have hkernelStrict :
      (fordCotKernel eta (-(x : ℂ))).re < 0 :=
    lt_of_le_of_lt hkernelNeg hboundNeg
  rw [hdiff, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have hmReal : (1 : ℝ) ≤ analyticVanishingOrder riemannZeta rho := by
    exact_mod_cast hmNat
  have hmult :
      (analyticVanishingOrder riemannZeta rho : ℝ) *
          (fordCotKernel eta (-(x : ℂ))).re ≤
        (fordCotKernel eta (-(x : ℂ))).re := by
    nlinarith
  exact hmult.trans (by simpa [x] using hkernelNeg)

#print axioms one_le_analyticVanishingOrder_riemannZeta
#print axioms fordSingleZero_cotangentContribution_le

end

end GafniTao
