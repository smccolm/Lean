import GafniTao.Pintz2023Equation42RightIntegrable
import RiemannZeta.GuthMaynard.ZetaBounds
import RiemannZeta.GuthMaynard.ClassicalDichotomy
import RiemannZeta.GuthMaynard.HughesYoungEquation84SourceLine

/-!
# Pintz (2023), equation (4.2): integrability of a pole-safe left line

Only polynomial growth is needed to justify the complete contour shift.  On
the source range `Re (rho+s) >= 1/4`, Abel's formula gives a linear ordinate
bound for zeta.  The finite mollifier is bounded by its length, and the
literal Pintz Gaussian then makes the product integrable.  The sharper
Heath--Brown exponent used later in Pintz (4.11) is deliberately not smuggled
into this contour-existence lemma.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

set_option maxHeartbeats 800000

theorem continuous_pintz2023Equation42Integrand_vertical
    {X : ℕ} {rho : ℂ} {lambda left : ℝ}
    (hleft : left ≠ 0) (hpole : rho.re + left ≠ 1) :
    Continuous (fun u : ℝ =>
      pintz2023Equation42Integrand X rho lambda
        ((left : ℂ) + (u : ℂ) * I)) := by
  have hline : Continuous (fun u : ℝ =>
      (left : ℂ) + (u : ℂ) * I) := by fun_prop
  have htotal : Continuous (fun u : ℝ =>
      rho + ((left : ℂ) + (u : ℂ) * I)) :=
    continuous_const.add hline
  have hmollifier : Continuous (fun u : ℝ =>
      zetaMollifier X (rho + ((left : ℂ) + (u : ℂ) * I))) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (analyticAt_zetaMollifier X _).continuousAt.comp htotal.continuousAt
  have hzeta : Continuous (fun u : ℝ =>
      riemannZeta (rho + ((left : ℂ) + (u : ℂ) * I))) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hne : rho + ((left : ℂ) + (u : ℂ) * I) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, I_re,
        I_im, mul_zero, sub_zero, one_re] at hre
      exact hpole (by simpa using hre)
    have hzAt : ContinuousAt riemannZeta
        (rho + ((left : ℂ) + (u : ℂ) * I)) :=
      (differentiableAt_riemannZeta
        (s := rho + ((left : ℂ) + (u : ℂ) * I)) hne).continuousAt
    have htotalAt : ContinuousAt (fun v : ℝ =>
        rho + ((left : ℂ) + (v : ℂ) * I)) u := htotal.continuousAt
    have hc := ContinuousAt.comp
      (x := u)
      (f := fun v : ℝ => rho + ((left : ℂ) + (v : ℂ) * I))
      (g := riemannZeta) hzAt htotalAt
    simpa only [Function.comp_apply] using hc
  have hkernel : Continuous (fun u : ℝ =>
      pintzGaussianKernel lambda ((left : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hs : (left : ℂ) + (u : ℂ) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, I_re,
        I_im, mul_zero, sub_zero, zero_re] at hre
      exact hleft (by simpa using hre)
    have hnumAt : ContinuousAt (pintzGaussianNumerator lambda)
        ((left : ℂ) + (u : ℂ) * I) :=
      (analyticAt_pintzGaussianNumerator lambda
        ((left : ℂ) + (u : ℂ) * I)).continuousAt
    have hlineAt : ContinuousAt (fun v : ℝ =>
        (left : ℂ) + (v : ℂ) * I) u := hline.continuousAt
    have hnum' : ContinuousAt (fun v : ℝ =>
        pintzGaussianNumerator lambda
          ((left : ℂ) + (v : ℂ) * I)) u := by
      have hc := ContinuousAt.comp
        (x := u) (f := fun v : ℝ => (left : ℂ) + (v : ℂ) * I)
        (g := pintzGaussianNumerator lambda) hnumAt hlineAt
      simpa only [Function.comp_apply] using hc
    exact hnum'.div hlineAt hs
  unfold pintz2023Equation42Integrand
  exact (hmollifier.mul hzeta).mul hkernel

theorem norm_pintzGaussianKernel_vertical_le
    {lambda left u : ℝ} (hlambda : 0 < lambda) (hleft : left ≠ 0) :
    ‖pintzGaussianKernel lambda ((left : ℂ) + (u : ℂ) * I)‖ ≤
      |left|⁻¹ *
        Real.exp (left ^ 2 / lambda + lambda * left -
          (1 / lambda) * u ^ 2) := by
  have hden : |left| ≤ ‖(left : ℂ) + (u : ℂ) * I‖ := by
    simpa using Complex.abs_re_le_norm ((left : ℂ) + (u : ℂ) * I)
  have hleftPos : 0 < |left| := abs_pos.mpr hleft
  have hdenPos : 0 < ‖(left : ℂ) + (u : ℂ) * I‖ :=
    hleftPos.trans_le hden
  have hinv : ‖(left : ℂ) + (u : ℂ) * I‖⁻¹ ≤ |left|⁻¹ :=
    (inv_le_inv₀ hdenPos hleftPos).2 hden
  rw [show (u : ℂ) * I = I * u by simp [mul_comm]]
  rw [pintzGaussianKernel, norm_div, div_eq_mul_inv,
    norm_pintzGaussianNumerator_vertical_factored lambda left u hlambda,
    ← Real.exp_add]
  have hmul := mul_le_mul_of_nonneg_left hinv
    (Real.exp_pos
      (left ^ 2 / lambda + lambda * left - (1 / lambda) * u ^ 2)).le
  convert hmul using 1 <;> ring_nf

set_option maxHeartbeats 800000 in
theorem integrable_pintz2023Equation42Integrand_left
    {X : ℕ} {rho : ℂ} {lambda left : ℝ}
    (hlambda : 0 < lambda) (hleft : left ≠ 0)
    (hsigmaLower : 1 / 4 ≤ rho.re + left)
    (hsigmaUpper : rho.re + left < 1) :
    Integrable (fun u : ℝ =>
      pintz2023Equation42Integrand X rho lambda
        ((left : ℂ) + (u : ℂ) * I)) := by
  let f : ℝ → ℂ := fun u =>
    pintz2023Equation42Integrand X rho lambda
      ((left : ℂ) + (u : ℂ) * I)
  let L : ℝ := |rho.im| + 1
  let C : ℝ := 5 * (X : ℝ) * |left|⁻¹
  let A : ℝ := left ^ 2 / lambda + lambda * left
  let B : ℝ := 1 / lambda
  let D : ℝ := |rho.re + left| + |rho.im|
  have hf : Continuous f := by
    exact continuous_pintz2023Equation42Integrand_vertical hleft
      (ne_of_lt hsigmaUpper)
  apply integrable_of_continuous_of_norm_le_gaussian_tail f hf
      (L := L) (C := C) (A := A) (B := B) (D := D) (j := 1)
  · dsimp only [L]
    positivity
  · dsimp only [B]
    positivity
  · intro u hu
    have himLower : 1 ≤ |rho.im + u| := by
      have hrev : |u| - |rho.im| ≤ |rho.im + u| := by
        have h := abs_sub_abs_le_abs_sub u (-rho.im)
        simpa [abs_neg, sub_neg_eq_add, add_comm] using h
      dsimp only [L] at hu
      linarith
    let z : ℂ := rho + ((left : ℂ) + (u : ℂ) * I)
    have hzRe : z.re = rho.re + left := by
      simp [z, Complex.mul_re]
    have hzIm : z.im = rho.im + u := by
      simp [z, Complex.mul_im]
    have hmoll : ‖zetaMollifier X z‖ ≤ (X : ℝ) := by
      apply norm_zetaMollifier_le_length
      rw [hzRe]
      linarith
    have hzeta : ‖riemannZeta z‖ ≤ 5 * ‖z‖ := by
      exact norm_riemannZeta_le_five_mul_norm (hzRe.symm ▸ hsigmaLower)
        (hzIm.symm ▸ himLower)
    have hznorm : ‖z‖ ≤ D + |u| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ = |rho.re + left| + |rho.im + u| := by rw [hzRe, hzIm]
        _ ≤ |rho.re + left| + (|rho.im| + |u|) := by
          gcongr
          exact abs_add_le _ _
        _ = D + |u| := by simp only [D]; ring
    have hkernel := norm_pintzGaussianKernel_vertical_le hlambda hleft
      (u := u)
    have hD : 0 ≤ D + |u| := by
      dsimp only [D]
      positivity
    change ‖f u‖ ≤ C * Real.exp (A - B * u ^ 2) * (D + |u|) ^ 1
    dsimp only [f]
    rw [pintz2023Equation42Integrand, norm_mul, norm_mul]
    calc
      ‖zetaMollifier X z‖ * ‖riemannZeta z‖ *
          ‖pintzGaussianKernel lambda ((left : ℂ) + (u : ℂ) * I)‖ ≤
        (X : ℝ) * (5 * ‖z‖) *
          (|left|⁻¹ * Real.exp
            (left ^ 2 / lambda + lambda * left - (1 / lambda) * u ^ 2)) := by
              gcongr
      _ ≤ (X : ℝ) * (5 * (D + |u|)) *
          (|left|⁻¹ * Real.exp
            (left ^ 2 / lambda + lambda * left - (1 / lambda) * u ^ 2)) := by
              gcongr
      _ = C * Real.exp (A - B * u ^ 2) * (D + |u|) ^ 1 := by
        simp only [C, A, B, pow_one]
        ring

#print axioms continuous_pintz2023Equation42Integrand_vertical
#print axioms norm_pintzGaussianKernel_vertical_le
#print axioms integrable_pintz2023Equation42Integrand_left

end

end GafniTao
