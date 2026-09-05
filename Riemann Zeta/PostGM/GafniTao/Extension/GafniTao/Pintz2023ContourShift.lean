import GafniTao.Pintz2023Equation47TruncationBound

/-!
# Pintz (2023), equation (4.2): the source contour displacement

The product `M_X (rho+s) * zeta (rho+s)` has a removable zero at `s=0`
when `rho` is a zeta zero.  We expose that removal with `dslope`, then prove
the finite rectangle displacement from `Re s = 3` to `Re s = -eta` without
crossing the translated zeta pole.  No cutoff is changed: `X` remains the
literal finite mollifier length from Pintz (4.1).
-/

open Complex Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintz2023ContourNumerator
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (s : ℂ) : ℂ :=
  zetaMollifier X (rho + s) * riemannZeta (rho + s) *
    pintzGaussianNumerator lambda s

noncomputable def pintz2023ContourIntegrand
    (X : ℕ) (rho : ℂ) (lambda : ℝ) : ℂ → ℂ :=
  dslope (pintz2023ContourNumerator X rho lambda) 0

theorem pintz2023ContourIntegrand_eq_source
    {X : ℕ} {rho s : ℂ} {lambda : ℝ}
    (hrho : riemannZeta rho = 0) (hs : s ≠ 0) :
    pintz2023ContourIntegrand X rho lambda s =
      pintz2023Equation42Integrand X rho lambda s := by
  rw [pintz2023ContourIntegrand, dslope_of_ne _ hs]
  simp [slope, pintz2023ContourNumerator, pintz2023Equation42Integrand,
    pintzGaussianKernel, hrho, smul_eq_mul, div_eq_mul_inv, mul_comm]
  ring

theorem differentiableAt_zetaMollifier_add
    (X : ℕ) (rho s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => zetaMollifier X (rho + z)) s := by
  unfold zetaMollifier
  apply DifferentiableAt.fun_sum
  intro n _hn
  have h :=
    ((LSeries.hasDerivAt_term
      (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) n (rho + s)).differentiableAt.comp
        s ((differentiableAt_const rho).add differentiableAt_id))
  convert h using 1
  funext z
  simp only [Function.comp_apply]
  rw [LSeries.term_def₀ (by simp)]

theorem differentiableOn_pintz2023ContourNumerator
    (X : ℕ) (rho : ℂ) (lambda : ℝ) :
    DifferentiableOn ℂ (pintz2023ContourNumerator X rho lambda)
      {s : ℂ | rho + s ≠ 1} := by
  intro s hs
  have hmollifier : DifferentiableAt ℂ
      (fun z : ℂ => zetaMollifier X (rho + z)) s :=
    differentiableAt_zetaMollifier_add X rho s
  have hzeta : DifferentiableAt ℂ
      (fun z : ℂ => riemannZeta (rho + z)) s :=
    (differentiableAt_riemannZeta hs).comp s (by fun_prop)
  have hgaussian : DifferentiableAt ℂ
      (pintzGaussianNumerator lambda) s := by
    unfold pintzGaussianNumerator
    fun_prop
  exact DifferentiableAt.differentiableWithinAt
    ((hmollifier.mul hzeta).mul hgaussian)

theorem differentiableOn_pintz2023ContourIntegrand
    {X : ℕ} {rho : ℂ} {lambda : ℝ} (hrhoOne : rho ≠ 1) :
    DifferentiableOn ℂ (pintz2023ContourIntegrand X rho lambda)
      {s : ℂ | rho + s ≠ 1} := by
  let U : Set ℂ := {s : ℂ | rho + s ≠ 1}
  have hUOpen : IsOpen U := by
    have hc : Continuous (fun s : ℂ => rho + s) :=
      continuous_const.add continuous_id
    simpa [U] using ((isOpen_ne : IsOpen {z : ℂ | z ≠ 1}).preimage hc)
  have hzero : (0 : ℂ) ∈ U := by simpa [U, add_comm] using hrhoOne
  exact (differentiableOn_dslope (hUOpen.mem_nhds hzero)).mpr
    (differentiableOn_pintz2023ContourNumerator X rho lambda)

private theorem pintz2023Contour_pole_avoided
    {rho : ℂ} {R : ℝ} (hheight : R < |rho.im|) :
    ∀ s : ℂ, -R ≤ s.im → s.im ≤ R → rho + s ≠ 1 := by
  intro s hsBottom hsTop hpole
  have him := congrArg Complex.im hpole
  simp only [add_im, one_im] at him
  have hsIm : |s.im| ≤ R := by
    rw [abs_le]
    exact ⟨hsBottom, hsTop⟩
  have heq : |rho.im| = |s.im| := by
    rw [show rho.im = -s.im by linarith, abs_neg]
  linarith

theorem pintz2023Contour_rectangle_vanishes
    {X : ℕ} {rho : ℂ} {lambda left R : ℝ}
    (hleft : left ≤ 3) (hR : 0 ≤ R) (hheight : R < |rho.im|) :
    RectangleIntegral (pintz2023ContourIntegrand X rho lambda)
      (((left : ℝ) : ℂ) + (-R : ℂ) * I)
      (((3 : ℝ) : ℂ) + (R : ℂ) * I) = 0 := by
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    have him : rho.im = 0 := by rw [hrho]; norm_num
    rw [him, abs_zero] at hheight
    linarith
  apply HolomorphicOn.vanishesOnRectangle
    (differentiableOn_pintz2023ContourIntegrand hrhoOne)
  intro s hs
  have hRe :
      ((((left : ℝ) : ℂ) + (-R : ℂ) * I).re) ≤
        ((((3 : ℝ) : ℂ) + (R : ℂ) * I).re) := by simpa using hleft
  have hIm :
      ((((left : ℝ) : ℂ) + (-R : ℂ) * I).im) ≤
        ((((3 : ℝ) : ℂ) + (R : ℂ) * I).im) := by
    norm_num [Complex.mul_im]
    linarith
  have hmem := (mem_Rect hRe hIm s).mp hs
  apply pintz2023Contour_pole_avoided hheight s
  · simpa using hmem.2.2.1
  · simpa using hmem.2.2.2

/-- Exact finite-height displacement underlying the first equality in
Pintz (4.2). -/
theorem pintz2023Contour_finite_vertical_shift
    {X : ℕ} {rho : ℂ} {lambda left R : ℝ}
    (hleft : left ≤ 3) (hR : 0 ≤ R) (hheight : R < |rho.im|) :
    VIntegral' (pintz2023ContourIntegrand X rho lambda) left (-R) R =
      VIntegral' (pintz2023ContourIntegrand X rho lambda) 3 (-R) R +
        HIntegral' (pintz2023ContourIntegrand X rho lambda) left 3 (-R) -
        HIntegral' (pintz2023ContourIntegrand X rho lambda) left 3 R := by
  have hrect := pintz2023Contour_rectangle_vanishes
    (X := X) (lambda := lambda) hleft hR hheight
  have hraw :
      VIntegral (pintz2023ContourIntegrand X rho lambda) left (-R) R =
        VIntegral (pintz2023ContourIntegrand X rho lambda) 3 (-R) R +
          HIntegral (pintz2023ContourIntegrand X rho lambda) left 3 (-R) -
          HIntegral (pintz2023ContourIntegrand X rho lambda) left 3 R := by
    unfold RectangleIntegral at hrect
    norm_num [Complex.mul_re, Complex.mul_im] at hrect
    linear_combination -hrect
  unfold VIntegral' HIntegral'
  rw [← smul_add, ← smul_sub]
  exact congrArg ((1 / (2 * Real.pi * I) : ℂ) • ·) hraw

theorem pintz2023Equation42Integral_eq_regularized
    {X : ℕ} {rho : ℂ} {lambda : ℝ} (hrho : riemannZeta rho = 0) :
    pintz2023Equation42Integral X rho lambda =
      VerticalIntegral' (pintz2023ContourIntegrand X rho lambda) 3 := by
  unfold pintz2023Equation42Integral VerticalIntegral' VerticalIntegral
  congr 2
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  symm
  apply pintz2023ContourIntegrand_eq_source hrho
  intro hs
  have hre := congrArg Complex.re hs
  norm_num at hre

#print axioms pintz2023ContourIntegrand_eq_source
#print axioms differentiableOn_pintz2023ContourIntegrand
#print axioms pintz2023Contour_rectangle_vanishes
#print axioms pintz2023Contour_finite_vertical_shift
#print axioms pintz2023Equation42Integral_eq_regularized

end

end GafniTao
