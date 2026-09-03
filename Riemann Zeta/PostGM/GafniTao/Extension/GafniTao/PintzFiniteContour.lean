import GafniTao.PintzMobiusHead
import GafniTao.FordQualitativeGlobalGrowth

/-!
# The finite Pintz detector and its pole-safe contour

After truncating the Möbius series, Pintz shifts a finite Dirichlet
polynomial multiplied by `ζ(ρ+s)`.  At `s=0` the apparent pole is removable
because `ρ` is a zeta zero.  We model that removal by the divided slope of
the complete numerator, rather than deleting a point from the contour.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The genuine finite Möbius Dirichlet polynomial through `Y₁`. -/
noncomputable def pintzFiniteMobiusPolynomial
    (rho : ℂ) (lambda : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
    LSeries.term
      (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) (rho + s) n

/-- Numerator of the finite contour integrand before division by `s`. -/
noncomputable def pintzFiniteContourNumerator
    (rho : ℂ) (lambda : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (rho + s) * pintzFiniteMobiusPolynomial rho lambda s *
    pintzGaussianNumerator lambda s

/-- Holomorphic removal of the apparent singularity at `s=0`. -/
noncomputable def pintzFiniteContourIntegrand
    (rho : ℂ) (lambda : ℝ) : ℂ → ℂ :=
  dslope (pintzFiniteContourNumerator rho lambda) 0

/-- Away from zero, the regularized integrand is the literal quotient in
Pintz's contour. -/
theorem pintzFiniteContourIntegrand_eq_div
    {rho s : ℂ} {lambda : ℝ} (hrhoZero : riemannZeta rho = 0)
    (hs : s ≠ 0) :
    pintzFiniteContourIntegrand rho lambda s =
      pintzFiniteContourNumerator rho lambda s / s := by
  rw [pintzFiniteContourIntegrand, dslope_of_ne _ hs]
  simp [slope, pintzFiniteContourNumerator, hrhoZero, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

/-- The finite numerator is holomorphic wherever the translated zeta factor
does not meet its pole. -/
theorem differentiableOn_pintzFiniteContourNumerator
    (rho : ℂ) (lambda : ℝ) :
    DifferentiableOn ℂ (pintzFiniteContourNumerator rho lambda)
      {s : ℂ | rho + s ≠ 1} := by
  intro s hs
  have hzeta : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (rho + z)) s :=
    (differentiableAt_riemannZeta hs).comp s (by fun_prop)
  have hpoly : DifferentiableAt ℂ
      (pintzFiniteMobiusPolynomial rho lambda) s := by
    unfold pintzFiniteMobiusPolynomial
    apply DifferentiableAt.fun_sum
    intro n hn
    exact (LSeries.hasDerivAt_term
      (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) n (rho + s)).differentiableAt.comp
        s ((differentiableAt_const rho).add differentiableAt_id)
  unfold pintzFiniteContourNumerator
  have hgauss : DifferentiableAt ℂ (pintzGaussianNumerator lambda) s := by
    unfold pintzGaussianNumerator
    fun_prop
  exact ((hzeta.mul hpoly).mul hgauss).differentiableWithinAt

/-- The regularized finite integrand is holomorphic on the same pole-safe
domain, provided the center itself is not the zeta pole. -/
theorem differentiableOn_pintzFiniteContourIntegrand
    {rho : ℂ} {lambda : ℝ} (hrhoOne : rho ≠ 1) :
    DifferentiableOn ℂ (pintzFiniteContourIntegrand rho lambda)
      {s : ℂ | rho + s ≠ 1} := by
  let U : Set ℂ := {s : ℂ | rho + s ≠ 1}
  have hUOpen : IsOpen U := by
    have hc : Continuous (fun s : ℂ => rho + s) :=
      continuous_const.add continuous_id
    simpa [U] using ((isOpen_ne : IsOpen {z : ℂ | z ≠ 1}).preimage hc)
  have hzero : (0 : ℂ) ∈ U := by simpa [U, add_comm] using hrhoOne
  have hUnhds : U ∈ 𝓝 (0 : ℂ) := hUOpen.mem_nhds hzero
  exact (differentiableOn_dslope hUnhds).mpr
    (differentiableOn_pintzFiniteContourNumerator rho lambda)

/-- If the horizontal height is below `|Im ρ|`, the translated zeta pole is
outside the entire contour rectangle. -/
theorem pintzFiniteContour_pole_avoided
    {rho : ℂ} {R : ℝ} (hheight : R < |rho.im|) :
    ∀ s : ℂ, -R <= s.im -> s.im <= R -> rho + s ≠ 1 := by
  intro s hsBottom hsTop hpole
  have him := congrArg Complex.im hpole
  simp only [add_im, one_im] at him
  have hsIm : |s.im| <= R := by
    rw [abs_le]
    exact ⟨hsBottom, hsTop⟩
  have : |rho.im| = |s.im| := by rw [show rho.im = -s.im by linarith, abs_neg]
  linarith

/-- Cauchy's theorem for the finite, regularized Pintz rectangle. -/
theorem pintzFiniteContour_rectangle_vanishes
    {rho : ℂ} {lambda left R : ℝ}
    (hleft : left <= 3)
    (hR : 0 <= R) (hheight : R < |rho.im|) :
    RectangleIntegral (pintzFiniteContourIntegrand rho lambda)
      (((left : ℝ) : ℂ) + (-R : ℂ) * I)
      (((3 : ℝ) : ℂ) + (R : ℂ) * I) = 0 := by
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    have him : rho.im = 0 := by rw [hrho]; norm_num
    have habs : |rho.im| = 0 := by rw [him, abs_zero]
    rw [habs] at hheight
    linarith
  apply HolomorphicOn.vanishesOnRectangle
    (differentiableOn_pintzFiniteContourIntegrand hrhoOne)
  intro s hs
  have hRe :
      ((((left : ℝ) : ℂ) + (-R : ℂ) * I).re) <=
        ((((3 : ℝ) : ℂ) + (R : ℂ) * I).re) := by simpa using hleft
  have hIm :
      ((((left : ℝ) : ℂ) + (-R : ℂ) * I).im) <=
        ((((3 : ℝ) : ℂ) + (R : ℂ) * I).im) := by
    norm_num [Complex.mul_im]
    linarith
  have hmem := (mem_Rect hRe hIm s).mp hs
  apply pintzFiniteContour_pole_avoided hheight s
  · simpa using hmem.2.2.1
  · simpa using hmem.2.2.2

/-- Exact finite-height displacement from the source line `Re s=3` to an
arbitrary left line, with both horizontal edges still explicit. -/
theorem pintzFiniteContour_finite_vertical_shift
    {rho : ℂ} {lambda left R : ℝ}
    (hleft : left <= 3)
    (hR : 0 <= R) (hheight : R < |rho.im|) :
    VIntegral' (pintzFiniteContourIntegrand rho lambda) left (-R) R =
      VIntegral' (pintzFiniteContourIntegrand rho lambda) 3 (-R) R +
        HIntegral' (pintzFiniteContourIntegrand rho lambda) left 3 (-R) -
        HIntegral' (pintzFiniteContourIntegrand rho lambda) left 3 R := by
  have hrect := pintzFiniteContour_rectangle_vanishes
    (lambda := lambda) hleft hR hheight
  have hraw :
      VIntegral (pintzFiniteContourIntegrand rho lambda) left (-R) R =
        VIntegral (pintzFiniteContourIntegrand rho lambda) 3 (-R) R +
          HIntegral (pintzFiniteContourIntegrand rho lambda) left 3 (-R) -
          HIntegral (pintzFiniteContourIntegrand rho lambda) left 3 R := by
    unfold RectangleIntegral at hrect
    norm_num [Complex.mul_re, Complex.mul_im] at hrect
    linear_combination -hrect
  unfold VIntegral' HIntegral'
  rw [← smul_add, ← smul_sub]
  exact congrArg ((1 / (2 * Real.pi * I) : ℂ) • ·) hraw

/-- On the original line, the regularized finite contour is pointwise the
finite sum of the genuine Möbius vertical terms. -/
theorem pintzFiniteContourIntegrand_three_eq_sum
    {rho : ℂ} {lambda : ℝ} (hrhoZero : riemannZeta rho = 0)
    (t : ℝ) :
    pintzFiniteContourIntegrand rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I) =
      ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        pintzMobiusVerticalTerm rho lambda n t := by
  have hs : (((3 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  rw [pintzFiniteContourIntegrand_eq_div hrhoZero hs]
  unfold pintzFiniteContourNumerator pintzFiniteMobiusPolynomial
    pintzMobiusVerticalTerm pintzGaussianKernel
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [add_comm rho]
  ring_nf

/-- The complete original-line integral of the finite contour is exactly
the finite Möbius head established in equation (4.5). -/
theorem pintzFiniteContour_verticalIntegral_three_eq_head
    {rho : ℂ} {lambda : ℝ} (hrhoZero : riemannZeta rho = 0)
    (hrhoHalf : 1 / 2 <= rho.re) (hlambda : 0 < lambda) :
    VerticalIntegral' (pintzFiniteContourIntegrand rho lambda) 3 =
      pintzMobiusFiniteHead rho lambda := by
  unfold VerticalIntegral' VerticalIntegral pintzMobiusFiniteHead
  simp only [smul_eq_mul]
  have hpoint : (fun t : ℝ => pintzFiniteContourIntegrand rho lambda
      (((3 : ℝ) : ℂ) + (t : ℂ) * I)) =
      (fun t : ℝ => ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        pintzMobiusVerticalTerm rho lambda n t) := by
    funext t
    exact pintzFiniteContourIntegrand_three_eq_sum hrhoZero t
  rw [hpoint, integral_finsetSum]
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    unfold pintzMobiusWeightedTerm
    convert normalized_integral_pintzMobiusVerticalTerm_eq rho lambda n using 1
    ring
  · intro n hn
    exact integrable_pintzMobiusVerticalTerm hrhoHalf hlambda n

#print axioms pintzFiniteContourIntegrand_eq_div
#print axioms differentiableOn_pintzFiniteContourIntegrand
#print axioms pintzFiniteContour_rectangle_vanishes
#print axioms pintzFiniteContour_finite_vertical_shift
#print axioms pintzFiniteContour_verticalIntegral_three_eq_head

end

end GafniTao
