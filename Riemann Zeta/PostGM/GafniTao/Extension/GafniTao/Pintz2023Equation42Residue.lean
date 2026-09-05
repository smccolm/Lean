import GafniTao.Pintz2023ContourShift
import RiemannZeta.External.PNT.ResidueCalcOnRectangles
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Pintz (2023), equation (4.2): the crossed zeta pole

Pintz shifts the complete source contour from `Re s = 3` to `Re s = -eta`.
The translated zeta pole at `s = 1 - rho` is crossed.  This module removes
both the apparent singularity at `s = 0` (using the fact that `rho` is a
zeta zero) and the zeta pole, and computes the resulting residue exactly.
-/

open Complex Set MeasureTheory Filter

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintz2023ShiftedRegularizedZeta
    (rho s : ℂ) : ℂ :=
  regularizedRiemannZeta (rho + s)

noncomputable def pintz2023EntireContourProduct
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (s : ℂ) : ℂ :=
  zetaMollifier X (rho + s) *
    pintz2023ShiftedRegularizedZeta rho s *
    pintzGaussianNumerator lambda s

/-- The entire numerator after removing the zero at `s = 0`. -/
noncomputable def pintz2023PoleNumerator
    (X : ℕ) (rho : ℂ) (lambda : ℝ) : ℂ → ℂ :=
  dslope (pintz2023EntireContourProduct X rho lambda) 0

/-- The exact residue crossed at the translated zeta pole. -/
noncomputable def pintz2023PoleResidue
    (X : ℕ) (rho : ℂ) (lambda : ℝ) : ℂ :=
  zetaMollifier X 1 * pintzGaussianNumerator lambda (1 - rho) / (1 - rho)

theorem pintz2023ShiftedRegularizedZeta_zero
    {rho : ℂ} (hrhoOne : rho ≠ 1) (hrhoZero : riemannZeta rho = 0) :
    pintz2023ShiftedRegularizedZeta rho 0 = 0 := by
  rw [pintz2023ShiftedRegularizedZeta, add_zero, regularizedRiemannZeta,
    Function.update_of_ne hrhoOne, hrhoZero, mul_zero]

theorem pintz2023ShiftedRegularizedZeta_eq
    {rho s : ℂ} (hpole : rho + s ≠ 1) :
    pintz2023ShiftedRegularizedZeta rho s =
      (s - (1 - rho)) * riemannZeta (rho + s) := by
  rw [pintz2023ShiftedRegularizedZeta, regularizedRiemannZeta,
    Function.update_of_ne hpole]
  ring

theorem pintz2023PoleNumerator_div_eq_source
    {X : ℕ} {rho s : ℂ} {lambda : ℝ}
    (hrhoOne : rho ≠ 1) (hrhoZero : riemannZeta rho = 0)
    (hsZero : s ≠ 0) (hsPole : s ≠ 1 - rho) :
    pintz2023PoleNumerator X rho lambda s / (s - (1 - rho)) =
      pintz2023Equation42Integrand X rho lambda s := by
  have hzero := pintz2023ShiftedRegularizedZeta_zero hrhoOne hrhoZero
  have hproductZero : pintz2023EntireContourProduct X rho lambda 0 = 0 := by
    simp [pintz2023EntireContourProduct, hzero]
  have hshiftPole : rho + s ≠ 1 := by
    intro h
    apply hsPole
    linear_combination h
  have hslope := sub_smul_dslope_of_zero hproductZero s
  have hnumerator :
      s * pintz2023PoleNumerator X rho lambda s =
        zetaMollifier X (rho + s) *
          ((s - (1 - rho)) * riemannZeta (rho + s)) *
          pintzGaussianNumerator lambda s := by
    simpa [pintz2023PoleNumerator, pintz2023EntireContourProduct,
      pintz2023ShiftedRegularizedZeta_eq hshiftPole, smul_eq_mul] using hslope
  rw [pintz2023Equation42Integrand, pintzGaussianKernel]
  rw [div_eq_iff (sub_ne_zero.mpr hsPole), div_eq_mul_inv]
  calc
    pintz2023PoleNumerator X rho lambda s =
        (s * pintz2023PoleNumerator X rho lambda s) / s := by
          field_simp
    _ = (zetaMollifier X (rho + s) *
          ((s - (1 - rho)) * riemannZeta (rho + s)) *
          pintzGaussianNumerator lambda s) / s := by rw [hnumerator]
    _ = (zetaMollifier X (rho + s) * riemannZeta (rho + s) *
          (pintzGaussianNumerator lambda s * s⁻¹)) *
          (s - (1 - rho)) := by
      rw [div_eq_mul_inv]
      ring

theorem differentiableAt_pintz2023ShiftedRegularizedZeta
    (rho s : ℂ) :
    DifferentiableAt ℂ (pintz2023ShiftedRegularizedZeta rho) s := by
  unfold pintz2023ShiftedRegularizedZeta
  exact (differentiableAt_regularizedRiemannZeta (rho + s)).comp s
    ((differentiableAt_const (𝕜 := ℂ) rho).add differentiableAt_id)

theorem differentiableAt_pintz2023EntireContourProduct
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (pintz2023EntireContourProduct X rho lambda) s := by
  have hm := differentiableAt_zetaMollifier_add X rho s
  have hz := differentiableAt_pintz2023ShiftedRegularizedZeta rho s
  have hg : DifferentiableAt ℂ (pintzGaussianNumerator lambda) s := by
    unfold pintzGaussianNumerator
    fun_prop
  exact (hm.mul hz).mul hg

theorem differentiableAt_pintz2023PoleNumerator
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (pintz2023PoleNumerator X rho lambda) s := by
  have hdiff : DifferentiableOn ℂ
      (pintz2023EntireContourProduct X rho lambda) Set.univ :=
    fun z _hz =>
      (differentiableAt_pintz2023EntireContourProduct X rho lambda z).differentiableWithinAt
  have hslope : DifferentiableOn ℂ
      (dslope (pintz2023EntireContourProduct X rho lambda) 0) Set.univ :=
    (Complex.differentiableOn_dslope
      (Filter.univ_mem : Set.univ ∈ nhds (0 : ℂ))).2 hdiff
  exact differentiableWithinAt_univ.mp (hslope s (Set.mem_univ s))

theorem pintz2023PoleNumerator_at_pole
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrhoOne : rho ≠ 1) (hrhoZero : riemannZeta rho = 0) :
    pintz2023PoleNumerator X rho lambda (1 - rho) =
      pintz2023PoleResidue X rho lambda := by
  let p : ℂ := 1 - rho
  have hpZero : p ≠ 0 := sub_ne_zero.mpr hrhoOne.symm
  have hzero := pintz2023ShiftedRegularizedZeta_zero hrhoOne hrhoZero
  have hproductZero : pintz2023EntireContourProduct X rho lambda 0 = 0 := by
    simp [pintz2023EntireContourProduct, hzero]
  have hrhop : rho + p = 1 := by dsimp [p]; ring
  have hregp : pintz2023ShiftedRegularizedZeta rho p = 1 := by
    rw [pintz2023ShiftedRegularizedZeta, hrhop, regularizedRiemannZeta]
    simp
  have hslope := sub_smul_dslope_of_zero hproductZero p
  have hpnum : p * pintz2023PoleNumerator X rho lambda p =
      zetaMollifier X 1 * pintzGaussianNumerator lambda p := by
    simpa [pintz2023PoleNumerator, pintz2023EntireContourProduct,
      hrhop, hregp, smul_eq_mul] using hslope
  unfold pintz2023PoleResidue
  change pintz2023PoleNumerator X rho lambda p =
    zetaMollifier X 1 * pintzGaussianNumerator lambda p / p
  rw [eq_div_iff hpZero]
  simpa [mul_comm] using hpnum

set_option maxHeartbeats 800000 in
/-- Finite rectangle form of the residue-bearing shift in Pintz (4.2). -/
theorem pintz2023Equation42_finite_rectangle_residue
    {X : ℕ} {rho : ℂ} {lambda left R : ℝ}
    (hrhoOne : rho ≠ 1) (hrhoZero : riemannZeta rho = 0)
    (hleft : left < 1 - rho.re) (hright : 1 - rho.re < 3)
    (hheight : |rho.im| < R) :
    RectangleIntegral'
      (fun s => pintz2023PoleNumerator X rho lambda s /
        (s - (1 - rho)))
      (((left : ℝ) : ℂ) - (R : ℂ) * I)
      (((3 : ℝ) : ℂ) + (R : ℂ) * I) =
        pintz2023PoleResidue X rho lambda := by
  let z : ℂ := ((left : ℝ) : ℂ) - (R : ℂ) * I
  let w : ℂ := ((3 : ℝ) : ℂ) + (R : ℂ) * I
  let p : ℂ := 1 - rho
  let N : ℂ → ℂ := pintz2023PoleNumerator X rho lambda
  let f : ℂ → ℂ := fun s => N s / (s - p)
  let g : ℂ → ℂ := dslope N p
  have hRpos : 0 < R := (abs_nonneg rho.im).trans_lt hheight
  have hzRe : z.re ≤ w.re := by simp [z, w]; linarith
  have hzIm : z.im ≤ w.im := by simp [z, w]; linarith
  have hpInterior : Rectangle z w ∈ nhds p := by
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzRe, Set.uIoo_of_le hzIm,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · simp [p, z, w]
      exact ⟨hleft, hright⟩
    · simp [p, z, w]
      constructor <;> linarith [le_abs_self rho.im, neg_le_abs rho.im]
  have hNdiff : DifferentiableOn ℂ N (Rectangle z w) := by
    intro s _hs
    exact (differentiableAt_pintz2023PoleNumerator X rho lambda s).differentiableWithinAt
  have hgHolo : HolomorphicOn g (Rectangle z w) :=
    (Complex.differentiableOn_dslope hpInterior).2 hNdiff
  have hNp : N p = pintz2023PoleResidue X rho lambda := by
    simpa [N, p] using pintz2023PoleNumerator_at_pole
      (X := X) (lambda := lambda) hrhoOne hrhoZero
  have hPrincipal : Set.EqOn
      (f - fun s => pintz2023PoleResidue X rho lambda / (s - p)) g
      (Rectangle z w \ {p}) := by
    intro s hs
    have hsp : s ≠ p := by simpa using hs.2
    have hslope := sub_smul_dslope N p s
    change f s - pintz2023PoleResidue X rho lambda / (s - p) = g s
    rw [← hNp]
    dsimp [f, g]
    rw [← sub_div, ← hslope]
    rw [smul_eq_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsp)]
  have hresidue := ResidueTheoremOnRectangleWithSimplePole
    hzRe hzIm hpInterior hgHolo hPrincipal
  simpa [z, w, p, N, f, g] using hresidue

set_option maxHeartbeats 800000 in
/-- The residue identity for the literal source integrand.  The values at
the two removable/interior exceptional points do not affect the boundary
because both points lie strictly inside the rectangle. -/
theorem pintz2023Equation42_finite_source_rectangle
    {X : ℕ} {rho : ℂ} {lambda left R : ℝ}
    (hrhoOne : rho ≠ 1) (hrhoZero : riemannZeta rho = 0)
    (hleftZero : left < 0)
    (hleft : left < 1 - rho.re) (hright : 1 - rho.re < 3)
    (hheight : |rho.im| < R) :
    RectangleIntegral' (pintz2023Equation42Integrand X rho lambda)
      (((left : ℝ) : ℂ) - (R : ℂ) * I)
      (((3 : ℝ) : ℂ) + (R : ℂ) * I) =
        pintz2023PoleResidue X rho lambda := by
  let z : ℂ := ((left : ℝ) : ℂ) - (R : ℂ) * I
  let w : ℂ := ((3 : ℝ) : ℂ) + (R : ℂ) * I
  have hRpos : 0 < R := (abs_nonneg rho.im).trans_lt hheight
  have hfinite := pintz2023Equation42_finite_rectangle_residue
    (X := X) (lambda := lambda) hrhoOne hrhoZero hleft hright hheight
  change RectangleIntegral' (pintz2023Equation42Integrand X rho lambda) z w = _
  rw [← hfinite]
  apply RectangleIntegral'_congr
  intro s hs
  have hsZero : s ≠ 0 := by
    intro hs0
    rw [hs0] at hs
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff] at hs
    rcases hs with ((hBottom | hLeft) | hTop) | hRight
    · have : (0 : ℝ) = -R := by simpa [z, w] using hBottom.2
      linarith
    · have : (0 : ℝ) = left := by simpa [z, w] using hLeft.1
      linarith
    · have : (0 : ℝ) = R := by simpa [z, w] using hTop.2
      linarith
    · have : (0 : ℝ) = 3 := by simpa [z, w] using hRight.1
      norm_num at this
  have hsPole : s ≠ 1 - rho := by
    intro hsp
    rw [hsp] at hs
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff] at hs
    rcases hs with ((hBottom | hLeft) | hTop) | hRight
    · have heq : -rho.im = -R := by simpa [z, w] using hBottom.2
      have hrho : rho.im = R := by linarith
      rw [hrho, abs_of_pos hRpos] at hheight
      exact (lt_irrefl R hheight).elim
    · have : 1 - rho.re = left := by simpa [z, w] using hLeft.1
      linarith
    · have heq : -rho.im = R := by simpa [z, w] using hTop.2
      have hrho : rho.im = -R := by linarith
      rw [hrho, abs_neg, abs_of_pos hRpos] at hheight
      exact (lt_irrefl R hheight).elim
    · have : 1 - rho.re = 3 := by simpa [z, w] using hRight.1
      linarith
  exact (pintz2023PoleNumerator_div_eq_source
    hrhoOne hrhoZero hsZero hsPole).symm

/-- Expansion of the normalized rectangle integral into its four oriented
edges. -/
theorem pintz2023RectangleIntegral'_eq_edges
    (f : ℂ → ℂ) (a b R : ℝ) :
    RectangleIntegral' f
        (((a : ℝ) : ℂ) - (R : ℂ) * I)
        (((b : ℝ) : ℂ) + (R : ℂ) * I) =
      HIntegral' f a b (-R) - HIntegral' f a b R +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) := by
  unfold RectangleIntegral' RectangleIntegral HIntegral' HIntegral VIntegral
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

set_option maxHeartbeats 800000 in
/-- Complete-line contour displacement in Pintz (4.2), isolated from the
later analytic estimates.  Its hypotheses are precisely absolute
integrability of the two literal vertical lines and decay of the two
literal horizontal edges; later modules discharge them quantitatively. -/
theorem pintz2023Equation42_complete_shift
    {X : ℕ} {rho : ℂ} {lambda left : ℝ}
    (hrhoOne : rho ≠ 1) (hrhoZero : riemannZeta rho = 0)
    (hleftZero : left < 0)
    (hleft : left < 1 - rho.re) (hright : 1 - rho.re < 3)
    (hrightInt : Integrable (fun u : ℝ =>
      pintz2023Equation42Integrand X rho lambda
        (((3 : ℝ) : ℂ) + (u : ℂ) * I)))
    (hleftInt : Integrable (fun u : ℝ =>
      pintz2023Equation42Integrand X rho lambda
        (((left : ℝ) : ℂ) + (u : ℂ) * I)))
    (hbottom : Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023Equation42Integrand X rho lambda)
        left 3 (-R)) atTop (nhds 0))
    (htop : Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023Equation42Integrand X rho lambda)
        left 3 R) atTop (nhds 0)) :
    pintz2023Equation42Integral X rho lambda =
      VerticalIntegral'
        (pintz2023Equation42Integrand X rho lambda) left +
          pintz2023PoleResidue X rho lambda := by
  let f : ℂ → ℂ := pintz2023Equation42Integrand X rho lambda
  let right : ℝ → ℂ := fun u => f (((3 : ℝ) : ℂ) + (u : ℂ) * I)
  let leftLine : ℝ → ℂ := fun u => f ((left : ℂ) + (u : ℂ) * I)
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hrightInt' : Integrable right := by simpa [right, f] using hrightInt
  have hleftInt' : Integrable leftLine := by simpa [leftLine, f] using hleftInt
  have hrightLimit : Tendsto (fun R : ℝ =>
      ∫ u in (-R)..R, right u) atTop (nhds (∫ u : ℝ, right u)) :=
    intervalIntegral_tendsto_integral hrightInt' tendsto_neg_atTop_atBot tendsto_id
  have hleftLimit : Tendsto (fun R : ℝ =>
      ∫ u in (-R)..R, leftLine u) atTop (nhds (∫ u : ℝ, leftLine u)) :=
    intervalIntegral_tendsto_integral hleftInt' tendsto_neg_atTop_atBot tendsto_id
  have heventually : ∀ᶠ R : ℝ in atTop, |rho.im| < R :=
    eventually_gt_atTop |rho.im|
  have hfinite : ∀ᶠ R : ℝ in atTop,
      HIntegral' f left 3 (-R) - HIntegral' f left 3 R +
          c * (∫ u in (-R)..R, right u) -
          c * (∫ u in (-R)..R, leftLine u) =
        pintz2023PoleResidue X rho lambda := by
    filter_upwards [heventually] with R hR
    have hrect := pintz2023Equation42_finite_source_rectangle
      (X := X) (lambda := lambda) hrhoOne hrhoZero hleftZero hleft hright hR
    rw [pintz2023RectangleIntegral'_eq_edges] at hrect
    simpa [f, right, leftLine, c] using hrect
  have hlimit : Tendsto (fun R : ℝ =>
      HIntegral' f left 3 (-R) - HIntegral' f left 3 R +
          c * (∫ u in (-R)..R, right u) -
          c * (∫ u in (-R)..R, leftLine u)) atTop
      (nhds (c * (∫ u : ℝ, right u) -
        c * (∫ u : ℝ, leftLine u))) := by
    convert (((hbottom.sub htop).add
      (tendsto_const_nhds.mul hrightLimit)).sub
        (tendsto_const_nhds.mul hleftLimit)) using 1
    all_goals simp
  have hconstant : Tendsto (fun _R : ℝ =>
      pintz2023PoleResidue X rho lambda) atTop
      (nhds (pintz2023PoleResidue X rho lambda)) := tendsto_const_nhds
  have heq : c * (∫ u : ℝ, right u) -
      c * (∫ u : ℝ, leftLine u) =
        pintz2023PoleResidue X rho lambda := by
    exact tendsto_nhds_unique hlimit
      (hconstant.congr' (hfinite.mono fun _R hR => hR.symm))
  unfold pintz2023Equation42Integral VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  change (1 / (2 * Real.pi * I) : ℂ) *
      (I * (∫ u : ℝ, right u)) =
    (1 / (2 * Real.pi * I) : ℂ) *
      (I * (∫ u : ℝ, leftLine u)) + pintz2023PoleResidue X rho lambda
  have hc : (1 / (2 * Real.pi * I) : ℂ) * I = c := by
    dsimp [c]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hc, ← mul_assoc, hc]
  linear_combination heq

#print axioms pintz2023PoleNumerator_div_eq_source
#print axioms differentiableAt_pintz2023PoleNumerator
#print axioms pintz2023PoleNumerator_at_pole
#print axioms pintz2023Equation42_finite_rectangle_residue
#print axioms pintz2023Equation42_finite_source_rectangle
#print axioms pintz2023Equation42_complete_shift

end

end GafniTao
