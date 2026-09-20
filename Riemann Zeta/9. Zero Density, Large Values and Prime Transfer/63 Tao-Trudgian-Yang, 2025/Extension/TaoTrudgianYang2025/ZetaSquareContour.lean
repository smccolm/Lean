import GuthMaynard.SmoothZetaAFE

/-!
Adapted from the adjacent Gafni--Tao one-sided contour proof, using the
canonical Lean 4.30 foundation directly. This proves an exact contour step;
it is not the uniform local mean-square estimate or the twelfth moment.

# The one-sided zeta-square contour

The local second-moment argument opens `zeta(s)^2`, rather than opening the
product of two independently shifted zeta functions.  Its reflected contour
is the corresponding square at height `-t`.  This is the source of the
ordinary divisor coefficient in the Atkinson sum.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace TaoTrudgianYang2025

noncomputable section

open RiemannZeta.GuthMaynard

/-- Pole normalization for one squared completed zeta factor. -/
noncomputable def zetaSquarePoleNormalization (t : ℝ) : ℂ :=
  (afeCriticalPoint t * (1 - afeCriticalPoint t)) ^ 2

theorem zetaSquarePoleNormalization_ne_zero (t : ℝ) :
    zetaSquarePoleNormalization t ≠ 0 := by
  unfold zetaSquarePoleNormalization
  exact pow_ne_zero 2 (mul_ne_zero (afeCriticalPoint_ne_zero t)
    (sub_ne_zero.mpr (afeCriticalPoint_ne_one t).symm))

theorem zetaSquarePoleNormalization_neg (t : ℝ) :
    zetaSquarePoleNormalization (-t) =
      zetaSquarePoleNormalization t := by
  unfold zetaSquarePoleNormalization
  rw [show afeCriticalPoint (-t) = 1 - afeCriticalPoint t by
    symm
    exact one_sub_afeCriticalPoint t]
  ring

theorem zetaSquarePoleNormalization_eq (t : ℝ) :
    zetaSquarePoleNormalization t = (((1 / 4 + t ^ 2) ^ 2 : ℝ) : ℂ) := by
  unfold zetaSquarePoleNormalization afeCriticalPoint
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem zetaSquarePoleNormalization_norm_lower (t : ℝ) :
    1 / 16 ≤ ‖zetaSquarePoleNormalization t‖ := by
  rw [zetaSquarePoleNormalization_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

/-- Entire numerator for the one-sided squared-zeta AFE. -/
noncomputable def zetaSquareContourNumerator
    (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    completedXiNumerator (afeCriticalPoint t + w) ^ 2 /
      zetaSquarePoleNormalization t

theorem differentiable_zetaSquareContourNumerator (t : ℝ) :
    Differentiable ℂ (zetaSquareContourNumerator t) := by
  unfold zetaSquareContourNumerator
  have hshift : Differentiable ℂ (fun w : ℂ => afeCriticalPoint t + w) := by
    fun_prop
  have hxi : Differentiable ℂ
      (fun w : ℂ => completedXiNumerator (afeCriticalPoint t + w)) :=
    fun w => differentiable_completedXiNumerator.differentiableAt.comp w
      (hshift w)
  have haux : Differentiable ℂ hughesYoungAuxiliaryZero :=
    differentiable_hughesYoungAuxiliaryZero
  fun_prop (disch := assumption)

/-- Functional-equation reflection of the one-sided numerator. -/
theorem zetaSquareContourNumerator_neg (t : ℝ) (w : ℂ) :
    zetaSquareContourNumerator t (-w) =
      zetaSquareContourNumerator (-t) w := by
  unfold zetaSquareContourNumerator
  rw [show afeCriticalPoint t + -w =
      1 - (afeCriticalPoint (-t) + w) by
        unfold afeCriticalPoint
        push_cast
        ring,
    completedXiNumerator_one_sub, hughesYoungAuxiliaryZero_neg,
    zetaSquarePoleNormalization_neg]
  simp only [neg_sq]

/-- The residue is the literal square of the completed zeta value. -/
theorem zetaSquareContourNumerator_zero (t : ℝ) :
    zetaSquareContourNumerator t 0 =
      completedRiemannZeta (afeCriticalPoint t) ^ 2 := by
  simp only [zetaSquareContourNumerator,
    zero_pow (by decide : 2 ≠ 0), mul_zero, exp_zero,
    hughesYoungAuxiliaryZero_zero, one_mul, add_zero]
  rw [completedXiNumerator_eq _
      (afeCriticalPoint_ne_zero t) (afeCriticalPoint_ne_one t)]
  rw [div_eq_iff (zetaSquarePoleNormalization_ne_zero t)]
  unfold zetaSquarePoleNormalization
  ring

noncomputable def zetaSquareContourIntegrand
    (t : ℝ) (w : ℂ) : ℂ :=
  zetaSquareContourNumerator t w / w

/-- Reflection changes the sign of the Cauchy kernel and the height. -/
theorem zetaSquareContourIntegrand_neg (t : ℝ) (w : ℂ) :
    zetaSquareContourIntegrand t (-w) =
      -zetaSquareContourIntegrand (-t) w := by
  unfold zetaSquareContourIntegrand
  rw [zetaSquareContourNumerator_neg]
  by_cases hw : w = 0
  · simp [hw]
  · field_simp

/-- Exact residue theorem for the one-sided square. -/
theorem zetaSquare_finiteRectangle
    (t : ℝ) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    RectangleIntegral'
        (fun w : ℂ => zetaSquareContourNumerator t w / w)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      completedRiemannZeta (afeCriticalPoint t) ^ 2 := by
  let F : ℂ → ℂ := zetaSquareContourNumerator t
  let z : ℂ := (-c : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  have hF : Differentiable ℂ F :=
    differentiable_zetaSquareContourNumerator t
  have hzero : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm,
      uIoo_of_le (by simp [z, w]; linarith : z.re ≤ w.re),
      uIoo_of_le (by simp [z, w]; linarith : z.im ≤ w.im)]
    simp [z, w, hc, hH]
  have hdslope : HolomorphicOn (dslope F 0) (Rectangle z w) := by
    change DifferentiableOn ℂ (dslope F 0) (Rectangle z w)
    rw [differentiableOn_dslope
      (show Rectangle z w ∈ 𝓝 (0 : ℂ) from hzero)]
    exact hF.differentiableOn
  have hprincipal : Set.EqOn
      ((fun u : ℂ => F u / u) - fun u => F 0 / (u - 0))
      (dslope F 0) (Rectangle z w \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    rw [Pi.sub_apply, dslope_of_ne F hu0]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp
  have hrect := ResidueTheoremOnRectangleWithSimplePole
    (f := fun u : ℂ => F u / u) (g := dslope F 0)
    (p := 0) (A := F 0)
    (zRe_le_wRe := by simp [z, w]; linarith)
    (zIm_le_wIm := by simp [z, w]; linarith)
    hzero hdslope hprincipal
  simpa [F, z, w, zetaSquareContourNumerator_zero] using hrect


end

end TaoTrudgianYang2025
