import RiemannZeta.GuthMaynard.SmoothZetaAFE

/-!
# The two-factor completed-zeta contour for Heath--Brown's local mean square

Heath--Brown's proof of the discrete twelfth moment starts from a local
second moment of zeta.  This file specializes the frozen completed-xi contour
machinery to the product at the conjugate critical-line points.  In
particular, the residue below is the actual completed zeta square; it is not
an abstract input standing in for the source estimate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The polynomial factor which removes the two completed-zeta poles in the
two-factor contour. -/
noncomputable def heathBrownZetaSquarePoleNormalization (t : ℝ) : ℂ :=
  afeCriticalPoint t * (1 - afeCriticalPoint t) *
    afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))

theorem heathBrownZetaSquarePoleNormalization_ne_zero (t : ℝ) :
    heathBrownZetaSquarePoleNormalization t ≠ 0 := by
  unfold heathBrownZetaSquarePoleNormalization
  repeat' apply mul_ne_zero
  · exact afeCriticalPoint_ne_zero t
  · exact sub_ne_zero.mpr (afeCriticalPoint_ne_one t).symm
  · exact afeCriticalPoint_ne_zero (-t)
  · exact sub_ne_zero.mpr (afeCriticalPoint_ne_one (-t)).symm

/-- Entire even numerator for the source two-factor AFE.  The already-audited
Hughes--Young auxiliary polynomial has more vanishing than is needed here,
which is harmless and leaves the same Gaussian horizontal decay. -/
noncomputable def heathBrownZetaSquareContourNumerator
    (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    completedXiNumerator (afeCriticalPoint t + w) *
    completedXiNumerator (afeCriticalPoint (-t) + w) /
      heathBrownZetaSquarePoleNormalization t

theorem differentiable_heathBrownZetaSquareContourNumerator (t : ℝ) :
    Differentiable ℂ (heathBrownZetaSquareContourNumerator t) := by
  unfold heathBrownZetaSquareContourNumerator
  have hplus : Differentiable ℂ (fun w : ℂ => afeCriticalPoint t + w) := by
    fun_prop
  have hminus : Differentiable ℂ (fun w : ℂ => afeCriticalPoint (-t) + w) := by
    fun_prop
  have hxiPlus : Differentiable ℂ
      (fun w : ℂ => completedXiNumerator (afeCriticalPoint t + w)) :=
    fun w => differentiable_completedXiNumerator.differentiableAt.comp w (hplus w)
  have hxiMinus : Differentiable ℂ
      (fun w : ℂ => completedXiNumerator (afeCriticalPoint (-t) + w)) :=
    fun w => differentiable_completedXiNumerator.differentiableAt.comp w (hminus w)
  have haux : Differentiable ℂ hughesYoungAuxiliaryZero :=
    differentiable_hughesYoungAuxiliaryZero
  fun_prop (disch := assumption)

theorem heathBrownZetaSquareContourNumerator_neg (t : ℝ) (w : ℂ) :
    heathBrownZetaSquareContourNumerator t (-w) =
      heathBrownZetaSquareContourNumerator t w := by
  unfold heathBrownZetaSquareContourNumerator
  rw [show afeCriticalPoint t + -w =
      1 - (afeCriticalPoint (-t) + w) by
        unfold afeCriticalPoint
        push_cast
        ring,
    show afeCriticalPoint (-t) + -w =
      1 - (afeCriticalPoint t + w) by
        unfold afeCriticalPoint
        push_cast
        ring,
    completedXiNumerator_one_sub, completedXiNumerator_one_sub,
    hughesYoungAuxiliaryZero_neg]
  simp only [neg_sq]
  ring

/-- The central value is the product of the two completed zeta factors. -/
theorem heathBrownZetaSquareContourNumerator_zero (t : ℝ) :
    heathBrownZetaSquareContourNumerator t 0 =
      completedRiemannZeta (afeCriticalPoint t) *
        completedRiemannZeta (afeCriticalPoint (-t)) := by
  simp only [heathBrownZetaSquareContourNumerator,
    zero_pow (by decide : 2 ≠ 0), mul_zero, exp_zero,
    hughesYoungAuxiliaryZero_zero, one_mul, add_zero]
  rw [completedXiNumerator_eq _
      (afeCriticalPoint_ne_zero t) (afeCriticalPoint_ne_one t),
    completedXiNumerator_eq _
      (afeCriticalPoint_ne_zero (-t)) (afeCriticalPoint_ne_one (-t))]
  rw [div_eq_iff (heathBrownZetaSquarePoleNormalization_ne_zero t)]
  unfold heathBrownZetaSquarePoleNormalization
  ring

/-- The odd Cauchy integrand obtained from the even two-factor numerator. -/
noncomputable def heathBrownZetaSquareContourIntegrand
    (t : ℝ) (w : ℂ) : ℂ :=
  heathBrownZetaSquareContourNumerator t w / w

theorem heathBrownZetaSquareContourIntegrand_neg (t : ℝ) (w : ℂ) :
    heathBrownZetaSquareContourIntegrand t (-w) =
      -heathBrownZetaSquareContourIntegrand t w := by
  unfold heathBrownZetaSquareContourIntegrand
  rw [heathBrownZetaSquareContourNumerator_neg]
  by_cases hw : w = 0
  · simp [hw]
  · field_simp

/-- Exact finite-rectangle residue identity for the completed zeta square.
This is the two-factor analogue of the frozen fourth-moment contour theorem. -/
theorem heathBrownZetaSquare_finiteRectangle
    (t : ℝ) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    RectangleIntegral'
        (fun w : ℂ => heathBrownZetaSquareContourNumerator t w / w)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      completedRiemannZeta (afeCriticalPoint t) *
        completedRiemannZeta (afeCriticalPoint (-t)) := by
  let F : ℂ → ℂ := heathBrownZetaSquareContourNumerator t
  let z : ℂ := (-c : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  have hF : Differentiable ℂ F :=
    differentiable_heathBrownZetaSquareContourNumerator t
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
  simpa [F, z, w, heathBrownZetaSquareContourNumerator_zero] using hrect


end

end GafniTao
