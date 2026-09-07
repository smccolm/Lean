import GafniTao.HeathBrownZetaSquareAFE

/-!
# The one-sided zeta-square contour

The local second-moment argument opens `zeta(s)^2`, rather than opening the
product of two independently shifted zeta functions.  Its reflected contour
is the corresponding square at height `-t`.  This is the source of the
ordinary divisor coefficient in the Atkinson sum.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Pole normalization for one squared completed zeta factor. -/
noncomputable def heathBrownOneSidedPoleNormalization (t : ℝ) : ℂ :=
  (afeCriticalPoint t * (1 - afeCriticalPoint t)) ^ 2

theorem heathBrownOneSidedPoleNormalization_ne_zero (t : ℝ) :
    heathBrownOneSidedPoleNormalization t ≠ 0 := by
  unfold heathBrownOneSidedPoleNormalization
  exact pow_ne_zero 2 (mul_ne_zero (afeCriticalPoint_ne_zero t)
    (sub_ne_zero.mpr (afeCriticalPoint_ne_one t).symm))

theorem heathBrownOneSidedPoleNormalization_neg (t : ℝ) :
    heathBrownOneSidedPoleNormalization (-t) =
      heathBrownOneSidedPoleNormalization t := by
  unfold heathBrownOneSidedPoleNormalization
  rw [show afeCriticalPoint (-t) = 1 - afeCriticalPoint t by
    symm
    exact one_sub_afeCriticalPoint t]
  ring

/-- Entire numerator for the one-sided squared-zeta AFE. -/
noncomputable def heathBrownOneSidedContourNumerator
    (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    completedXiNumerator (afeCriticalPoint t + w) ^ 2 /
      heathBrownOneSidedPoleNormalization t

theorem differentiable_heathBrownOneSidedContourNumerator (t : ℝ) :
    Differentiable ℂ (heathBrownOneSidedContourNumerator t) := by
  unfold heathBrownOneSidedContourNumerator
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
theorem heathBrownOneSidedContourNumerator_neg (t : ℝ) (w : ℂ) :
    heathBrownOneSidedContourNumerator t (-w) =
      heathBrownOneSidedContourNumerator (-t) w := by
  unfold heathBrownOneSidedContourNumerator
  rw [show afeCriticalPoint t + -w =
      1 - (afeCriticalPoint (-t) + w) by
        unfold afeCriticalPoint
        push_cast
        ring,
    completedXiNumerator_one_sub, hughesYoungAuxiliaryZero_neg,
    heathBrownOneSidedPoleNormalization_neg]
  simp only [neg_sq]

/-- The residue is the literal square of the completed zeta value. -/
theorem heathBrownOneSidedContourNumerator_zero (t : ℝ) :
    heathBrownOneSidedContourNumerator t 0 =
      completedRiemannZeta (afeCriticalPoint t) ^ 2 := by
  simp only [heathBrownOneSidedContourNumerator,
    zero_pow (by decide : 2 ≠ 0), mul_zero, exp_zero,
    hughesYoungAuxiliaryZero_zero, one_mul, add_zero]
  rw [completedXiNumerator_eq _
      (afeCriticalPoint_ne_zero t) (afeCriticalPoint_ne_one t)]
  rw [div_eq_iff (heathBrownOneSidedPoleNormalization_ne_zero t)]
  unfold heathBrownOneSidedPoleNormalization
  ring

noncomputable def heathBrownOneSidedContourIntegrand
    (t : ℝ) (w : ℂ) : ℂ :=
  heathBrownOneSidedContourNumerator t w / w

/-- Reflection changes the sign of the Cauchy kernel and the height. -/
theorem heathBrownOneSidedContourIntegrand_neg (t : ℝ) (w : ℂ) :
    heathBrownOneSidedContourIntegrand t (-w) =
      -heathBrownOneSidedContourIntegrand (-t) w := by
  unfold heathBrownOneSidedContourIntegrand
  rw [heathBrownOneSidedContourNumerator_neg]
  by_cases hw : w = 0
  · simp [hw]
  · field_simp

/-- Exact residue theorem for the one-sided square. -/
theorem heathBrownOneSided_finiteRectangle
    (t : ℝ) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    RectangleIntegral'
        (fun w : ℂ => heathBrownOneSidedContourNumerator t w / w)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      completedRiemannZeta (afeCriticalPoint t) ^ 2 := by
  let F : ℂ → ℂ := heathBrownOneSidedContourNumerator t
  let z : ℂ := (-c : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  have hF : Differentiable ℂ F :=
    differentiable_heathBrownOneSidedContourNumerator t
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
  simpa [F, z, w, heathBrownOneSidedContourNumerator_zero] using hrect


end

end GafniTao
