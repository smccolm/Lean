import GafniTao.FordLocalDiskZeros
import Mathlib.Topology.Order.Compact

/-!
# A rigorous positive cotangent constant for Ford's local disk

Ford records the numerical lower bound `0.3758`, obtained in part by a
computer-algebra boundary check.  For the asymptotic zero-free argument it
is enough to retain a uniform strictly positive constant.  We obtain one as
the attained minimum of the exact cotangent profile on the compact rectangle
containing every normalized displacement in Ford's disk.
-/

open Complex Set

namespace GafniTao

noncomputable section

/-- The normalized rectangle used by Ford's parameters. -/
def fordLocalCotRegion : Set ℂ :=
  Set.Icc (6421 / 10000 : ℝ) (16421 / 10000 : ℝ) ×ℂ
    Set.Icc (-1 : ℝ) 1

/-- The real cotangent profile before the final factor `1/R`. -/
noncomputable def fordLocalCotProfile (z : ℂ) : ℝ :=
  (Real.pi / 5) *
    (Real.sin (2 * ((Real.pi / 5) * z.re)) /
      (Real.cosh (2 * ((Real.pi / 5) * z.im)) -
        Real.cos (2 * ((Real.pi / 5) * z.re))))

theorem fordLocalCotRegion_compact : IsCompact fordLocalCotRegion := by
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem fordLocalCotRegion_nonempty : fordLocalCotRegion.Nonempty := by
  refine ⟨((6421 / 10000 : ℝ) : ℂ), ?_⟩
  rw [fordLocalCotRegion, mem_reProdIm]
  simp
  norm_num

private theorem fordLocalCotRegion_scaled_re_bounds
    {z : ℂ} (hz : z ∈ fordLocalCotRegion) :
    0 < 2 * ((Real.pi / 5) * z.re) ∧
      2 * ((Real.pi / 5) * z.re) < Real.pi := by
  rw [fordLocalCotRegion, mem_reProdIm] at hz
  have hre := hz.1
  have hpi := Real.pi_pos
  constructor
  · have : 0 < z.re := by linarith [hre.1]
    positivity
  · have hzUpper : z.re < 5 / 2 := by linarith [hre.2]
    nlinarith

private theorem fordLocalCotProfile_denominator_pos
    {z : ℂ} (hz : z ∈ fordLocalCotRegion) :
    0 < Real.cosh (2 * ((Real.pi / 5) * z.im)) -
      Real.cos (2 * ((Real.pi / 5) * z.re)) := by
  have hx := fordLocalCotRegion_scaled_re_bounds hz
  have hxPos : 0 < (Real.pi / 5) * z.re := by linarith [hx.1]
  have hxLtPi : (Real.pi / 5) * z.re < Real.pi := by
    linarith [hx.2, Real.pi_pos]
  have hsinHalf : 0 < Real.sin ((Real.pi / 5) * z.re) :=
    Real.sin_pos_of_pos_of_lt_pi hxPos hxLtPi
  have hcoslt :
      Real.cos (2 * ((Real.pi / 5) * z.re)) < 1 := by
    rw [Real.cos_two_mul_eq_one_sub]
    nlinarith [sq_pos_of_pos hsinHalf]
  have hcosh : 1 ≤ Real.cosh (2 * ((Real.pi / 5) * z.im)) :=
    Real.one_le_cosh _
  linarith

theorem fordLocalCotProfile_pos
    {z : ℂ} (hz : z ∈ fordLocalCotRegion) :
    0 < fordLocalCotProfile z := by
  have hx := fordLocalCotRegion_scaled_re_bounds hz
  have hnum : 0 < Real.sin (2 * ((Real.pi / 5) * z.re)) :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hden := fordLocalCotProfile_denominator_pos hz
  unfold fordLocalCotProfile
  exact mul_pos (div_pos Real.pi_pos (by norm_num)) (div_pos hnum hden)

theorem continuousOn_fordLocalCotProfile :
    ContinuousOn fordLocalCotProfile fordLocalCotRegion := by
  have hnum : Continuous (fun z : ℂ =>
      Real.sin (2 * ((Real.pi / 5) * z.re))) := by
    fun_prop
  have hden : Continuous (fun z : ℂ =>
      Real.cosh (2 * ((Real.pi / 5) * z.im)) -
        Real.cos (2 * ((Real.pi / 5) * z.re))) := by
    fun_prop
  unfold fordLocalCotProfile
  exact continuousOn_const.mul
    (hnum.continuousOn.div hden.continuousOn fun z hz =>
      (fordLocalCotProfile_denominator_pos hz).ne')

/-- A kernel-defined positive lower bound for Ford's local cotangent
profile.  Its numerical value is deliberately not asserted. -/
noncomputable def fordLocalCotLowerConstant : ℝ :=
  fordLocalCotProfile
    (Classical.choose
      (fordLocalCotRegion_compact.exists_isMinOn
        fordLocalCotRegion_nonempty continuousOn_fordLocalCotProfile))

private theorem fordLocalCotLowerConstant_minimizer_mem :
    Classical.choose
      (fordLocalCotRegion_compact.exists_isMinOn
        fordLocalCotRegion_nonempty continuousOn_fordLocalCotProfile) ∈
      fordLocalCotRegion :=
  (Classical.choose_spec
    (fordLocalCotRegion_compact.exists_isMinOn
      fordLocalCotRegion_nonempty continuousOn_fordLocalCotProfile)).1

theorem fordLocalCotLowerConstant_pos :
    0 < fordLocalCotLowerConstant := by
  exact fordLocalCotProfile_pos fordLocalCotLowerConstant_minimizer_mem

theorem fordLocalCotLowerConstant_le
    {z : ℂ} (hz : z ∈ fordLocalCotRegion) :
    fordLocalCotLowerConstant ≤ fordLocalCotProfile z := by
  exact (Classical.choose_spec
    (fordLocalCotRegion_compact.exists_isMinOn
      fordLocalCotRegion_nonempty continuousOn_fordLocalCotProfile)).2 hz

/-- The real-formula profile is exactly Ford's complex cotangent profile. -/
theorem fordLocalCotProfile_eq_complex (z : ℂ) :
    fordLocalCotProfile z =
      (((Real.pi / 5 : ℝ) : ℂ) *
        Complex.cot ((((Real.pi / 5 : ℝ) : ℂ) * z))).re := by
  have harg : (((Real.pi / 5 : ℝ) : ℂ) * z) =
      (((Real.pi / 5) * z.re : ℝ) : ℂ) +
        (((Real.pi / 5) * z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [harg, ford_re_cot_formula]
  unfold fordLocalCotProfile
  simp

end

end GafniTao
