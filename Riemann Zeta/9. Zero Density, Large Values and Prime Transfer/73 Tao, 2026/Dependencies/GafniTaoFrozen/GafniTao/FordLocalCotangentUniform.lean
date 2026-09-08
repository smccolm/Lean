import GafniTao.FordLocalCotangentConsumer

/-!
# Uniform local cotangent coercivity under Ford's good-shift perturbation

The contour selector replaces `eta = 2.5 R` by a nearby good shift.  We use
the whole band `2.5 R <= eta' <= 3 R`, and take the positive minimum of the
exact normalized cotangent profile on that compact parameter region.
-/

open Complex Set

namespace GafniTao

noncomputable section

def fordLocalCotParameterRegion : Set (ℝ × ℂ) :=
  Set.Icc (5 / 2 : ℝ) 3 ×ˢ fordLocalCotRegion

noncomputable def fordLocalCotUniformProfile (p : ℝ × ℂ) : ℝ :=
  let q := p.1
  let z := p.2
  let x := (Real.pi / (2 * q)) * z.re
  let y := (Real.pi / (2 * q)) * z.im
  (Real.pi / (2 * q)) *
    (Real.sin (2 * x) /
      (Real.cosh (2 * y) - Real.cos (2 * x)))

theorem fordLocalCotParameterRegion_compact :
    IsCompact fordLocalCotParameterRegion := by
  exact isCompact_Icc.prod fordLocalCotRegion_compact

theorem fordLocalCotParameterRegion_nonempty :
    fordLocalCotParameterRegion.Nonempty := by
  obtain ⟨z, hz⟩ := fordLocalCotRegion_nonempty
  exact ⟨((5 / 2 : ℝ), z), ⟨by norm_num, hz⟩⟩

private theorem fordLocalCotUniform_scaled_re_bounds
    {p : ℝ × ℂ} (hp : p ∈ fordLocalCotParameterRegion) :
    0 < 2 * ((Real.pi / (2 * p.1)) * p.2.re) ∧
      2 * ((Real.pi / (2 * p.1)) * p.2.re) < Real.pi := by
  rcases hp with ⟨hq, hz⟩
  rw [fordLocalCotRegion, mem_reProdIm] at hz
  have hqPos : 0 < p.1 := by linarith [hq.1]
  have hzPos : 0 < p.2.re := by linarith [hz.1.1]
  have hzLtQ : p.2.re < p.1 := by linarith [hz.1.2, hq.1]
  constructor
  · positivity
  · rw [show 2 * (Real.pi / (2 * p.1) * p.2.re) =
      Real.pi * (p.2.re / p.1) by field_simp [hqPos.ne']]
    have hquot : p.2.re / p.1 < 1 := (div_lt_one hqPos).mpr hzLtQ
    nlinarith [Real.pi_pos]

private theorem fordLocalCotUniform_denominator_pos
    {p : ℝ × ℂ} (hp : p ∈ fordLocalCotParameterRegion) :
    0 < Real.cosh
          (2 * ((Real.pi / (2 * p.1)) * p.2.im)) -
        Real.cos (2 * ((Real.pi / (2 * p.1)) * p.2.re)) := by
  have hx := fordLocalCotUniform_scaled_re_bounds hp
  have hxPos : 0 < (Real.pi / (2 * p.1)) * p.2.re := by linarith [hx.1]
  have hxLtPi : (Real.pi / (2 * p.1)) * p.2.re < Real.pi := by
    linarith [hx.2, Real.pi_pos]
  have hsinHalf :
      0 < Real.sin ((Real.pi / (2 * p.1)) * p.2.re) :=
    Real.sin_pos_of_pos_of_lt_pi hxPos hxLtPi
  have hcoslt :
      Real.cos (2 * ((Real.pi / (2 * p.1)) * p.2.re)) < 1 := by
    rw [Real.cos_two_mul_eq_one_sub]
    nlinarith [sq_pos_of_pos hsinHalf]
  have hcosh : 1 ≤ Real.cosh
      (2 * ((Real.pi / (2 * p.1)) * p.2.im)) := Real.one_le_cosh _
  linarith

theorem fordLocalCotUniformProfile_pos
    {p : ℝ × ℂ} (hp : p ∈ fordLocalCotParameterRegion) :
    0 < fordLocalCotUniformProfile p := by
  have hqPos : 0 < p.1 := by
    rcases hp.1 with ⟨h, _⟩
    linarith
  have hx := fordLocalCotUniform_scaled_re_bounds hp
  have hnum :
      0 < Real.sin (2 * ((Real.pi / (2 * p.1)) * p.2.re)) :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hden := fordLocalCotUniform_denominator_pos hp
  unfold fordLocalCotUniformProfile
  dsimp only
  exact mul_pos (div_pos Real.pi_pos (mul_pos (by norm_num) hqPos))
    (div_pos hnum hden)

theorem continuousOn_fordLocalCotUniformProfile :
    ContinuousOn fordLocalCotUniformProfile fordLocalCotParameterRegion := by
  have hq : ∀ p ∈ fordLocalCotParameterRegion, p.1 ≠ 0 := by
    intro p hp
    have : 0 < p.1 := by linarith [hp.1.1]
    exact this.ne'
  have hscale : ContinuousOn (fun p : ℝ × ℂ =>
      Real.pi / (2 * p.1)) fordLocalCotParameterRegion := by
    apply ContinuousOn.div continuousOn_const
      (continuous_const.mul continuous_fst).continuousOn
    intro p hp
    exact mul_ne_zero two_ne_zero (hq p hp)
  have hx : ContinuousOn (fun p : ℝ × ℂ =>
      (Real.pi / (2 * p.1)) * p.2.re)
      fordLocalCotParameterRegion :=
    hscale.mul (continuous_re.comp continuous_snd).continuousOn
  have hy : ContinuousOn (fun p : ℝ × ℂ =>
      (Real.pi / (2 * p.1)) * p.2.im)
      fordLocalCotParameterRegion :=
    hscale.mul (continuous_im.comp continuous_snd).continuousOn
  have hnum : ContinuousOn (fun p : ℝ × ℂ =>
      Real.sin (2 * ((Real.pi / (2 * p.1)) * p.2.re)))
      fordLocalCotParameterRegion :=
    Real.continuous_sin.comp_continuousOn (continuousOn_const.mul hx)
  have hden : ContinuousOn (fun p : ℝ × ℂ =>
      Real.cosh (2 * ((Real.pi / (2 * p.1)) * p.2.im)) -
        Real.cos (2 * ((Real.pi / (2 * p.1)) * p.2.re)))
      fordLocalCotParameterRegion :=
    (Real.continuous_cosh.comp_continuousOn
      (continuousOn_const.mul hy)).sub
      (Real.continuous_cos.comp_continuousOn
        (continuousOn_const.mul hx))
  unfold fordLocalCotUniformProfile
  dsimp only
  exact hscale.mul (hnum.div hden fun p hp =>
    (fordLocalCotUniform_denominator_pos hp).ne')

noncomputable def fordLocalCotUniformLowerConstant : ℝ :=
  fordLocalCotUniformProfile
    (Classical.choose
      (fordLocalCotParameterRegion_compact.exists_isMinOn
        fordLocalCotParameterRegion_nonempty
        continuousOn_fordLocalCotUniformProfile))

private theorem fordLocalCotUniformLowerConstant_minimizer_mem :
    Classical.choose
      (fordLocalCotParameterRegion_compact.exists_isMinOn
        fordLocalCotParameterRegion_nonempty
        continuousOn_fordLocalCotUniformProfile) ∈
      fordLocalCotParameterRegion :=
  (Classical.choose_spec
    (fordLocalCotParameterRegion_compact.exists_isMinOn
      fordLocalCotParameterRegion_nonempty
      continuousOn_fordLocalCotUniformProfile)).1

theorem fordLocalCotUniformLowerConstant_pos :
    0 < fordLocalCotUniformLowerConstant :=
  fordLocalCotUniformProfile_pos
    fordLocalCotUniformLowerConstant_minimizer_mem

theorem fordLocalCotUniformLowerConstant_le
    {p : ℝ × ℂ} (hp : p ∈ fordLocalCotParameterRegion) :
    fordLocalCotUniformLowerConstant ≤ fordLocalCotUniformProfile p :=
  (Classical.choose_spec
    (fordLocalCotParameterRegion_compact.exists_isMinOn
      fordLocalCotParameterRegion_nonempty
      continuousOn_fordLocalCotUniformProfile)).2 hp

theorem fordLocalCotUniformProfile_eq_complex (q : ℝ) (z : ℂ) :
    fordLocalCotUniformProfile (q, z) =
      (((Real.pi / (2 * q) : ℝ) : ℂ) *
        Complex.cot ((((Real.pi / (2 * q) : ℝ) : ℂ) * z))).re := by
  have harg : (((Real.pi / (2 * q) : ℝ) : ℂ) * z) =
      ((((Real.pi / (2 * q)) * z.re : ℝ) : ℂ) +
        (((Real.pi / (2 * q)) * z.im : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp <;> ring
  rw [mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [harg, ford_re_cot_formula]
  unfold fordLocalCotUniformProfile
  simp

end

end GafniTao
