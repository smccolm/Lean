import GafniTao.FordLemma36LogTaylor

/-!
# Ford Lemma 3.6: logarithmic potential

Ford uses `d + log d + log (2-d)` to integrate the normalized exponent
recurrence.  This file proves its monotonicity on the relevant interval and
the exact one-step estimate with the source coefficient `2/5`.
-/

namespace GafniTao

noncomputable section

def fordPotential36 (d : ℝ) : ℝ :=
  d + Real.log d + Real.log (2 - d)

theorem fordPotential36_mono
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    fordPotential36 x ≤ fordPotential36 y := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hderiv : ∀ z ∈ Set.Icc x y,
      HasDerivAt fordPotential36
        (1 + 1 / z + (-1) / (2 - z)) z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hx hz.1
    have hz2 : 0 < 2 - z := by linarith [hz.2, hy]
    unfold fordPotential36
    convert (((hasDerivAt_id z).add (Real.hasDerivAt_log hz0.ne')).add
      (((hasDerivAt_const z (2 : ℝ)).sub (hasDerivAt_id z)).log hz2.ne')) using 1
    all_goals simp only [Pi.sub_apply, id_eq, zero_sub, one_div]
  have hmono : MonotoneOn fordPotential36 (Set.Icc x y) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
      (fun z hz => (hderiv z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hderiv z (interior_subset hz)).hasDerivWithinAt)
      (by
        intro z hz
        simp only [interior_Icc, Set.mem_Ioo] at hz
        have hz0 : 0 < z := lt_trans hx hz.1
        have hzHalf : z < 1 / 2 := lt_of_lt_of_le hz.2 hy
        have hz2 : 0 < 2 - z := by linarith
        field_simp [hz0.ne', hz2.ne']
        nlinarith)
  exact hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

theorem fordPotential36_quadratic_coefficient
    {d : ℝ} (hd0 : 0 ≤ d) (hdHalf : d ≤ 1 / 2) :
    (2 / 5 : ℝ) ≤
      ((2 - d) ^ 2 + d ^ 2) / (2 * (2 - d ^ 2) ^ 2) := by
  have hS : 0 < 2 - d ^ 2 := by nlinarith [sq_nonneg d]
  have hdSq : d ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (d - 1 / 2)]
  have hdFourth : d ^ 4 ≤ d ^ 2 / 4 := by
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSq)]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5)
    (mul_pos (by norm_num) (sq_pos_of_pos hS))]
  nlinarith [sq_nonneg (5 * d - 2)]

theorem fordPotential36_model_step
    {d b : ℝ} (hd0 : 0 < d) (hdHalf : d ≤ 1 / 2)
    (hb0 : 0 ≤ b)
    (hbSmall : (2 - d) / (2 - d ^ 2) * b < 1) :
    let d' := d * (1 - (2 - d) / (2 - d ^ 2) * b)
    fordPotential36 d' ≤ fordPotential36 d - b - (2 / 5) * b ^ 2 := by
  let S : ℝ := 2 - d ^ 2
  let a : ℝ := (2 - d) / S
  let q : ℝ := d / S
  let d' : ℝ := d * (1 - a * b)
  dsimp only
  have hdNonneg : 0 ≤ d := hd0.le
  have hS : 0 < S := by dsimp [S]; nlinarith [sq_nonneg d]
  have hTwoD : 0 < 2 - d := by linarith
  have ha0 : 0 ≤ a := div_nonneg hTwoD.le hS.le
  have hq0 : 0 ≤ q := div_nonneg hd0.le hS.le
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hqb0 : 0 ≤ q * b := mul_nonneg hq0 hb0
  have hone : 0 < 1 - a * b := by simpa [a, S] using sub_pos.mpr hbSmall
  have hd'0 : 0 < d' := mul_pos hd0 hone
  have hratio : 2 - d' = (2 - d) * (1 + q * b) := by
    dsimp [d', a, q, S]
    field_simp [ne_of_gt hS]
    ring
  have hlogD : Real.log d' = Real.log d + Real.log (1 - a * b) := by
    dsimp [d']
    exact Real.log_mul hd0.ne' hone.ne'
  have hlogTwo : Real.log (2 - d') =
      Real.log (2 - d) + Real.log (1 + q * b) := by
    rw [hratio]
    exact Real.log_mul hTwoD.ne' (by linarith [hqb0])
  have hminus := log_one_sub_le_cubic hab0 (by simpa [a, S] using hbSmall)
  have hplus := log_one_add_le_cubic hqb0
  have hraw :
      fordPotential36 d' ≤ fordPotential36 d +
        (-d * a * b - a * b - (a * b) ^ 2 / 2 - (a * b) ^ 3 / 3 +
          q * b - (q * b) ^ 2 / 2 + (q * b) ^ 3 / 3) := by
    unfold fordPotential36
    rw [hlogD, hlogTwo]
    dsimp [d']
    linarith
  have hlinear : -d * a + -a + q = -1 := by
    dsimp [a, q, S]
    have hS' : 2 - d ^ 2 ≠ 0 := by nlinarith [sq_nonneg d]
    field_simp [hS']
    ring
  have hqCoeff := fordPotential36_quadratic_coefficient hd0.le hdHalf
  have hcubic : (q * b) ^ 3 / 3 ≤ (a * b) ^ 3 / 3 := by
    have hqa : q ≤ a := by
      dsimp [q, a]
      exact div_le_div_of_nonneg_right (by linarith) hS.le
    have hmul : q * b ≤ a * b := mul_le_mul_of_nonneg_right hqa hb0
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hqb0 hmul 3) (by norm_num)
  have hquad :
      (2 / 5 : ℝ) * b ^ 2 ≤ ((a ^ 2 + q ^ 2) / 2) * b ^ 2 := by
    have hcoeff : (2 / 5 : ℝ) ≤ (a ^ 2 + q ^ 2) / 2 := by
      calc
        (2 / 5 : ℝ) ≤
            ((2 - d) ^ 2 + d ^ 2) / (2 * (2 - d ^ 2) ^ 2) := hqCoeff
        _ = (a ^ 2 + q ^ 2) / 2 := by
          dsimp [a, q, S]
          field_simp [ne_of_gt hS]
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg b)
  have htail :
      -(a * b) ^ 2 / 2 - (q * b) ^ 2 / 2 - (a * b) ^ 3 / 3 +
          (q * b) ^ 3 / 3 ≤
        -(2 / 5 : ℝ) * b ^ 2 := by
    have hnegCubic : -(a * b) ^ 3 / 3 + (q * b) ^ 3 / 3 ≤ 0 := by linarith
    have hfactor :
        -(a * b) ^ 2 / 2 - (q * b) ^ 2 / 2 =
          -((a ^ 2 + q ^ 2) / 2) * b ^ 2 := by ring
    have hquadNeg :
        -((a ^ 2 + q ^ 2) / 2) * b ^ 2 ≤ -(2 / 5 : ℝ) * b ^ 2 := by
      linarith
    rw [hfactor]
    linarith
  calc
    fordPotential36 d' ≤ fordPotential36 d +
        (-d * a * b - a * b - (a * b) ^ 2 / 2 - (a * b) ^ 3 / 3 +
          q * b - (q * b) ^ 2 / 2 + (q * b) ^ 3 / 3) := hraw
    _ = fordPotential36 d - b +
        (-(a * b) ^ 2 / 2 - (q * b) ^ 2 / 2 - (a * b) ^ 3 / 3 +
          (q * b) ^ 3 / 3) := by
      have hlinMul : -d * a * b - a * b + q * b = -b := by
        calc
          -d * a * b - a * b + q * b = (-d * a + -a + q) * b := by ring
          _ = -b := by rw [hlinear]; ring
      linarith
    _ ≤ fordPotential36 d - b - (2 / 5) * b ^ 2 := by linarith

#print axioms fordPotential36_mono
#print axioms fordPotential36_quadratic_coefficient
#print axioms fordPotential36_model_step

end

end GafniTao
