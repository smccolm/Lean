import GafniTao.FordGeneralLocalCount

/-!
# Uniform control of the compact left-edge remainder

The finite selected contour crosses the bounded-height strip.  Its exact
contribution has an exponentially small `sech²` factor.  The following
elementary fourth-power estimate makes that smallness uniform in
`0 < R ≤ 1/4`.
-/

namespace GafniTao

noncomputable section

theorem real_exp_neg_le_256_div_pow_four
    {z : ℝ} (hz : 0 < z) :
    Real.exp (-z) ≤ 256 / z ^ 4 := by
  have hbase : z / 4 ≤ Real.exp (z / 4) := by
    have h := Real.add_one_le_exp (z / 4)
    linarith
  have hbaseNonneg : 0 ≤ z / 4 := by positivity
  have hpow := pow_le_pow_left₀ hbaseNonneg hbase 4
  have hexpPow : Real.exp (z / 4) ^ 4 = Real.exp z := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hlower : z ^ 4 / 256 ≤ Real.exp z := by
    rw [hexpPow] at hpow
    nlinarith [sq_nonneg (z ^ 2)]
  have hleftPos : 0 < z ^ 4 / 256 := by positivity
  have hinv : 1 / Real.exp z ≤ 1 / (z ^ 4 / 256) :=
    one_div_le_one_div_of_le hleftPos hlower
  rw [Real.exp_neg]
  calc
    (Real.exp z)⁻¹ ≤ (z ^ 4 / 256)⁻¹ := by
      simpa [one_div] using hinv
    _ = 256 / z ^ 4 := by field_simp [ne_of_gt hz]

set_option maxHeartbeats 800000 in
/-- For Ford's selected range of `eta`, the entire compact left-edge term
contributes at most one after multiplication by `R`. -/
theorem fordShiftedLeftLowMajorant_mul_R_le_one
    {eta t R : ℝ} (ht : 100 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4)
    (hetaLow : (5 / 2 : ℝ) * R < eta)
    (hetaHigh : eta < (51 / 20 : ℝ) * R) :
    R * fordShiftedLeftLowMajorant eta t
        (eta - (6421 / 10000 : ℝ) * R) ≤ 1 := by
  let d : ℝ := eta - (6421 / 10000 : ℝ) * R
  let z : ℝ := Real.pi * (t - 3) / eta
  have hetaPos : 0 < eta := by nlinarith
  have hd : R < d := by dsimp [d]; nlinarith
  have hdPos : 0 < d := hR.trans hd
  have htGapPos : 0 < t - 3 := by linarith
  have hz : 0 < z := by
    dsimp [z]
    exact div_pos (mul_pos Real.pi_pos htGapPos) hetaPos
  have hexp := real_exp_neg_le_256_div_pow_four hz
  have hscaleEq :
      2 * fordDetectorPhysicalScale eta t 3 = -z := by
    dsimp [z]
    unfold fordDetectorPhysicalScale
    field_simp [hetaPos.ne']
    ring
  rw [← hscaleEq] at hexp
  have hxPos : 0 < 4 / d + 8 := by positivity
  have hlog : Real.log (4 / d + 8) ≤ 4 / d + 8 := by
    have h := Real.log_le_sub_one_of_pos hxPos
    linarith
  have hdiv : 4 / d ≤ 4 / R := by
    gcongr
  have hlogCoarse : Real.log (4 / d + 8) ≤ 4 / R + 8 :=
    hlog.trans (by linarith)
  have hlogNonneg : 0 ≤ Real.log (4 / d + 8) := by
    apply Real.log_nonneg
    have hdivPos : 0 < 4 / d := div_pos (by norm_num) hdPos
    have : 1 ≤ 4 / d + 8 := by linarith
    exact this
  have hetaUpper : eta ≤ 3 * R := by nlinarith
  have htGap : 97 ≤ t - 3 := by linarith
  have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
  have htargetEq :
      R * ((1 / (4 * eta)) *
        ((24 * Real.pi / (2 * eta)) *
          Real.log (4 / d + 8) * (256 / z ^ 4))) =
        768 * R * eta ^ 2 * Real.log (4 / d + 8) /
          (Real.pi ^ 3 * (t - 3) ^ 4) := by
    dsimp [z]
    field_simp [hetaPos.ne', Real.pi_ne_zero,
      ne_of_gt (by linarith : 0 < t - 3)]
    ring
  unfold fordShiftedLeftLowMajorant
  change R *
      ((1 / (4 * eta)) *
        ((24 * Real.pi / (2 * eta)) *
          Real.log (4 / d + 8) *
            Real.exp (2 * fordDetectorPhysicalScale eta t 3))) ≤ 1
  calc
    R * ((1 / (4 * eta)) *
        ((24 * Real.pi / (2 * eta)) *
          Real.log (4 / d + 8) *
            Real.exp (2 * fordDetectorPhysicalScale eta t 3))) ≤
      R * ((1 / (4 * eta)) *
        ((24 * Real.pi / (2 * eta)) *
          Real.log (4 / d + 8) * (256 / z ^ 4))) := by
        gcongr
    _ = 768 * R * eta ^ 2 * Real.log (4 / d + 8) /
          (Real.pi ^ 3 * (t - 3) ^ 4) := htargetEq
    _ ≤ 768 * R * (3 * R) ^ 2 * (4 / R + 8) /
          (3 ^ 3 * 97 ^ 4) := by
      gcongr
    _ ≤ 1 := by
      have hRNonneg : 0 ≤ R := hR.le
      have hR2 : R ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
        (sq_le_sq₀ hRNonneg (by norm_num)).2 hRUpper
      have hR3 : R ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := by
        exact pow_le_pow_left₀ hRNonneg hRUpper 3
      field_simp [hR.ne']
      nlinarith

#print axioms real_exp_neg_le_256_div_pow_four
#print axioms fordShiftedLeftLowMajorant_mul_R_le_one

end

end GafniTao
