import GafniTao.FordGeneralLocalCountFinal

/-!
# Source-scale normalization of Ford's local zero count

Ford's next argument integrates the local disk count over its radius.  This
file packages the exact count proved in `FordGeneralLocalCountFinal` into a
single nonnegative Richert-scale expression.  The constant below is explicit
and depends only on the two fixed detector integrals; no zero-density or
zero-free statement is assumed.
-/

namespace GafniTao

noncomputable section

noncomputable def fordGeneralLocalCountScale
    (A B t R : ℝ) : ℝ :=
  1 + Real.log A - Real.log R + Real.log (Real.log t) +
    B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t

noncomputable def fordGeneralLocalCountConstant : ℝ :=
  (8 + 3 * fordSechLogMoment) /
    fordLocalCotUniformLowerConstant

theorem fordGeneralLocalCountConstant_pos :
    0 < fordGeneralLocalCountConstant := by
  unfold fordGeneralLocalCountConstant
  apply div_pos
  · linarith [fordSechLogMoment_nonneg]
  · exact fordLocalCotUniformLowerConstant_pos

theorem fordGeneralLocalCountScale_nonneg
    {A B t R : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 100 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4) :
    0 ≤ fordGeneralLocalCountScale A B t R := by
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogR : Real.log R ≤ 0 :=
    Real.log_nonpos hR.le (by linarith)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hloglogt : 0 ≤ Real.log (Real.log t) := by
    apply Real.log_nonneg
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans_le (by norm_num)
    exact hlogThree.le.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < t by linarith) (by linarith))
  have hmain :
      0 ≤ B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t := by
    positivity
  unfold fordGeneralLocalCountScale
  linarith

theorem fordGeneralLocalCountNumerator_le_scale
    {A B t R : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 100 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4) :
    fordGeneralLocalCountNumerator A B t R ≤
      (8 + 3 * fordSechLogMoment) *
        fordGeneralLocalCountScale A B t R := by
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogR : Real.log R ≤ 0 :=
    Real.log_nonpos hR.le (by linarith)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hloglogt : 0 ≤ Real.log (Real.log t) := by
    apply Real.log_nonneg
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans_le (by norm_num)
    exact hlogThree.le.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < t by linarith) (by linarith))
  have hpow : 0 ≤ (2 * R) ^ (3 / 2 : ℝ) := by positivity
  have hmain :
      0 ≤ B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t := by
    positivity
  have hmoment := fordSechLogMoment_nonneg
  have hlogRecip :
      Real.log (1 + 1 / (3 * R)) ≤ -Real.log R := by
    have hR23 : R ≤ 2 / 3 := hRUpper.trans (by norm_num)
    have harg : 1 + 1 / (3 * R) ≤ 1 / R := by
      field_simp [hR.ne']
      nlinarith
    have hleft : 0 < 1 + 1 / (3 * R) := by positivity
    have hright : 0 < 1 / R := by positivity
    calc
      Real.log (1 + 1 / (3 * R)) ≤ Real.log (1 / R) :=
        Real.strictMonoOn_log.monotoneOn hleft hright harg
      _ = -Real.log R := by rw [Real.log_div (by norm_num) hR.ne', Real.log_one]; ring
  have halpha : 1 / (6421 / 10000 : ℝ) ≤ 2 := by norm_num
  have hupper :
      fordGeneralLocalCountNumerator A B t R ≤
        5 - Real.log R + 2 * Real.log A + 2 *
          (B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t) +
          (4 / 3 : ℝ) * Real.log (Real.log t) +
          fordSechLogMoment *
            (B * (2 * R) ^ (3 / 2 : ℝ) + 2 / 3) := by
    unfold fordGeneralLocalCountNumerator
    nlinarith [mul_nonneg hmoment
      (by positivity : 0 ≤ B * (2 * R) ^ (3 / 2 : ℝ))]
  apply hupper.trans
  unfold fordGeneralLocalCountScale
  have hMnegLog := mul_nonneg hmoment (neg_nonneg.mpr hlogR)
  have hMlogA := mul_nonneg hmoment hlogA
  have hMloglog := mul_nonneg hmoment hloglogt
  have hMmain := mul_nonneg hmoment hmain
  have hlogtOne : 1 ≤ Real.log t := by
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans_le (by norm_num)
    exact hlogThree.le.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < t by linarith) (by linarith))
  have hBpow : 0 ≤ B * (2 * R) ^ (3 / 2 : ℝ) := by positivity
  have hBpowMain : B * (2 * R) ^ (3 / 2 : ℝ) ≤
      B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t := by
    nlinarith
  have hMBpowMain := mul_le_mul_of_nonneg_left hBpowMain hmoment
  nlinarith

/-- Ford's literal local count, in the qualitative source normalization used
by the radius-integration argument. -/
theorem fordLocalDiskZeroCount_le_general_scale
    {A B t R : ℝ} (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 100 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4) :
    (fordLocalDiskZeroCount t R : ℝ) <
      fordGeneralLocalCountConstant *
        fordGeneralLocalCountScale A B t R := by
  have hraw := fordLocalDiskZeroCount_le_general_majorant
    hFord hA hB ht hR hRUpper
  have hnum := fordGeneralLocalCountNumerator_le_scale
    hA hB ht hR hRUpper
  unfold fordGeneralLocalCountMajorant at hraw
  unfold fordGeneralLocalCountConstant
  apply hraw.trans_le
  calc
    fordGeneralLocalCountNumerator A B t R /
          fordLocalCotUniformLowerConstant ≤
        ((8 + 3 * fordSechLogMoment) *
          fordGeneralLocalCountScale A B t R) /
            fordLocalCotUniformLowerConstant :=
      div_le_div_of_nonneg_right hnum
        fordLocalCotUniformLowerConstant_pos.le
    _ = (8 + 3 * fordSechLogMoment) /
          fordLocalCotUniformLowerConstant *
            fordGeneralLocalCountScale A B t R := by ring

#print axioms fordLocalDiskZeroCount_le_general_scale

end

end GafniTao
