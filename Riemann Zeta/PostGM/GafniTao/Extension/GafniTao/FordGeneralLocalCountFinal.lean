import GafniTao.FordGeneralLocalCountLow

/-!
# A qualitative source-form local zero-count lemma

The result below has exactly the scale needed by the Vinogradov--Korobov
argument: `B R^(3/2) log t`, `log A`, `log(1/R)`, and `log log t`.
All constants remain explicit, including the kernel-defined positive
cotangent minimum.
-/

namespace GafniTao

noncomputable section

noncomputable def fordGeneralLocalCountNumerator
    (A B t R : ℝ) : ℝ :=
  1 / (6421 / 10000 : ℝ) + 3 +
    Real.log (1 + 1 / (3 * R)) +
    2 * (Real.log A +
      B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t +
      (2 / 3 : ℝ) * Real.log (Real.log t)) +
    (B * (2 * R) ^ (3 / 2 : ℝ) + 2 / 3) *
      fordSechLogMoment

noncomputable def fordGeneralLocalCountMajorant
    (A B t R : ℝ) : ℝ :=
  fordGeneralLocalCountNumerator A B t R /
    fordLocalCotUniformLowerConstant

theorem fordGeneralLocalCountNumerator_nonneg
    {A B t R : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 100 ≤ t) (hR : 0 < R) :
    0 ≤ fordGeneralLocalCountNumerator A B t R := by
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hloglogt : 0 ≤ Real.log (Real.log t) := by
    apply Real.log_nonneg
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans_le (by norm_num)
    exact hlogThree.le.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < t by linarith) (by linarith))
  have hlogR : 0 ≤ Real.log (1 + 1 / (3 * R)) := by
    apply Real.log_nonneg
    have : 0 ≤ 1 / (3 * R) := by positivity
    linarith
  have halpha : 0 ≤ 1 / (6421 / 10000 : ℝ) := by norm_num
  have hpow : 0 ≤ (2 * R) ^ (3 / 2 : ℝ) := by positivity
  have hBterm :
      0 ≤ B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t := by positivity
  have hq : 0 ≤ B * (2 * R) ^ (3 / 2 : ℝ) + 2 / 3 := by positivity
  have hmoment :
      0 ≤ (B * (2 * R) ^ (3 / 2 : ℝ) + 2 / 3) *
        fordSechLogMoment :=
    mul_nonneg hq fordSechLogMoment_nonneg
  unfold fordGeneralLocalCountNumerator
  nlinarith

set_option maxHeartbeats 1400000 in
/-- Ford's local disk contains at most the displayed qualitative Richert
majorant, with analytic multiplicity. -/
theorem fordLocalDiskZeroCount_le_general_majorant
    {A B t R : ℝ} (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 100 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4) :
    (fordLocalDiskZeroCount t R : ℝ) <
      fordGeneralLocalCountMajorant A B t R := by
  have ht3 : 3 ≤ t := by linarith
  let ε : ℝ := 1 / R
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨eta, hetaLow, hetaHigh, hraw⟩ :=
    exists_fordLocalDiskZeroCount_general_raw_bound
      hFord hA hB ht3 hR hRUpper ε hε
  let d : ℝ := eta - (6421 / 10000 : ℝ) * R
  have hetaPos : 0 < eta := by nlinarith
  have hetaUpper : eta ≤ 3 * R := by nlinarith
  have hdNonneg : 0 ≤ d := by dsimp [d]; nlinarith
  have hdUpper : d ≤ 2 * R := by dsimp [d]; nlinarith
  have hpow : d ^ (3 / 2 : ℝ) ≤ (2 * R) ^ (3 / 2 : ℝ) := by
    exact Real.rpow_le_rpow hdNonneg hdUpper (by norm_num)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hloglogt : 0 ≤ Real.log (Real.log t) := by
    apply Real.log_nonneg
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans_le (by norm_num)
    exact hlogThree.le.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < t by linarith) (by linarith))
  have hbaseNonneg :
      0 ≤ Real.log A + B * d ^ (3 / 2 : ℝ) * Real.log t +
        (2 / 3 : ℝ) * Real.log (Real.log t) := by
    have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
    positivity
  have hqNonneg : 0 ≤ B * d ^ (3 / 2 : ℝ) + 2 / 3 := by
    positivity
  have hbracketNonneg :
      0 ≤ 2 * (Real.log A + B * d ^ (3 / 2 : ℝ) * Real.log t +
          (2 / 3 : ℝ) * Real.log (Real.log t)) +
        (B * d ^ (3 / 2 : ℝ) + 2 / 3) * fordSechLogMoment := by
    have hm := mul_nonneg hqNonneg fordSechLogMoment_nonneg
    nlinarith
  have hpole :
      R * (eta / (Real.pi * t ^ 2)) ≤ 1 := by
    have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
    have ht0 : 0 ≤ t := by linarith
    have htSq : (100 : ℝ) ^ 2 ≤ t ^ 2 :=
      (sq_le_sq₀ (by norm_num) ht0).2 ht
    have hden : (3 : ℝ) * 100 ^ 2 ≤ Real.pi * t ^ 2 :=
      mul_le_mul hpi htSq (by norm_num) Real.pi_pos.le
    have hnum : R * eta ≤ (3 / 16 : ℝ) := by
      have hR2 : R ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
        (sq_le_sq₀ hR.le (by norm_num)).2 hRUpper
      nlinarith
    calc
      R * (eta / (Real.pi * t ^ 2)) =
          R * eta / (Real.pi * t ^ 2) := by ring
      _ ≤
          (3 / 16 : ℝ) / (Real.pi * t ^ 2) := by gcongr
      _ ≤ (3 / 16 : ℝ) / ((3 : ℝ) * 100 ^ 2) := by
        gcongr
      _ ≤ 1 := by norm_num
  have hlogRNonneg : 0 ≤ Real.log (1 + 1 / (3 * R)) := by
    apply Real.log_nonneg
    have : 0 ≤ 1 / (3 * R) := by positivity
    linarith
  have hright :
      R * (Real.log (1 + 1 / (3 * R)) / (2 * eta)) ≤
        Real.log (1 + 1 / (3 * R)) := by
    have hfac : R / (2 * eta) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 2 * eta)]
      nlinarith
    calc
      R * (Real.log (1 + 1 / (3 * R)) / (2 * eta)) =
          (R / (2 * eta)) * Real.log (1 + 1 / (3 * R)) := by ring
      _ ≤ 1 * Real.log (1 + 1 / (3 * R)) :=
        mul_le_mul_of_nonneg_right hfac hlogRNonneg
      _ = _ := one_mul _
  have hhighFactor : R / (2 * eta) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < 2 * eta)]
    nlinarith
  have hhighRaw :
      R * (2 * fordGeneralShiftedLeftHighMajorant A B eta
          (1 + (6421 / 10000 : ℝ) * R) t) ≤
        2 * (Real.log A + B * d ^ (3 / 2 : ℝ) * Real.log t +
          (2 / 3 : ℝ) * Real.log (Real.log t)) +
        (B * d ^ (3 / 2 : ℝ) + 2 / 3) * fordSechLogMoment := by
    unfold fordGeneralShiftedLeftHighMajorant
    unfold fordGeneralAffineGrowthCoefficient
    have hdelta :
        1 - (1 + (6421 / 10000 : ℝ) * R - eta) = d := by
      dsimp [d]
      ring
    rw [hdelta]
    show R * (2 * ((1 / (4 * eta)) *
      (2 * (Real.log A + B * d ^ (3 / 2 : ℝ) * Real.log t +
        (2 / 3 : ℝ) * Real.log (Real.log t)) +
      (B * d ^ (3 / 2 : ℝ) + 2 / 3) * fordSechLogMoment))) ≤ _
    rw [show R * (2 * ((1 / (4 * eta)) *
        (2 * (Real.log A + B * d ^ (3 / 2 : ℝ) * Real.log t +
          (2 / 3 : ℝ) * Real.log (Real.log t)) +
        (B * d ^ (3 / 2 : ℝ) + 2 / 3) * fordSechLogMoment))) =
      (R / (2 * eta)) *
        (2 * (Real.log A + B * d ^ (3 / 2 : ℝ) * Real.log t +
          (2 / 3 : ℝ) * Real.log (Real.log t)) +
        (B * d ^ (3 / 2 : ℝ) + 2 / 3) * fordSechLogMoment) by ring]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hhighFactor hbracketNonneg
  have hhigh :
      R * (2 * fordGeneralShiftedLeftHighMajorant A B eta
          (1 + (6421 / 10000 : ℝ) * R) t) ≤
        2 * (Real.log A +
          B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t +
          (2 / 3 : ℝ) * Real.log (Real.log t)) +
        (B * (2 * R) ^ (3 / 2 : ℝ) + 2 / 3) *
          fordSechLogMoment := by
    apply hhighRaw.trans
    have hBpow : B * d ^ (3 / 2 : ℝ) ≤
        B * (2 * R) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow hB
    have hBlog : B * d ^ (3 / 2 : ℝ) * Real.log t ≤
        B * (2 * R) ^ (3 / 2 : ℝ) * Real.log t :=
      mul_le_mul_of_nonneg_right hBpow hlogt
    have hmoment := mul_le_mul_of_nonneg_right
      (add_le_add_right hBpow (2 / 3)) fordSechLogMoment_nonneg
    linarith
  have hlow := fordShiftedLeftLowMajorant_mul_R_le_one
    ht hR hRUpper hetaLow hetaHigh
  have hmul := mul_lt_mul_of_pos_right hraw hR
  have hscaled :
      (fordLocalDiskZeroCount t R : ℝ) *
          fordLocalCotUniformLowerConstant <
        fordGeneralLocalCountNumerator A B t R := by
    dsimp [ε] at hmul
    unfold fordGeneralLocalCountNumerator
    have halpha :
        R * (1 / ((6421 / 10000 : ℝ) * R)) =
          1 / (6421 / 10000 : ℝ) := by
      field_simp [hR.ne']
    have hleft :
        (fordLocalDiskZeroCount t R : ℝ) *
          (fordLocalCotUniformLowerConstant / R) * R =
        (fordLocalDiskZeroCount t R : ℝ) *
          fordLocalCotUniformLowerConstant := by
      field_simp [hR.ne']
    have heps : R * (1 / R) = 1 := by field_simp [hR.ne']
    have hrightExpanded :
        (1 / ((6421 / 10000 : ℝ) * R) +
              eta / (Real.pi * t ^ 2) +
              Real.log (1 + 1 / (3 * R)) / (2 * eta) +
              2 * fordGeneralShiftedLeftHighMajorant A B eta
                (1 + (6421 / 10000 : ℝ) * R) t +
              fordShiftedLeftLowMajorant eta t
                (eta - (6421 / 10000 : ℝ) * R) +
              1 / R) * R =
          1 / (6421 / 10000 : ℝ) +
            R * (eta / (Real.pi * t ^ 2)) +
            R * (Real.log (1 + 1 / (3 * R)) / (2 * eta)) +
            R * (2 * fordGeneralShiftedLeftHighMajorant A B eta
              (1 + (6421 / 10000 : ℝ) * R) t) +
            R * fordShiftedLeftLowMajorant eta t
              (eta - (6421 / 10000 : ℝ) * R) + 1 := by
      calc
        _ = R * (1 / ((6421 / 10000 : ℝ) * R)) +
            R * (eta / (Real.pi * t ^ 2)) +
            R * (Real.log (1 + 1 / (3 * R)) / (2 * eta)) +
            R * (2 * fordGeneralShiftedLeftHighMajorant A B eta
              (1 + (6421 / 10000 : ℝ) * R) t) +
            R * fordShiftedLeftLowMajorant eta t
              (eta - (6421 / 10000 : ℝ) * R) + R * (1 / R) := by ring
        _ = _ := by rw [halpha, heps]
    rw [hleft, hrightExpanded] at hmul
    linarith
  unfold fordGeneralLocalCountMajorant
  rw [lt_div_iff₀ fordLocalCotUniformLowerConstant_pos]
  simpa [mul_comm] using hscaled

#print axioms fordLocalDiskZeroCount_le_general_majorant

end

end GafniTao
