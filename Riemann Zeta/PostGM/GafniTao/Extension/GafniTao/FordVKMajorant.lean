import GafniTao.FordVKScale
import GafniTao.FordGeneralLocalCountLow

/-!
# Uniform source-scale bound for the one-zero detector error
-/

namespace GafniTao

noncomputable section

noncomputable def fordVKMajorantCoefficient (A B : ℝ) : ℝ :=
  3 + (2 * Real.log A + 18 * B + 4 / 3 +
    (9 * B + 2 / 3) * fordSechLogMoment) / 5

theorem fordVKMajorantCoefficient_pos
    {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) :
    0 < fordVKMajorantCoefficient A B := by
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hM := fordSechLogMoment_nonneg
  unfold fordVKMajorantCoefficient
  positivity

private theorem fordVK_lowMajorant_le_standard
    {eta t R lambda : ℝ} (hR : 0 < R)
    (heta : (5 / 2 : ℝ) * R < eta)
    (hlambdaUpper : lambda ≤ (6421 / 10000 : ℝ) * R) :
    fordShiftedLeftLowMajorant eta t (eta - lambda) ≤
      fordShiftedLeftLowMajorant eta t
        (eta - (6421 / 10000 : ℝ) * R) := by
  have hetaPos : 0 < eta := by nlinarith
  have hdStd : 0 < eta - (6421 / 10000 : ℝ) * R := by
    nlinarith
  have hdActual : 0 < eta - lambda :=
    lt_of_lt_of_le hdStd (sub_le_sub_left hlambdaUpper eta)
  have hdiv : 4 / (eta - lambda) ≤
      4 / (eta - (6421 / 10000 : ℝ) * R) := by
    exact div_le_div_of_nonneg_left (by norm_num) hdStd
      (sub_le_sub_left hlambdaUpper eta)
  have hargActual : 0 < 4 / (eta - lambda) + 8 := by positivity
  have hargStd : 0 < 4 / (eta - (6421 / 10000 : ℝ) * R) + 8 := by
    positivity
  have hlog : Real.log (4 / (eta - lambda) + 8) ≤
      Real.log (4 / (eta - (6421 / 10000 : ℝ) * R) + 8) :=
    Real.strictMonoOn_log.monotoneOn hargActual hargStd (by linarith)
  unfold fordShiftedLeftLowMajorant
  have hfactor : 0 ≤ (1 / (4 * eta)) * (24 * Real.pi / (2 * eta)) := by
    positivity
  have hexp : 0 ≤ Real.exp (2 * fordDetectorPhysicalScale eta t 3) :=
    (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hlog (mul_nonneg hfactor hexp)]

set_option maxHeartbeats 1200000 in
/-- Every explicit error term in the selected-zero contour is bounded by a
fixed multiple of the physical Vinogradov--Korobov denominator. -/
theorem fordGeneralDetectorMajorant_le_vinogradovKorobovDenominator
    {A B t R eta lambda : ℝ}
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 100 ≤ t)
    (hRDef : R = fordVKRadius t)
    (hbase : Real.exp (Real.exp 1) ≤ t)
    (hu : 6 ≤ fordVKLogLog t)
    (hlogu : 2 * Real.log (fordVKLogLog t) ≤ fordVKLogLog t)
    (hRUpper : R ≤ 1 / 4)
    (hetaLow : (5 / 2 : ℝ) * R < eta)
    (hetaHigh : eta < (51 / 20 : ℝ) * R)
    (hlambda : 0 ≤ lambda)
    (hlambdaUpper : lambda ≤ R / 2) :
    fordGeneralDetectorMajorant A B eta (1 + lambda) t ≤
      fordVKMajorantCoefficient A B * vinogradovKorobovDenominator t := by
  have hR : 0 < R := hRDef.symm ▸ fordVKRadius_pos t
  have hD : 0 < vinogradovKorobovDenominator t :=
    vinogradovKorobovDenominator_pos hbase
  have hDR : vinogradovKorobovDenominator t * R = fordVKLogLog t := by
    rw [mul_comm, hRDef, fordVKRadius_mul_denominator hbase]
  have huOne : 1 ≤ fordVKLogLog t := by linarith
  have hDOne : 1 ≤ vinogradovKorobovDenominator t := by
    have hROne : R ≤ 1 := hRUpper.trans (by norm_num)
    nlinarith
  have huDiv : fordVKLogLog t / R = vinogradovKorobovDenominator t := by
    apply (div_eq_iff hR.ne').mpr
    linarith
  have hInvR : 1 / R ≤ vinogradovKorobovDenominator t := by
    apply (div_le_iff₀ hR).mpr
    nlinarith
  have hetaPos : 0 < eta := by nlinarith
  have hetaUpper : eta ≤ 3 * R := by linarith
  have hlambdaStd : lambda ≤ (6421 / 10000 : ℝ) * R := by
    nlinarith
  have hdPos : 0 < eta - lambda := by nlinarith
  have hdUpper : eta - lambda ≤ 3 * R := by linarith
  have hlogtPos : 0 < Real.log t := by
    exact Real.log_pos ((show (1 : ℝ) < Real.exp (Real.exp 1) by
      exact (Real.one_lt_exp_iff.mpr (Real.exp_pos 1))).trans_le hbase)
  have hpowMono :
      (eta - lambda) ^ (3 / 2 : ℝ) ≤
        (3 * R) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hdPos.le hdUpper (by norm_num)
  have hthreePow : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 9 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by norm_num : (3 / 2 : ℝ) ≤ 2)
    calc
      (3 : ℝ) ^ (3 / 2 : ℝ) ≤ (3 : ℝ) ^ (2 : ℝ) := this
      _ = 9 := by norm_num [Real.rpow_two]
  have hbalanced := fordVKRadius_rpow_three_halves_mul_log hbase
  rw [← hRDef] at hbalanced
  have hthreeR :
      (3 * R) ^ (3 / 2 : ℝ) * Real.log t ≤
        9 * fordVKLogLog t := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hR.le]
    nlinarith [mul_le_mul_of_nonneg_right hthreePow
      (mul_nonneg (Real.rpow_nonneg hR.le (3 / 2 : ℝ)) hlogtPos.le)]
  have hdMain :
      (eta - lambda) ^ (3 / 2 : ℝ) * Real.log t ≤
        9 * fordVKLogLog t :=
    (mul_le_mul_of_nonneg_right hpowMono hlogtPos.le).trans hthreeR
  have hdPower :
      (eta - lambda) ^ (3 / 2 : ℝ) ≤
        9 * fordVKLogLog t := by
    have hlogtOne : 1 ≤ Real.log t := by
      have : Real.exp 1 ≤ Real.log t := by
        simpa using Real.strictMonoOn_log.monotoneOn
          (Real.exp_pos _) (show 0 < t by linarith) hbase
      exact (show (1 : ℝ) ≤ Real.exp 1 by
        exact one_le_two.trans Real.exp_one_gt_two.le).trans this
    nlinarith [Real.rpow_nonneg hdPos.le (3 / 2 : ℝ)]
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hM : 0 ≤ fordSechLogMoment := fordSechLogMoment_nonneg
  let C0 : ℝ := 2 * Real.log A + 18 * B + 4 / 3 +
    (9 * B + 2 / 3) * fordSechLogMoment
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hbracket :
      2 * (Real.log A +
          (B * (eta - lambda) ^ (3 / 2 : ℝ)) * Real.log t +
          (2 / 3 : ℝ) * Real.log (Real.log t)) +
        (B * (eta - lambda) ^ (3 / 2 : ℝ) + 2 / 3) *
          fordSechLogMoment ≤ C0 * fordVKLogLog t := by
    have hUeq : Real.log (Real.log t) = fordVKLogLog t := rfl
    rw [hUeq]
    dsimp [C0]
    have hlogAAbs : Real.log A ≤ Real.log A * fordVKLogLog t := by
      nlinarith
    have hBMain := mul_le_mul_of_nonneg_left hdMain hB
    have hBPower := mul_le_mul_of_nonneg_left hdPower hB
    nlinarith [mul_le_mul_of_nonneg_right hBPower hM]
  have hHigh :
      2 * fordGeneralShiftedLeftHighMajorant A B eta (1 + lambda) t ≤
        (C0 / 5) * vinogradovKorobovDenominator t := by
    unfold fordGeneralShiftedLeftHighMajorant
    unfold fordGeneralAffineGrowthCoefficient
    have hInv : 1 / (2 * eta) ≤ 1 / (5 * R) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hRightNonneg : 0 ≤ C0 * fordVKLogLog t :=
      mul_nonneg hC0 (by linarith)
    calc
      2 * ((1 / (4 * eta)) *
          (2 * (Real.log A +
            (B * (1 - (1 + lambda - eta)) ^ (3 / 2 : ℝ)) * Real.log t +
            (2 / 3 : ℝ) * Real.log (Real.log t)) +
          (B * (1 - (1 + lambda - eta)) ^ (3 / 2 : ℝ) + 2 / 3) *
            fordSechLogMoment)) =
          (1 / (2 * eta)) *
            (2 * (Real.log A +
              (B * (eta - lambda) ^ (3 / 2 : ℝ)) * Real.log t +
              (2 / 3 : ℝ) * Real.log (Real.log t)) +
            (B * (eta - lambda) ^ (3 / 2 : ℝ) + 2 / 3) *
              fordSechLogMoment) := by ring_nf
      _ ≤ (1 / (2 * eta)) *
            (C0 * fordVKLogLog t) :=
        mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ ≤ (1 / (5 * R)) *
            (C0 * fordVKLogLog t) :=
        mul_le_mul_of_nonneg_right hInv hRightNonneg
      _ = (C0 / 5) * vinogradovKorobovDenominator t := by
        rw [← huDiv]
        field_simp [hR.ne']
  have hPole : eta / (Real.pi * t ^ 2) ≤
      vinogradovKorobovDenominator t := by
    have hden : 1 ≤ Real.pi * t ^ 2 := by
      have hpi := Real.pi_gt_three
      nlinarith [sq_nonneg t]
    have hetaOne : eta ≤ 1 := by nlinarith
    have hnonneg : 0 ≤ eta := hetaPos.le
    calc
      eta / (Real.pi * t ^ 2) ≤ eta :=
        (div_le_iff₀ (by positivity)).mpr (by nlinarith)
      _ ≤ 1 := hetaOne
      _ ≤ vinogradovKorobovDenominator t := hDOne
  have hRight :
      Real.log (1 + 1 / (1 + lambda + eta - 1)) / (2 * eta) ≤
        vinogradovKorobovDenominator t := by
    have hden : R ≤ 1 + lambda + eta - 1 := by nlinarith
    have hdenPos : 0 < 1 + lambda + eta - 1 := hR.trans_le hden
    have hinv : 1 / (1 + lambda + eta - 1) ≤ 1 / R :=
      one_div_le_one_div_of_le hR hden
    have hargPos : 0 < 1 + 1 / (1 + lambda + eta - 1) := by positivity
    have hRone : R ≤ 1 := hRUpper.trans (by norm_num)
    have hargBound : 1 + 1 / R ≤ 2 / R := by
      apply (le_div_iff₀ hR).mpr
      field_simp [hR.ne']
      linarith
    have hlogMono : Real.log (1 + 1 / (1 + lambda + eta - 1)) ≤
        Real.log (2 / R) := by
      apply Real.strictMonoOn_log.monotoneOn hargPos
        (div_pos (by norm_num) hR)
      linarith
    have hlogTwo : Real.log 2 ≤ 1 := by
      exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq
        (by norm_num)
    have hlogR := log_fordVKRadius t
    rw [← hRDef] at hlogR
    have hlogBound : Real.log (2 / R) ≤ fordVKLogLog t := by
      rw [Real.log_div (by norm_num) hR.ne', hlogR]
      have hloguNonneg : 0 ≤ Real.log (fordVKLogLog t) :=
        Real.log_nonneg huOne
      nlinarith
    have hnum : Real.log (1 + 1 / (1 + lambda + eta - 1)) ≤
        fordVKLogLog t := hlogMono.trans hlogBound
    have hnumNonneg : 0 ≤
        Real.log (1 + 1 / (1 + lambda + eta - 1)) :=
      Real.log_nonneg (by
        have : 0 ≤ 1 / (1 + lambda + eta - 1) := by positivity
        linarith)
    calc
      Real.log (1 + 1 / (1 + lambda + eta - 1)) / (2 * eta) ≤
          fordVKLogLog t / (2 * eta) :=
        div_le_div_of_nonneg_right hnum (by nlinarith)
      _ ≤ fordVKLogLog t / R := by
        apply div_le_div_of_nonneg_left (by linarith) hR
        nlinarith
      _ = vinogradovKorobovDenominator t := huDiv
  have hLowCompare := fordVK_lowMajorant_le_standard
    (t := t) hR hetaLow hlambdaStd
  have hLowStd := fordShiftedLeftLowMajorant_mul_R_le_one
    ht hR hRUpper hetaLow hetaHigh
  have hLow : fordShiftedLeftLowMajorant eta t (eta - lambda) ≤
      vinogradovKorobovDenominator t := by
    have hstd : fordShiftedLeftLowMajorant eta t
        (eta - (6421 / 10000 : ℝ) * R) ≤ 1 / R := by
      apply (le_div_iff₀ hR).mpr
      simpa [mul_comm] using hLowStd
    exact (hLowCompare.trans hstd).trans hInvR
  unfold fordGeneralDetectorMajorant fordVKMajorantCoefficient
  dsimp [C0] at hHigh
  nlinarith [mul_nonneg
    (by positivity : 0 ≤ (2 * Real.log A + 18 * B + 4 / 3 +
      (9 * B + 2 / 3) * fordSechLogMoment) / 5) hD.le]

#print axioms fordGeneralDetectorMajorant_le_vinogradovKorobovDenominator

end

end GafniTao
