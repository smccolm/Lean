import GafniTao.FordLocalInverseSquare

/-!
# The source-scale `v^{-1/2}` local inverse-square bound

The `B R^{3/2} log t` part of Ford's local count must be integrated before
the radius is bounded uniformly.  Doing otherwise loses the
Vinogradov--Korobov scale.  This file performs that separation and records a
coarse numerical coefficient while preserving the exact powers of `v`.
-/

open Complex Finset MeasureTheory Set

namespace GafniTao

noncomputable section

noncomputable def fordGeneralLocalCountBase
    (A t v : ℝ) : ℝ :=
  1 + Real.log A - Real.log v + Real.log (Real.log t)

theorem fordGeneralLocalCountBase_nonneg
    {A t v : ℝ} (hA : 1 ≤ A) (ht : 100 ≤ t)
    (hv : 0 < v) (hvUpper : v ≤ 1 / 4) :
    0 ≤ fordGeneralLocalCountBase A t v := by
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogv : Real.log v ≤ 0 :=
    Real.log_nonpos hv.le (hvUpper.trans (by norm_num))
  have hloglogt : 0 ≤ Real.log (Real.log t) := by
    apply Real.log_nonneg
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans_le (by norm_num)
    exact hlogThree.le.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < t by linarith) (by linarith))
  unfold fordGeneralLocalCountBase
  linarith

theorem fordGeneralLocalCountScale_le_base_add_main
    {A B t v u : ℝ} (hv : 0 < v) (hu : v ≤ u) :
    fordGeneralLocalCountScale A B t u ≤
      fordGeneralLocalCountBase A t v +
        B * (2 * u) ^ (3 / 2 : ℝ) * Real.log t := by
  have huPos : 0 < u := hv.trans_le hu
  have hlog : Real.log v ≤ Real.log u :=
    Real.strictMonoOn_log.monotoneOn hv huPos hu
  unfold fordGeneralLocalCountScale fordGeneralLocalCountBase
  linarith

theorem two_rpow_three_halves_le_four :
    (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
  calc
    (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 4 := by norm_num

theorem ford_main_inverse_square_kernel_le
    {B t u : ℝ} (hB : 0 ≤ B) (ht : 1 ≤ t) (hu : 0 < u) :
    (2 / u ^ 3) *
        (B * (2 * u) ^ (3 / 2 : ℝ) * Real.log t) ≤
      8 * B * Real.log t * u ^ (-3 / 2 : ℝ) := by
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hsplit : (2 * u) ^ (3 / 2 : ℝ) =
      (2 : ℝ) ^ (3 / 2 : ℝ) * u ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hu.le]
  have hpowu : u ^ (3 : ℕ) = u ^ (3 : ℝ) := by
    exact (Real.rpow_natCast u 3).symm
  have hratio : u ^ (3 / 2 : ℝ) / u ^ 3 =
      u ^ (-3 / 2 : ℝ) := by
    rw [hpowu, ← Real.rpow_sub hu]
    congr 1
    ring
  rw [hsplit]
  have hnonneg : 0 ≤ B * Real.log t * u ^ (-3 / 2 : ℝ) := by
    positivity
  calc
    (2 / u ^ 3) *
        (B * ((2 : ℝ) ^ (3 / 2 : ℝ) *
          u ^ (3 / 2 : ℝ)) * Real.log t) =
      (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) *
        (B * Real.log t * (u ^ (3 / 2 : ℝ) / u ^ 3)) := by ring
    _ = (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) *
        (B * Real.log t * u ^ (-3 / 2 : ℝ)) := by rw [hratio]
    _ ≤ 8 * (B * Real.log t * u ^ (-3 / 2 : ℝ)) := by
      gcongr
      nlinarith [two_rpow_three_halves_le_four]
    _ = 8 * B * Real.log t * u ^ (-3 / 2 : ℝ) := by ring

theorem integral_rpow_neg_three_halves
    {v q : ℝ} (hv : 0 < v) (hvq : v ≤ q) :
    (∫ u : ℝ in v..q, u ^ (-3 / 2 : ℝ)) =
      2 * (v ^ (-1 / 2 : ℝ) - q ^ (-1 / 2 : ℝ)) := by
  rw [integral_rpow]
  · norm_num
    ring
  · right
    constructor
    · norm_num
    · rw [uIcc_of_le hvq]
      intro hzero
      exact (not_lt_of_ge hzero.1) hv

theorem intervalIntegrable_fordSharpLocalInverseMajorant
    {A B t v q : ℝ} (hv : 0 < v) (hvq : v ≤ q) :
    IntervalIntegrable
      (fun u : ℝ => fordGeneralLocalCountConstant *
        ((fordGeneralLocalCountBase A t v) * (2 / u ^ 3) +
          8 * B * Real.log t * u ^ (-3 / 2 : ℝ))) volume v q := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.const_mul
  apply ContinuousOn.add
  · apply ContinuousOn.const_mul
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro u hu
      rw [uIcc_of_le hvq] at hu
      exact pow_ne_zero 3 (ne_of_gt (hv.trans_le hu.1))
  · apply ContinuousOn.mul continuousOn_const
    apply (continuousOn_id.rpow_const)
    intro u hu
    rw [uIcc_of_le hvq] at hu
    exact Or.inl (ne_of_gt (hv.trans_le hu.1))

theorem fordGeneralLocalInverseSquareIntegrand_le_sharp
    {A B t v u : ℝ} (hB : 0 ≤ B) (ht : 100 ≤ t)
    (hv : 0 < v) (hu : v ≤ u) :
    fordGeneralLocalInverseSquareIntegrand A B t u ≤
      fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v * (2 / u ^ 3) +
          8 * B * Real.log t * u ^ (-3 / 2 : ℝ)) := by
  have huPos : 0 < u := hv.trans_le hu
  have hkernel : 0 ≤ 2 / u ^ 3 := by positivity
  have hscale := fordGeneralLocalCountScale_le_base_add_main
    (A := A) (B := B) (t := t) hv hu
  have hmain := ford_main_inverse_square_kernel_le
    hB (show 1 ≤ t by linarith) huPos
  have hC := fordGeneralLocalCountConstant_pos.le
  unfold fordGeneralLocalInverseSquareIntegrand
  calc
    (2 / u ^ 3) * fordGeneralLocalCountConstant *
        fordGeneralLocalCountScale A B t u ≤
      (2 / u ^ 3) * fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v +
          B * (2 * u) ^ (3 / 2 : ℝ) * Real.log t) := by
      exact mul_le_mul_of_nonneg_left hscale
        (mul_nonneg hkernel hC)
    _ = fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v * (2 / u ^ 3) +
          (2 / u ^ 3) *
            (B * (2 * u) ^ (3 / 2 : ℝ) * Real.log t)) := by ring
    _ ≤ fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v * (2 / u ^ 3) +
          8 * B * Real.log t * u ^ (-3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        add_le_add_left hmain
          (fordGeneralLocalCountBase A t v * (2 / u ^ 3))

theorem integral_fordGeneralLocalInverseSquareIntegrand_le_sharp
    {A B t v q : ℝ} (hB : 0 ≤ B)
    (ht : 100 ≤ t) (hv : 0 < v) (hvq : v ≤ q) :
    (∫ u : ℝ in v..q,
      fordGeneralLocalInverseSquareIntegrand A B t u) ≤
      fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v *
            (1 / v ^ 2 - 1 / q ^ 2) +
          16 * B * Real.log t *
            (v ^ (-1 / 2 : ℝ) - q ^ (-1 / 2 : ℝ))) := by
  have hmono := intervalIntegral.integral_mono_on hvq
    (intervalIntegrable_fordGeneralLocalInverseSquareIntegrand
      (A := A) (B := B) (t := t) hv hvq)
    (intervalIntegrable_fordSharpLocalInverseMajorant
      (A := A) (B := B) (t := t) hv hvq)
    (fun u hu => fordGeneralLocalInverseSquareIntegrand_le_sharp
      (A := A) hB ht hv hu.1)
  have hInvInt :
      (∫ u : ℝ in v..q, 2 / u ^ 3) =
        1 / v ^ 2 - 1 / q ^ 2 := by
    linarith [inv_sq_eq_endpoint_add_integral hv hvq]
  have hInvIntegrable : IntervalIntegrable (fun u : ℝ => 2 / u ^ 3)
      volume v q := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro u hu
      rw [uIcc_of_le hvq] at hu
      exact pow_ne_zero 3 (ne_of_gt (hv.trans_le hu.1))
  have hRpowIntegrable :
      IntervalIntegrable (fun u : ℝ => u ^ (-3 / 2 : ℝ)) volume v q := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    intro u hu
    rw [uIcc_of_le hvq] at hu
    exact Or.inl (ne_of_gt (hv.trans_le hu.1))
  have hFirstIntegrable : IntervalIntegrable
      (fun u : ℝ => fordGeneralLocalCountBase A t v * (2 / u ^ 3))
      volume v q := hInvIntegrable.const_mul _
  have hSecondIntegrable : IntervalIntegrable
      (fun u : ℝ => 8 * B * Real.log t * u ^ (-3 / 2 : ℝ))
      volume v q := by
    simpa [mul_assoc] using
      hRpowIntegrable.const_mul (8 * B * Real.log t)
  calc
    (∫ u : ℝ in v..q,
      fordGeneralLocalInverseSquareIntegrand A B t u) ≤
      ∫ u : ℝ in v..q, fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v * (2 / u ^ 3) +
          8 * B * Real.log t * u ^ (-3 / 2 : ℝ)) := hmono
    _ = fordGeneralLocalCountConstant *
        (∫ u : ℝ in v..q,
          (fordGeneralLocalCountBase A t v * (2 / u ^ 3) +
            8 * B * Real.log t * u ^ (-3 / 2 : ℝ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = fordGeneralLocalCountConstant *
        ((∫ u : ℝ in v..q,
            fordGeneralLocalCountBase A t v * (2 / u ^ 3)) +
          (∫ u : ℝ in v..q,
            8 * B * Real.log t * u ^ (-3 / 2 : ℝ))) := by
      rw [intervalIntegral.integral_add hFirstIntegrable hSecondIntegrable]
    _ = fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v *
            (∫ u : ℝ in v..q, 2 / u ^ 3) +
          8 * B * Real.log t *
            (∫ u : ℝ in v..q, u ^ (-3 / 2 : ℝ))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v *
            (1 / v ^ 2 - 1 / q ^ 2) +
          16 * B * Real.log t *
            (v ^ (-1 / 2 : ℝ) - q ^ (-1 / 2 : ℝ))) := by
      rw [hInvInt, integral_rpow_neg_three_halves hv hvq]
      ring

/-- The sharp local inverse-square estimate in the qualitative form needed
by Ford's zero inequality. -/
theorem fordLocalAnnularInverseSquare_le_general_sharp
    {A B t v q : ℝ} (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (ht : 100 ≤ t)
    (hv : 0 < v) (hvq : v ≤ q) (hq : q ≤ 1 / 4) :
    fordLocalAnnularInverseSquare t v q ≤
      fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v / v ^ 2 +
          20 * B * Real.log t * v ^ (-1 / 2 : ℝ)) := by
  have hbase := fordLocalAnnularInverseSquare_le_general_integral
    hFord hA hB ht hv hvq hq
  have hint := integral_fordGeneralLocalInverseSquareIntegrand_le_sharp
    (A := A) hB ht hv hvq
  have hbaseNonneg := fordGeneralLocalCountBase_nonneg
    hA ht hv (hvq.trans hq)
  have hqPos : 0 < q := hv.trans_le hvq
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hqInv : q ^ (-1 / 2 : ℝ) ≤ v ^ (-1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow_of_nonpos hv hvq (by norm_num)
  have hscaleQ : fordGeneralLocalCountScale A B t q =
      fordGeneralLocalCountBase A t v + (Real.log v - Real.log q) +
        B * (2 * q) ^ (3 / 2 : ℝ) * Real.log t := by
    unfold fordGeneralLocalCountScale fordGeneralLocalCountBase
    ring
  have hlogVQ : Real.log v ≤ Real.log q :=
    Real.strictMonoOn_log.monotoneOn hv hqPos hvq
  have hendpointMain :
      B * (2 * q) ^ (3 / 2 : ℝ) * Real.log t / q ^ 2 ≤
        4 * B * Real.log t * q ^ (-1 / 2 : ℝ) := by
    have hsplit : (2 * q) ^ (3 / 2 : ℝ) =
        (2 : ℝ) ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hqPos.le]
    have hqpow : q ^ (3 / 2 : ℝ) / q ^ 2 =
        q ^ (-1 / 2 : ℝ) := by
      rw [show q ^ (2 : ℕ) = q ^ (2 : ℝ) from
          (Real.rpow_natCast q 2).symm,
        ← Real.rpow_sub hqPos]
      congr 1
      ring
    rw [hsplit]
    calc
      B * ((2 : ℝ) ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ)) *
          Real.log t / q ^ 2 =
        (2 : ℝ) ^ (3 / 2 : ℝ) * B * Real.log t *
          (q ^ (3 / 2 : ℝ) / q ^ 2) := by ring
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * B * Real.log t *
          q ^ (-1 / 2 : ℝ) := by rw [hqpow]
      _ ≤ 4 * B * Real.log t * q ^ (-1 / 2 : ℝ) := by
        gcongr
        exact two_rpow_three_halves_le_four
  have hendpoint :
      fordGeneralLocalCountScale A B t q / q ^ 2 ≤
        fordGeneralLocalCountBase A t v / q ^ 2 +
          4 * B * Real.log t * q ^ (-1 / 2 : ℝ) := by
    rw [hscaleQ]
    have hqSq : 0 < q ^ 2 := sq_pos_of_pos hqPos
    have hlogTerm : (Real.log v - Real.log q) / q ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlogVQ) hqSq.le
    calc
      (fordGeneralLocalCountBase A t v + (Real.log v - Real.log q) +
          B * (2 * q) ^ (3 / 2 : ℝ) * Real.log t) / q ^ 2 =
        fordGeneralLocalCountBase A t v / q ^ 2 +
          (Real.log v - Real.log q) / q ^ 2 +
          B * (2 * q) ^ (3 / 2 : ℝ) * Real.log t / q ^ 2 := by ring
      _ ≤ fordGeneralLocalCountBase A t v / q ^ 2 +
          0 + 4 * B * Real.log t * q ^ (-1 / 2 : ℝ) := by
        gcongr
      _ = _ := by ring
  have hC : 0 ≤ fordGeneralLocalCountConstant :=
    fordGeneralLocalCountConstant_pos.le
  have hmainMono :
      4 * B * Real.log t * q ^ (-1 / 2 : ℝ) ≤
        4 * B * Real.log t * v ^ (-1 / 2 : ℝ) := by
    gcongr
  calc
    fordLocalAnnularInverseSquare t v q ≤
      fordGeneralLocalCountConstant *
          fordGeneralLocalCountScale A B t q / q ^ 2 +
        ∫ u : ℝ in v..q,
          fordGeneralLocalInverseSquareIntegrand A B t u := hbase
    _ ≤ fordGeneralLocalCountConstant *
          (fordGeneralLocalCountBase A t v / q ^ 2 +
            4 * B * Real.log t * q ^ (-1 / 2 : ℝ)) +
        fordGeneralLocalCountConstant *
          (fordGeneralLocalCountBase A t v *
              (1 / v ^ 2 - 1 / q ^ 2) +
            16 * B * Real.log t *
              (v ^ (-1 / 2 : ℝ) - q ^ (-1 / 2 : ℝ))) := by
      apply add_le_add
      · rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hendpoint hC
      · exact hint
    _ ≤ fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v / q ^ 2 +
          4 * B * Real.log t * v ^ (-1 / 2 : ℝ) +
          fordGeneralLocalCountBase A t v *
            (1 / v ^ 2 - 1 / q ^ 2) +
          16 * B * Real.log t * v ^ (-1 / 2 : ℝ)) := by
      have hdrop :
          16 * B * Real.log t *
              (v ^ (-1 / 2 : ℝ) - q ^ (-1 / 2 : ℝ)) ≤
            16 * B * Real.log t * v ^ (-1 / 2 : ℝ) := by
        have hnonneg : 0 ≤ 16 * B * Real.log t := by positivity
        nlinarith [Real.rpow_nonneg hqPos.le (-1 / 2 : ℝ)]
      nlinarith [mul_le_mul_of_nonneg_left hmainMono hC,
        mul_le_mul_of_nonneg_left hdrop hC]
    _ = fordGeneralLocalCountConstant *
        (fordGeneralLocalCountBase A t v / v ^ 2 +
          20 * B * Real.log t * v ^ (-1 / 2 : ℝ)) := by ring

#print axioms fordLocalAnnularInverseSquare_le_general_sharp

end

end GafniTao
