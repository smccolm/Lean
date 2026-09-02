import GafniTao.FordGeneralGrowth
import GafniTao.FordZetaGrowthConsumer

/-!
# Logarithmic consumers of a parameterized Richert--Ford bound

The detector integrates `log |ζ|`.  These lemmas convert the norm estimate
with visible constants into the exact logarithmic and affine-height bounds
used on the left edge.
-/

open Complex

namespace GafniTao

noncomputable section

noncomputable def fordGeneralZetaGrowthMajorant
    (A B sigma t : ℝ) : ℝ :=
  A * |t| ^ (B * (1 - sigma) ^ (3 / 2 : ℝ)) *
    Real.log |t| ^ (2 / 3 : ℝ)

theorem fordGeneralZetaGrowthMajorant_pos
    {A B sigma t : ℝ} (hA : 0 < A) (ht : 3 ≤ |t|) :
    0 < fordGeneralZetaGrowthMajorant A B sigma t := by
  unfold fordGeneralZetaGrowthMajorant
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hlogPos : 0 < Real.log |t| :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) ht)
  positivity

theorem log_fordGeneralZetaGrowthMajorant
    {A B sigma t : ℝ} (hA : 0 < A) (ht : 3 ≤ |t|) :
    Real.log (fordGeneralZetaGrowthMajorant A B sigma t) =
      Real.log A +
        (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log |t| +
        (2 / 3 : ℝ) * Real.log (Real.log |t|) := by
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hlogPos : 0 < Real.log |t| :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) ht)
  unfold fordGeneralZetaGrowthMajorant
  rw [Real.log_mul
      (mul_ne_zero hA.ne'
        (Real.rpow_pos_of_pos htPos _).ne')
      (Real.rpow_pos_of_pos hlogPos _).ne',
    Real.log_mul hA.ne' (Real.rpow_pos_of_pos htPos _).ne',
    Real.log_rpow htPos, Real.log_rpow hlogPos]

theorem log_norm_riemannZeta_le_fordGeneral
    {A B sigma t : ℝ} (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 3 ≤ |t|) :
    Real.log ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      Real.log A +
        (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log |t| +
        (2 / 3 : ℝ) * Real.log (Real.log |t|) := by
  have hAPos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hmajorPos := fordGeneralZetaGrowthMajorant_pos
    (B := B) (sigma := sigma) hAPos ht
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hmajorOne : 1 ≤ fordGeneralZetaGrowthMajorant A B sigma t := by
    unfold fordGeneralZetaGrowthMajorant
    have htOne : 1 ≤ |t| := by linarith
    have hlogOne : 1 ≤ Real.log |t| := by
      have hlogThree : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
        exact Real.exp_one_lt_d9.trans_le (by norm_num)
      exact hlogThree.le.trans
        (Real.strictMonoOn_log.monotoneOn (by norm_num) htPos ht)
    have hpowT :
        1 ≤ |t| ^ (B * (1 - sigma) ^ (3 / 2 : ℝ)) := by
      apply Real.one_le_rpow htOne
      positivity
    have hpowLog : 1 ≤ Real.log |t| ^ (2 / 3 : ℝ) :=
      Real.one_le_rpow hlogOne (by norm_num)
    have hprod :
        1 ≤ |t| ^ (B * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log |t| ^ (2 / 3 : ℝ) := by
      simpa only [one_mul] using
        mul_le_mul hpowT hpowLog (by norm_num) (by positivity)
    calc
      1 ≤ A := hA
      _ = A * 1 := by ring
      _ ≤ A *
          (|t| ^ (B * (1 - sigma) ^ (3 / 2 : ℝ)) *
            Real.log |t| ^ (2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (zero_le_one.trans hA)
      _ = A * |t| ^ (B * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log |t| ^ (2 / 3 : ℝ) := by ring
  rw [← log_fordGeneralZetaGrowthMajorant hAPos ht]
  by_cases hzeta : riemannZeta ((sigma : ℂ) + I * t) = 0
  · simp [hzeta, Real.log_nonneg hmajorOne]
  · exact Real.strictMonoOn_log.monotoneOn
      (norm_pos_iff.mpr hzeta) hmajorPos
      (by simpa [fordGeneralZetaGrowthMajorant] using
        hFord hsigmaLower hsigmaUpper ht)

noncomputable def fordGeneralAffineGrowthCoefficient
    (B sigma : ℝ) : ℝ :=
  B * (1 - sigma) ^ (3 / 2 : ℝ) + 2 / 3

theorem fordGeneralAffineGrowthCoefficient_nonneg
    {B sigma : ℝ} (hB : 0 ≤ B) (hsigma : sigma ≤ 1) :
    0 ≤ fordGeneralAffineGrowthCoefficient B sigma := by
  unfold fordGeneralAffineGrowthCoefficient
  positivity

/-- A sharp separable logarithmic envelope.  Unlike the coarse helper used
for mere integrability, this retains `log log t` and therefore preserves the
`R^(3/2) log t` scale in Ford's local zero count. -/
theorem log_log_abs_affine_height_le_sharp
    {t a u : ℝ} (ht : 3 ≤ t) (ha0 : 0 ≤ a) (haUpper : a ≤ 1 / 2)
    (hheight : 3 ≤ |t + a * u|) :
    Real.log (Real.log |t + a * u|) ≤
      Real.log (Real.log t) + Real.log (|u| + 2) := by
  have htPos : 0 < t := by linarith
  have hlogtOne : 1 ≤ Real.log t := by
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans_le (by norm_num)
    exact hlogThree.le.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num) htPos ht)
  have huPos : 0 < |u| + 2 := by positivity
  have huOne : 1 ≤ |u| + 2 := by linarith [abs_nonneg u]
  have hlogu : Real.log (|u| + 2) ≤ (|u| + 2) - 1 :=
    Real.log_le_sub_one_of_pos huPos
  have hmul :
      Real.log t + Real.log (|u| + 2) ≤
        Real.log t * (|u| + 2) := by
    have hscale : (|u| + 2) - 1 ≤
        Real.log t * ((|u| + 2) - 1) := by
      nlinarith [abs_nonneg u]
    nlinarith
  have hlogHeight := log_abs_affine_height_le ht ha0 haUpper hheight
  have hinner : Real.log |t + a * u| ≤ Real.log t * (|u| + 2) :=
    hlogHeight.trans hmul
  have hinnerPos : 0 < Real.log |t + a * u| :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hheight)
  have htargetPos : 0 < Real.log t * (|u| + 2) :=
    mul_pos (lt_of_lt_of_le (by norm_num) hlogtOne) huPos
  calc
    Real.log (Real.log |t + a * u|) ≤
        Real.log (Real.log t * (|u| + 2)) :=
      Real.strictMonoOn_log.monotoneOn hinnerPos htargetPos hinner
    _ = Real.log (Real.log t) + Real.log (|u| + 2) :=
      Real.log_mul (ne_of_gt (lt_of_lt_of_le (by norm_num) hlogtOne))
        huPos.ne'

theorem log_norm_riemannZeta_affine_le_fordGeneralEnvelope
    {A B sigma t a u : ℝ} (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 3 ≤ t) (ha0 : 0 ≤ a) (haUpper : a ≤ 1 / 2)
    (hheight : 3 ≤ |t + a * u|) :
    Real.log ‖riemannZeta
        ((sigma : ℂ) + I * (t + a * u : ℝ))‖ ≤
      Real.log A +
        (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log t +
        (2 / 3 : ℝ) * Real.log (Real.log t) +
        fordGeneralAffineGrowthCoefficient B sigma *
          Real.log (|u| + 2) := by
  have hraw := log_norm_riemannZeta_le_fordGeneral hFord hA hB
    hsigmaLower hsigmaUpper hheight
  have hlog := log_abs_affine_height_le ht ha0 haUpper hheight
  have hloglog :=
    log_log_abs_affine_height_le_sharp ht ha0 haUpper hheight
  have hcoeff : 0 ≤ B * (1 - sigma) ^ (3 / 2 : ℝ) := by positivity
  calc
    Real.log ‖riemannZeta
        ((sigma : ℂ) + I * (t + a * u : ℝ))‖ ≤
      Real.log A +
        (B * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log |t + a * u| +
        (2 / 3 : ℝ) * Real.log (Real.log |t + a * u|) := hraw
    _ ≤ Real.log A +
        (B * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (Real.log t + Real.log (|u| + 2)) +
        (2 / 3 : ℝ) *
          (Real.log (Real.log t) + Real.log (|u| + 2)) := by
      gcongr
    _ = Real.log A +
        (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log t +
        (2 / 3 : ℝ) * Real.log (Real.log t) +
        fordGeneralAffineGrowthCoefficient B sigma *
          Real.log (|u| + 2) := by
      unfold fordGeneralAffineGrowthCoefficient
      ring

#print axioms log_norm_riemannZeta_le_fordGeneral
#print axioms log_norm_riemannZeta_affine_le_fordGeneralEnvelope

end

end GafniTao
