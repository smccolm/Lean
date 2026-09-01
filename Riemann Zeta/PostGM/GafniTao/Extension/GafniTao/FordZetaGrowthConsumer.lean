import GafniTao.FordSource

/-!
# Pointwise logarithmic form of Ford's zeta-growth theorem

Ford's zero detector consumes `log |zeta|`, whereas the published growth
theorem is stated as a norm bound.  This file performs that conversion with
the literal constants from Ford's Theorem 1.  The zero case is handled
separately because Lean's real logarithm is total at zero.
-/

open Complex

namespace GafniTao

noncomputable section

/-- The literal positive right-hand side in Ford's Theorem 1. -/
noncomputable def fordZetaGrowthMajorant (sigma t : ℝ) : ℝ :=
  76.2 * |t| ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) *
    Real.log |t| ^ (2 / 3 : ℝ)

theorem fordZetaGrowthMajorant_pos
    {sigma t : ℝ} (ht : 3 ≤ |t|) :
    0 < fordZetaGrowthMajorant sigma t := by
  unfold fordZetaGrowthMajorant
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hlogPos : 0 < Real.log |t| :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) ht)
  positivity

/-- Exact logarithmic expansion of Ford's positive majorant. -/
theorem log_fordZetaGrowthMajorant
    {sigma t : ℝ} (ht : 3 ≤ |t|) :
    Real.log (fordZetaGrowthMajorant sigma t) =
      Real.log 76.2 +
        (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log |t| +
        (2 / 3 : ℝ) * Real.log (Real.log |t|) := by
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hlogPos : 0 < Real.log |t| :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) ht)
  unfold fordZetaGrowthMajorant
  rw [Real.log_mul
      (mul_ne_zero (by norm_num : (76.2 : ℝ) ≠ 0)
        (Real.rpow_pos_of_pos htPos _).ne')
      (Real.rpow_pos_of_pos hlogPos _).ne',
    Real.log_mul (by norm_num : (76.2 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos htPos _).ne',
    Real.log_rpow htPos, Real.log_rpow hlogPos]

/-- Ford's norm estimate in the exact source normalization. -/
theorem norm_riemannZeta_le_fordZetaGrowthMajorant
    (hFord : FordZetaGrowthBound)
    {sigma t : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ |t|) :
    ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      fordZetaGrowthMajorant sigma t := by
  simpa [fordZetaGrowthMajorant] using
    hFord hsigmaLower hsigmaUpper ht

/-- The pointwise logarithmic inequality used on Ford's left detector edge.

No nonvanishing assumption is needed: if zeta vanishes, Lean's total real
logarithm gives `log 0 = 0`, while the explicit source majorant is greater
than one in the stated range. -/
theorem log_norm_riemannZeta_le_ford
    (hFord : FordZetaGrowthBound)
    {sigma t : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ |t|) :
    Real.log ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      Real.log 76.2 +
        (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log |t| +
        (2 / 3 : ℝ) * Real.log (Real.log |t|) := by
  have hmajorPos := fordZetaGrowthMajorant_pos (sigma := sigma) ht
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hmajorOne : 1 ≤ fordZetaGrowthMajorant sigma t := by
    unfold fordZetaGrowthMajorant
    have htOne : 1 ≤ |t| := by linarith
    have hlogOne : 1 ≤ Real.log |t| := by
      have hlogThree : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
        exact Real.exp_one_lt_d9.trans_le (by norm_num)
      exact hlogThree.le.trans
        (Real.strictMonoOn_log.monotoneOn (by norm_num) htPos ht)
    have hpowT : 1 ≤ |t| ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) := by
      apply Real.one_le_rpow htOne
      positivity
    have hpowLog : 1 ≤ Real.log |t| ^ (2 / 3 : ℝ) := by
      exact Real.one_le_rpow hlogOne (by norm_num)
    calc
      1 ≤ (76.2 : ℝ) := by norm_num
      _ ≤ 76.2 * |t| ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log |t| ^ (2 / 3 : ℝ) := by
        have hfirst : (1 : ℝ) ≤
            |t| ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) *
              Real.log |t| ^ (2 / 3 : ℝ) :=
          by
            have hmul := mul_le_mul hpowT hpowLog
              (by norm_num : (0 : ℝ) ≤ 1)
              (by positivity : 0 ≤
                |t| ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)))
            simpa using hmul
        nlinarith
  rw [← log_fordZetaGrowthMajorant ht]
  by_cases hzeta : riemannZeta ((sigma : ℂ) + I * t) = 0
  · simp [hzeta, Real.log_nonneg hmajorOne]
  · exact Real.strictMonoOn_log.monotoneOn
      (norm_pos_iff.mpr hzeta) hmajorPos
      (norm_riemannZeta_le_fordZetaGrowthMajorant hFord
        hsigmaLower hsigmaUpper ht)

/-- The physical affine height on Ford's detector is controlled by a
product of the central height and a fixed logarithmic envelope. -/
theorem abs_affine_height_le_mul_abs_add_two
    {t a u : ℝ} (ht : 3 ≤ t) (ha0 : 0 ≤ a) (haUpper : a ≤ 1 / 2) :
    |t + a * u| ≤ t * (|u| + 2) := by
  have htPos : 0 < t := by linarith
  calc
    |t + a * u| ≤ |t| + |a * u| := abs_add_le _ _
    _ = t + a * |u| := by
      rw [abs_of_pos htPos, abs_mul, abs_of_nonneg ha0]
    _ ≤ t * (|u| + 2) := by
      have haLeT : a ≤ t := haUpper.trans (by linarith)
      nlinarith [abs_nonneg u,
        mul_le_mul_of_nonneg_right haLeT (abs_nonneg u)]

theorem log_abs_affine_height_le
    {t a u : ℝ} (ht : 3 ≤ t) (ha0 : 0 ≤ a) (haUpper : a ≤ 1 / 2)
    (hheight : 3 ≤ |t + a * u|) :
    Real.log |t + a * u| ≤ Real.log t + Real.log (|u| + 2) := by
  have htPos : 0 < t := by linarith
  have huPos : 0 < |u| + 2 := by positivity
  calc
    Real.log |t + a * u| ≤ Real.log (t * (|u| + 2)) := by
      exact Real.strictMonoOn_log.monotoneOn
        (lt_of_lt_of_le (by norm_num) hheight)
        (mul_pos htPos huPos)
        (abs_affine_height_le_mul_abs_add_two ht ha0 haUpper)
    _ = Real.log t + Real.log (|u| + 2) :=
      Real.log_mul htPos.ne' huPos.ne'

theorem log_log_abs_affine_height_le
    {t a u : ℝ} (ht : 3 ≤ t) (ha0 : 0 ≤ a) (haUpper : a ≤ 1 / 2)
    (hheight : 3 ≤ |t + a * u|) :
    Real.log (Real.log |t + a * u|) ≤
      Real.log t + Real.log (|u| + 2) := by
  have hlogHeightPos : 0 < Real.log |t + a * u| :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hheight)
  have hself : Real.log (Real.log |t + a * u|) ≤
      Real.log |t + a * u| := by
    have h := Real.log_le_sub_one_of_pos hlogHeightPos
    linarith
  exact hself.trans (log_abs_affine_height_le ht ha0 haUpper hheight)

/-- A separable `sech²`-integrable envelope for the logarithmic Ford bound
along the physical left edge.  This is deliberately a little coarser than
Ford's cancellation-based Lemma 3.3, but it retains the exact Richert
exponent and introduces only an explicit logarithmic-envelope term. -/
theorem log_norm_riemannZeta_affine_le_fordEnvelope
    (hFord : FordZetaGrowthBound)
    {sigma t a u : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : 3 ≤ t)
    (ha0 : 0 ≤ a) (haUpper : a ≤ 1 / 2)
    (hheight : 3 ≤ |t + a * u|) :
    Real.log ‖riemannZeta
        ((sigma : ℂ) + I * (t + a * u : ℝ))‖ ≤
      Real.log 76.2 +
        (4.45 * (1 - sigma) ^ (3 / 2 : ℝ) + 2 / 3) *
          (Real.log t + Real.log (|u| + 2)) := by
  have hraw := log_norm_riemannZeta_le_ford hFord
    hsigmaLower hsigmaUpper hheight
  have hlog := log_abs_affine_height_le ht ha0 haUpper hheight
  have hloglog := log_log_abs_affine_height_le ht ha0 haUpper hheight
  have hcoeff : 0 ≤ 4.45 * (1 - sigma) ^ (3 / 2 : ℝ) := by positivity
  calc
    Real.log ‖riemannZeta
        ((sigma : ℂ) + I * (t + a * u : ℝ))‖ ≤
      Real.log 76.2 +
        (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log |t + a * u| +
        (2 / 3 : ℝ) * Real.log (Real.log |t + a * u|) := hraw
    _ ≤ Real.log 76.2 +
        (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (Real.log t + Real.log (|u| + 2)) +
        (2 / 3 : ℝ) * (Real.log t + Real.log (|u| + 2)) := by
      gcongr
    _ = Real.log 76.2 +
        (4.45 * (1 - sigma) ^ (3 / 2 : ℝ) + 2 / 3) *
          (Real.log t + Real.log (|u| + 2)) := by ring

#print axioms log_norm_riemannZeta_le_ford
#print axioms log_norm_riemannZeta_affine_le_fordEnvelope

end

end GafniTao
