import GafniTao.Pintz2023DyadicDepthBound

/-!
# Pintz (2023), the detected powered threshold

The lower bound in equation (4.16) contains two logarithmic denominators and
the selected natural power `h`.  This file proves directly that its square
loses only a fixed power of `log T`.  The literal source expression is kept
in the conclusion.
-/

open Filter

namespace GafniTao

noncomputable section

/-- The exact squared large-value threshold from equation (4.16) eventually
dominates a fixed negative power of `log T`. -/
theorem eventually_pintz2023_detected_threshold_sq_lower
    {k h : ℕ} (hkTwo : 2 ≤ k) (hh : 0 < h) :
    ∀ᶠ T : ℝ in atTop,
      Real.log T ^ (-(8 * (h : ℝ) + 2)) ≤
        (((1 / (32 * Real.exp 2 *
              Real.log (pintz2023SourceLambda T k)) /
            pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h /
          h) ^ 2 := by
  have hk : 0 < k := lt_of_lt_of_le (by omega) hkTwo
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal)
  let B : ℝ := (Real.log 2 + 3) * (Real.log 2)⁻¹ + 2
  let D : ℝ := (Real.log 2)⁻¹ + B
  let M : ℝ := max (64 * Real.exp 2 * D) (h : ℝ)
  have hLogLarge : ∀ᶠ T : ℝ in atTop, M ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop M)
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 4)),
    hLambda.eventually (eventually_ge_atTop (Real.exp 1)),
    hLogLarge] with T hT hLam hLogLargeT
  have hTPos : 0 < T := (Real.exp_pos _).trans_le hT
  have hTOne : 1 ≤ T := by
    have : (1 : ℝ) ≤ Real.exp (Real.exp 4) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (Real.exp_pos 4).le
    exact this.trans hT
  have hlogT : 4 ≤ Real.log T := by
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos (Real.exp 4)) hTPos hT
    rw [Real.log_exp] at hlog
    have hFour : (4 : ℝ) ≤ Real.exp 4 := by
      nlinarith [Real.add_one_le_exp 4]
    exact hFour.trans hlog
  have hlogTPos : 0 < Real.log T := by linarith
  have hLambdaPos : 0 < pintz2023SourceLambda T k :=
    (Real.exp_pos 1).trans_le hLam
  have hlogLambdaPos : 0 < Real.log (pintz2023SourceLambda T k) :=
    Real.log_pos ((show (1 : ℝ) < Real.exp 1 by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)).trans_le hLam)
  have hLambdaLeT : pintz2023SourceLambda T k ≤ T := by
    unfold pintz2023SourceLambda
    have hratio : 2 / (k : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 (by exact_mod_cast hkTwo)
    have hlogLe : Real.log T ≤ T := Real.log_le_sub_one_of_pos hTPos |>.trans (by linarith)
    calc
      2 / (k : ℝ) * Real.log T ≤ Real.log T :=
        mul_le_of_le_one_left hlogTPos.le hratio
      _ ≤ T := hlogLe
  have hlogLambdaLe :
      Real.log (pintz2023SourceLambda T k) ≤ Real.log T :=
    Real.strictMonoOn_log.monotoneOn hLambdaPos hTPos hLambdaLeT
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDepthAffine :=
    pintz2023DyadicDepth_cutoff_cast_le_affine hLambdaPos.le
  have hLambdaLog : pintz2023SourceLambda T k ≤ Real.log T := by
    unfold pintz2023SourceLambda
    have hratio : 2 / (k : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 (by exact_mod_cast hkTwo)
    exact mul_le_of_le_one_left hlogTPos.le hratio
  have hDepth :
      (pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) ≤
        D * Real.log T := by
    calc
      _ ≤ (Real.log 2)⁻¹ * pintz2023SourceLambda T k + B := by
        simpa only [B] using hDepthAffine
      _ ≤ (Real.log 2)⁻¹ * Real.log T + B := by gcongr
      _ ≤ (Real.log 2)⁻¹ * Real.log T + B * Real.log T := by
        have hBmul := mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ Real.log T by linarith) hB.le
        linarith
      _ = D * Real.log T := by dsimp only [D]; ring
  have hConstant : 64 * Real.exp 2 * D ≤ Real.log T := by
    exact (le_max_left _ _).trans hLogLargeT
  have hDenom :
      64 * Real.exp 2 *
          Real.log (pintz2023SourceLambda T k) *
          (pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) ≤
        Real.log T ^ 4 := by
    calc
      _ ≤ 64 * Real.exp 2 * Real.log T * (D * Real.log T) := by
        gcongr
      _ = (64 * Real.exp 2 * D) * Real.log T ^ 2 := by ring
      _ ≤ Real.log T * Real.log T ^ 2 := by gcongr
      _ ≤ Real.log T ^ 4 := by
        have hlogOne : 1 ≤ Real.log T := by linarith
        calc
          Real.log T * Real.log T ^ 2 = Real.log T ^ 3 := by ring
          _ ≤ Real.log T ^ 3 * Real.log T :=
            le_mul_of_one_le_right (by positivity) hlogOne
          _ = Real.log T ^ 4 := by ring
  have hDepthPos : 0 < pintz2023DyadicDepth
      (pintz2023Cutoff (pintz2023SourceLambda T k)) :=
    pintz2023DyadicDepth_pos _
  have hV : Real.log T ^ (-4 : ℝ) ≤
      (1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) /
          pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2 := by
    have hDenomPos : 0 < 64 * Real.exp 2 *
        Real.log (pintz2023SourceLambda T k) *
        (pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) := by
      positivity
    have hlogPowPos : 0 < Real.log T ^ (4 : ℝ) :=
      Real.rpow_pos_of_pos hlogTPos _
    rw [show (1 / (32 * Real.exp 2 *
          Real.log (pintz2023SourceLambda T k)) /
        pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2 =
        (64 * Real.exp 2 * Real.log (pintz2023SourceLambda T k) *
          (pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ))⁻¹ by
      field_simp
      norm_num]
    rw [Real.rpow_neg hlogTPos.le]
    apply (inv_le_inv₀ hlogPowPos hDenomPos).2
    exact hDenom.trans_eq (Real.rpow_natCast (Real.log T) 4).symm
  have hVNonneg : 0 ≤
      (1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) /
          pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2 := by
    positivity
  have hPow := pow_le_pow_left₀
    (Real.rpow_nonneg hlogTPos.le (-4)) hV h
  have hhReal : (0 : ℝ) < h := by exact_mod_cast hh
  have hhLeLog : (h : ℝ) ≤ Real.log T := by
    exact (le_max_right _ _).trans hLogLargeT
  have hdiv : Real.log T ^ (-(4 * (h : ℝ) + 1)) ≤
      ((1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) /
          pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h := by
    have hpowShape : (Real.log T ^ (-4 : ℝ)) ^ h =
        Real.log T ^ (-4 * (h : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlogTPos.le]
    have hinvH : (h : ℝ)⁻¹ ≥ (Real.log T)⁻¹ :=
      (inv_le_inv₀ hlogTPos hhReal).2 hhLeLog
    calc
      Real.log T ^ (-(4 * (h : ℝ) + 1)) =
          Real.log T ^ (-4 * (h : ℝ)) * (Real.log T)⁻¹ := by
        rw [show -(4 * (h : ℝ) + 1) = -4 * (h : ℝ) + (-1) by ring,
          Real.rpow_add hlogTPos, Real.rpow_neg_one]
      _ ≤ Real.log T ^ (-4 * (h : ℝ)) * (h : ℝ)⁻¹ := by
        gcongr
      _ ≤ ((1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) /
          pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h *
            (h : ℝ)⁻¹ := by
        rw [← hpowShape]
        gcongr
      _ = _ := by simp only [div_eq_mul_inv]
  have hsq := sq_le_sq₀
    (Real.rpow_nonneg hlogTPos.le (-(4 * (h : ℝ) + 1)))
    (by positivity : 0 ≤
      ((1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) /
          pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h)
    |>.2 hdiv
  calc
    Real.log T ^ (-(8 * (h : ℝ) + 2)) =
        (Real.log T ^ (-(4 * (h : ℝ) + 1))) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlogTPos.le]
      congr 1
      ring
    _ ≤ _ := hsq

#print axioms eventually_pintz2023_detected_threshold_sq_lower

end

end GafniTao
