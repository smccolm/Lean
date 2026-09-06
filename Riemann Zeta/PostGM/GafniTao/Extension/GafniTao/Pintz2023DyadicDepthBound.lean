import GafniTao.Pintz2023SmallMSurvival
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Pintz (2023): logarithmic cost of the first dyadic subdivision

The number of blocks between `X` and the exponential source cutoff is
logarithmic in `T`.  A merely linear bound in the cutoff is too weak for
equation (4.14), so this comparison is kept explicit.
-/

open Filter

namespace GafniTao

noncomputable section

theorem pintz2023Cutoff_cast_le_two_exp
    {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (pintz2023Cutoff lambda : ℝ) ≤ 2 * Real.exp (lambda + 3) := by
  have hExpOne : 1 ≤ Real.exp (lambda + 3) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hCeil : (pintz2023Cutoff lambda : ℝ) <
      Real.exp (lambda + 3) + 1 := by
    unfold pintz2023Cutoff
    exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  linarith

theorem log_pintz2023Cutoff_le
    {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    Real.log (pintz2023Cutoff lambda : ℝ) ≤
      Real.log 2 + lambda + 3 := by
  have hCutoffPos : (0 : ℝ) < pintz2023Cutoff lambda := by
    unfold pintz2023Cutoff
    exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos _)
  have hUpperPos : 0 < 2 * Real.exp (lambda + 3) := by positivity
  have hlog := Real.log_le_log hCutoffPos
    (pintz2023Cutoff_cast_le_two_exp hlambda)
  calc
    Real.log (pintz2023Cutoff lambda : ℝ) ≤
        Real.log (2 * Real.exp (lambda + 3)) := hlog
    _ = Real.log 2 + (lambda + 3) := by
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    _ = Real.log 2 + lambda + 3 := by ring

/-- Real-cast logarithmic upper bound for the exact `Nat.clog` depth. -/
theorem pintz2023DyadicDepth_cutoff_cast_lt
    {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (pintz2023DyadicDepth (pintz2023Cutoff lambda) : ℝ) <
      (Real.log 2 + lambda + 3) / Real.log 2 + 2 := by
  have hCutoffOne : 1 ≤ pintz2023Cutoff lambda := by
    unfold pintz2023Cutoff
    have hpos : 0 < Nat.ceil (Real.exp (lambda + 3)) :=
      Nat.ceil_pos.mpr (Real.exp_pos _)
    omega
  have hlogbNonneg : 0 ≤
      Real.logb 2 (pintz2023Cutoff lambda : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hCutoffOne)
  have hCeil := Nat.ceil_lt_add_one hlogbNonneg
  have hClog :
      Nat.ceil (Real.logb 2 (pintz2023Cutoff lambda : ℝ)) =
        Nat.clog 2 (pintz2023Cutoff lambda) := by
    simpa using Real.natCeil_logb_natCast 2 (pintz2023Cutoff lambda)
  have hLogCutoff := log_pintz2023Cutoff_le hlambda
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogb : Real.logb 2 (pintz2023Cutoff lambda : ℝ) ≤
      (Real.log 2 + lambda + 3) / Real.log 2 := by
    unfold Real.logb
    exact div_le_div_of_nonneg_right hLogCutoff hlogTwo.le
  unfold pintz2023DyadicDepth
  rw [hClog] at hCeil
  calc
    ((Nat.clog 2 (pintz2023Cutoff lambda) + 1 : ℕ) : ℝ) =
        (Nat.clog 2 (pintz2023Cutoff lambda) : ℝ) + 1 := by norm_num
    _ < (Real.logb 2 (pintz2023Cutoff lambda : ℝ) + 1) + 1 :=
      by simpa only [add_comm, add_left_comm, add_assoc] using
        add_lt_add_right hCeil 1
    _ ≤ (Real.log 2 + lambda + 3) / Real.log 2 + 2 := by
      linarith

/-- A simpler affine estimate sufficient for all later little-oh
absorptions. -/
theorem pintz2023DyadicDepth_cutoff_cast_le_affine
    {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (pintz2023DyadicDepth (pintz2023Cutoff lambda) : ℝ) ≤
      (Real.log 2)⁻¹ * lambda +
        ((Real.log 2 + 3) * (Real.log 2)⁻¹ + 2) := by
  have h := (pintz2023DyadicDepth_cutoff_cast_lt hlambda).le
  calc
    (pintz2023DyadicDepth (pintz2023Cutoff lambda) : ℝ) ≤
        (Real.log 2 + lambda + 3) * (Real.log 2)⁻¹ + 2 := by
      simpa only [div_eq_mul_inv] using h
    _ = (Real.log 2)⁻¹ * lambda +
        ((Real.log 2 + 3) * (Real.log 2)⁻¹ + 2) := by ring

/-- The equation-(4.14) power saving is eventually smaller than half of
the first-localization detector threshold.  All logarithmic losses are
shown explicitly. -/
theorem eventually_pintz2023_largeM_error_le_half_localized_threshold
    {epsilon : ℝ} {k : ℕ} (hepsilon : 0 < epsilon) (hkTwo : 2 ≤ k) :
    ∀ᶠ T : ℝ in atTop,
      T ^ (-2 * epsilon / (k : ℝ)) ≤
        (1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) /
          pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2 := by
  have hk : 0 < k := lt_of_lt_of_le (by omega) hkTwo
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  let B : ℝ := (Real.log 2 + 3) * (Real.log 2)⁻¹ + 2
  let D : ℝ := (Real.log 2)⁻¹ + B
  let C : ℝ := 64 * Real.exp 2 * D
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hsmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := C) (p := 2) (q := 2 * epsilon / (k : ℝ)) (b := 1)
    hC (by positivity) (by norm_num)
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal)
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 1),
    hLambda.eventually (eventually_gt_atTop 1)] with T hsmallT hT hLam
  have hTOne : 1 ≤ T := by
    have : (1 : ℝ) ≤ Real.exp 1 := by
      rw [← Real.exp_zero]
      exact (Real.exp_lt_exp.mpr (by norm_num)).le
    exact this.trans hT
  have hlogTOne : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) hT
  have hLambdaNonneg : 0 ≤ pintz2023SourceLambda T k :=
    zero_le_one.trans hLam.le
  have hLambdaLeLog : pintz2023SourceLambda T k ≤ Real.log T := by
    unfold pintz2023SourceLambda
    have hratio : 2 / (k : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 (by exact_mod_cast hkTwo)
    exact mul_le_of_le_one_left (Real.log_nonneg hTOne) hratio
  have hLogLambda :
      Real.log (pintz2023SourceLambda T k) ≤ Real.log T :=
    Real.log_le_log (by linarith)
      (hLambdaLeLog.trans
        ((Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)))
  have hDepth := pintz2023DyadicDepth_cutoff_cast_le_affine hLambdaNonneg
  have hDepthSimple :
      (pintz2023DyadicDepth
        (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) ≤
        D * Real.log T := by
    calc
      (pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) ≤
          (Real.log 2)⁻¹ * pintz2023SourceLambda T k + B := by
        simpa only [B] using hDepth
      _ ≤ (Real.log 2)⁻¹ * Real.log T + B := by gcongr
      _ ≤ (Real.log 2)⁻¹ * Real.log T + B * Real.log T := by
        nlinarith
      _ = D * Real.log T := by dsimp only [D]; ring
  have hLogLambdaNonneg :
      0 ≤ Real.log (pintz2023SourceLambda T k) :=
    Real.log_nonneg hLam.le
  have hDepthNonneg : 0 ≤
      (pintz2023DyadicDepth
        (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) := by positivity
  have hPowerNonneg : 0 ≤ T ^ (-2 * epsilon / (k : ℝ)) := by positivity
  have hProduct :
      (64 * Real.exp 2 * Real.log (pintz2023SourceLambda T k) *
          (pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ)) *
          T ^ (-2 * epsilon / (k : ℝ)) ≤ 1 := by
    calc
      (64 * Real.exp 2 * Real.log (pintz2023SourceLambda T k) *
          (pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ)) *
          T ^ (-2 * epsilon / (k : ℝ)) ≤
        (64 * Real.exp 2 * Real.log T * (D * Real.log T)) *
          T ^ (-2 * epsilon / (k : ℝ)) := by gcongr
      _ = C * Real.log T ^ (2 : ℝ) *
          T ^ (-2 * epsilon / (k : ℝ)) := by
        rw [Real.rpow_two]
        dsimp only [C]
        ring
      _ ≤ 1 := by
        simpa only [neg_div, neg_mul] using hsmallT
  have hDenPos : 0 <
      64 * Real.exp 2 * Real.log (pintz2023SourceLambda T k) *
        (pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) := by
    have hLogPos : 0 < Real.log (pintz2023SourceLambda T k) := by
      exact Real.log_pos hLam
    have hDepthPos : 0 < pintz2023DyadicDepth
        (pintz2023Cutoff (pintz2023SourceLambda T k)) :=
      pintz2023DyadicDepth_pos _
    positivity
  have hOneDiv : T ^ (-2 * epsilon / (k : ℝ)) ≤
      1 / (64 * Real.exp 2 *
        Real.log (pintz2023SourceLambda T k) *
        (pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ)) := by
    apply (le_div_iff₀ hDenPos).2
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hProduct
  calc
    T ^ (-2 * epsilon / (k : ℝ)) ≤ _ := hOneDiv
    _ = (1 / (32 * Real.exp 2 *
          Real.log (pintz2023SourceLambda T k)) /
        pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

#print axioms pintz2023Cutoff_cast_le_two_exp
#print axioms log_pintz2023Cutoff_le
#print axioms pintz2023DyadicDepth_cutoff_cast_lt
#print axioms pintz2023DyadicDepth_cutoff_cast_le_affine
#print axioms eventually_pintz2023_largeM_error_le_half_localized_threshold

end

end GafniTao
