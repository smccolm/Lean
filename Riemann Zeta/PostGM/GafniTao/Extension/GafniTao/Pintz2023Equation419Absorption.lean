import GafniTao.Pintz2023DetectedThreshold
import GafniTao.Pintz2023Equation419Gram
import GafniTao.Pintz2023PoweredHalasz

/-!
# Pintz (2023), equation (4.19): automatic absorption

This file pays the coefficient-energy loss against the two terms of the
completed Gram estimate.  The source detector threshold is used literally;
there is no residual absorption hypothesis in the public theorem.
-/

open Filter

namespace GafniTao

noncomputable section

/-- The exact energy times the exact equation-(4.19) off-diagonal majorant is
eventually at most half the squared detector threshold. -/
theorem eventually_pintz2023_equation419_absorption
    {eta target : ℝ} {k ell h : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell)
    (hh : 0 < h) {Ce Cg : ℝ} (hCg : 0 < Cg) :
    ∀ᶠ T : ℝ in atTop, ∀ N : ℕ,
      1 ≤ T → 0 < N →
      T ^ pintz2023EllThreshold eta data.epsilon ell ≤ (N : ℝ) →
      (N : ℝ) ≤ T ^ (3 : ℝ) →
      let epsilonCoeff := data.epsilon / (100 * (k : ℝ))
      let E := Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
        (N : ℝ) ^ (-4 * eta - 2 / pintz2023SourceLambda T k +
          2 * epsilonCoeff)
      let O := (N : ℝ) ^ (4 * eta) *
        (4 * (N : ℝ) ^ (-2 * data.epsilon) +
          Cg * (4 * eta)⁻¹ *
            ((4 ^ pintz2023NearOneGramExponent
                eta eta data.epsilon + 3) *
              T ^ (-data.epsilon / (k : ℝ))))
      let A :=
        ((1 / (32 * Real.exp 2 *
              Real.log (pintz2023SourceLambda T k)) /
            pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h
      E * O ≤ A ^ 2 / 2 := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hk : 0 < k := lt_of_lt_of_le (by omega) hcell.1
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  let epsilonCoeff : ℝ := data.epsilon / (100 * (k : ℝ))
  let a : ℝ := pintz2023EllThreshold eta data.epsilon ell
  let q : ℝ := data.epsilon / (2 * (k : ℝ) * (ell : ℝ))
  let p : ℝ := 8 * (h : ℝ) + 2
  let Cterm : ℝ := Cg * (4 * eta)⁻¹ *
    (4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3)
  let K : ℝ :=
    Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ * (4 + Cterm)
  have hec : 0 < epsilonCoeff := by
    dsimp only [epsilonCoeff]
    exact div_pos data.epsilon_pos (mul_pos (by norm_num) hkReal)
  have hq : 0 < q := by
    dsimp only [q]
    exact div_pos data.epsilon_pos
      (mul_pos (mul_pos (by norm_num) hkReal) hellReal)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hCterm : 0 ≤ Cterm := by
    dsimp only [Cterm]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg Ce)
        (inv_nonneg.mpr pintz2023HalaszKernelConstant_pos.le))
      (add_nonneg (by norm_num) hCterm)
  have hDenPos : 0 < pintzEllDenominator eta data.epsilon ell :=
    pintzEllDenominator_pos hell data.ell_margin
  have hDenLt : pintzEllDenominator eta data.epsilon ell < (ell : ℝ) := by
    unfold pintzEllDenominator
    have hellThree : (3 : ℝ) ≤ ell := by exact_mod_cast hcell.2.1
    have hellOne : (1 : ℝ) < ell := by
      linarith
    have hetaTerm : 0 < 2 * eta * ((ell : ℝ) - 1) :=
      mul_pos (mul_pos (by norm_num) heta) (sub_pos.mpr hellOne)
    have hepsTerm : 0 < 6 * (ell : ℝ) * data.epsilon :=
      mul_pos (mul_pos (by norm_num) hellReal) data.epsilon_pos
    nlinarith
  have haLower : 1 / (ell : ℝ) < a := by
    dsimp only [a, pintz2023EllThreshold]
    exact one_div_lt_one_div_of_lt hDenPos hDenLt
  have ha : 0 < a := (by positivity : 0 < 1 / (ell : ℝ)).trans haLower
  have hExpOne : a * (2 * epsilonCoeff - 2 * data.epsilon) ≤ -q := by
    have hecShape : epsilonCoeff = data.epsilon / (100 * (k : ℝ)) := rfl
    have hkFour : (4 : ℝ) ≤ k := by exact_mod_cast hcell.1
    have hecBound : epsilonCoeff ≤ data.epsilon / 400 := by
      dsimp only [epsilonCoeff]
      rw [div_le_iff₀ (mul_pos (by norm_num) hkReal)]
      nlinarith [data.epsilon_pos]
    have hnegative : 2 * epsilonCoeff - 2 * data.epsilon < 0 := by
      nlinarith [data.epsilon_pos]
    have hmul := mul_lt_mul_of_neg_right haLower hnegative
    have hAtLower :
        (1 / (ell : ℝ)) * (2 * epsilonCoeff - 2 * data.epsilon) ≤
          -q := by
      dsimp only [epsilonCoeff, q]
      field_simp [hkReal.ne', hellReal.ne']
      nlinarith [data.epsilon_pos, hkFour]
    exact hmul.le.trans hAtLower
  have hExpTwo : 6 * epsilonCoeff - data.epsilon / (k : ℝ) ≤ -q := by
    dsimp only [epsilonCoeff, q]
    have hellThree : (3 : ℝ) ≤ ell := by exact_mod_cast hcell.2.1
    field_simp [hkReal.ne', hellReal.ne']
    nlinarith [data.epsilon_pos, hkReal, hellReal]
  have hThreshold :=
    eventually_pintz2023_detected_threshold_sq_lower
      (hcell.1.trans' (by omega)) hh
  have hSmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := 2 * K) (p := p) (q := q) (b := 1)
    (by positivity) hq (by norm_num)
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal)
  filter_upwards [hThreshold, hSmall, eventually_ge_atTop (Real.exp 1),
    hLambda.eventually (eventually_ge_atTop 1)] with
      T hThresholdT hSmallT hT hLambdaT
  intro N hTone hN hCritical hNUpper
  dsimp only
  have hTPos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlogTPos : 0 < Real.log T := Real.log_pos
    ((show (1 : ℝ) < Real.exp 1 by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)).trans_le hT)
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hLambdaPos : 0 < pintz2023SourceLambda T k :=
    zero_lt_one.trans_le hLambdaT
  have hDropLambda :
      -2 / pintz2023SourceLambda T k + 2 * epsilonCoeff ≤
        2 * epsilonCoeff := by
    have : 0 ≤ 2 / pintz2023SourceLambda T k := by positivity
    have hneg : -(2 / pintz2023SourceLambda T k) ≤ 0 :=
      neg_nonpos.mpr this
    convert add_le_add_right hneg (2 * epsilonCoeff) using 1 <;> ring
  have hOnePower :
      (N : ℝ) ^ (-2 / pintz2023SourceLambda T k +
          2 * epsilonCoeff - 2 * data.epsilon) ≤ T ^ (-q) := by
    have hExponentNeg : 2 * epsilonCoeff - 2 * data.epsilon < 0 := by
      have hkFour : (4 : ℝ) ≤ k := by exact_mod_cast hcell.1
      have hecBound : epsilonCoeff ≤ data.epsilon / 400 := by
        dsimp only [epsilonCoeff]
        rw [div_le_iff₀ (mul_pos (by norm_num) hkReal)]
        nlinarith [data.epsilon_pos]
      nlinarith [data.epsilon_pos]
    calc
      _ ≤ (N : ℝ) ^ (2 * epsilonCoeff - 2 * data.epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hNOne (by linarith)
      _ ≤ (T ^ a) ^ (2 * epsilonCoeff - 2 * data.epsilon) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos hTPos a) hCritical hExponentNeg.le
      _ = T ^ (a * (2 * epsilonCoeff - 2 * data.epsilon)) := by
        rw [← Real.rpow_mul hTPos.le]
      _ ≤ T ^ (-q) :=
        Real.rpow_le_rpow_of_exponent_le hTone hExpOne
  have hTwoPower :
      (N : ℝ) ^ (-2 / pintz2023SourceLambda T k +
          2 * epsilonCoeff) * T ^ (-data.epsilon / (k : ℝ)) ≤
        T ^ (-q) := by
    have hecNonneg : 0 ≤ 2 * epsilonCoeff := by positivity
    calc
      _ ≤ (N : ℝ) ^ (2 * epsilonCoeff) *
          T ^ (-data.epsilon / (k : ℝ)) := by
        gcongr
      _ ≤ (T ^ (3 : ℝ)) ^ (2 * epsilonCoeff) *
          T ^ (-data.epsilon / (k : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) hNUpper hecNonneg)
          (Real.rpow_nonneg hTPos.le _)
      _ = T ^ (6 * epsilonCoeff - data.epsilon / (k : ℝ)) := by
        rw [← Real.rpow_mul hTPos.le, ← Real.rpow_add hTPos]
        congr 1
        ring
      _ ≤ T ^ (-q) :=
        Real.rpow_le_rpow_of_exponent_le hTone hExpTwo
  have hOff :
      (Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
          (N : ℝ) ^ (-4 * eta - 2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff)) *
        ((N : ℝ) ^ (4 * eta) *
          (4 * (N : ℝ) ^ (-2 * data.epsilon) +
            Cg * (4 * eta)⁻¹ *
              ((4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) *
                T ^ (-data.epsilon / (k : ℝ))))) ≤
        K * T ^ (-q) := by
    have hCancel :
        (N : ℝ) ^ (-4 * eta - 2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff) * (N : ℝ) ^ (4 * eta) =
          (N : ℝ) ^ (-2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff) := by
      rw [← Real.rpow_add hNReal]
      congr 1
      ring
    rw [show
      (Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
          (N : ℝ) ^ (-4 * eta - 2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff)) *
        ((N : ℝ) ^ (4 * eta) *
          (4 * (N : ℝ) ^ (-2 * data.epsilon) +
            Cg * (4 * eta)⁻¹ *
              ((4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) *
                T ^ (-data.epsilon / (k : ℝ))))) =
        (Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹) *
          ((N : ℝ) ^ (-4 * eta - 2 / pintz2023SourceLambda T k +
              2 * epsilonCoeff) * (N : ℝ) ^ (4 * eta)) *
          (4 * (N : ℝ) ^ (-2 * data.epsilon) +
            Cg * (4 * eta)⁻¹ *
              ((4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) *
                T ^ (-data.epsilon / (k : ℝ)))) by ring,
      hCancel]
    have hFirst :
        (N : ℝ) ^ (-2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff) *
          (4 * (N : ℝ) ^ (-2 * data.epsilon)) ≤
            4 * T ^ (-q) := by
      rw [show (N : ℝ) ^ (-2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff) *
          (4 * (N : ℝ) ^ (-2 * data.epsilon)) =
        4 * ((N : ℝ) ^ (-2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff) * (N : ℝ) ^ (-2 * data.epsilon)) by ring,
        ← Real.rpow_add hNReal]
      have hScaled := mul_le_mul_of_nonneg_left hOnePower
        (show (0 : ℝ) ≤ 4 by norm_num)
      simpa [sub_eq_add_neg] using hScaled
    have hSecond :
        (N : ℝ) ^ (-2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff) *
          (Cg * (4 * eta)⁻¹ *
            ((4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) *
              T ^ (-data.epsilon / (k : ℝ)))) ≤
            Cterm * T ^ (-q) := by
      change _ ≤ (Cg * (4 * eta)⁻¹ *
        (4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3)) *
          T ^ (-q)
      have hCoeffNonneg : 0 ≤ Cg * (4 * eta)⁻¹ *
          (4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) := by
        positivity
      calc
        _ = (Cg * (4 * eta)⁻¹ *
            (4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3)) *
              ((N : ℝ) ^ (-2 / pintz2023SourceLambda T k +
                2 * epsilonCoeff) *
                T ^ (-data.epsilon / (k : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hTwoPower hCoeffNonneg
    have hBaseNonneg : 0 ≤
        Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ :=
      mul_nonneg (sq_nonneg Ce)
        (inv_nonneg.mpr pintz2023HalaszKernelConstant_pos.le)
    calc
      _ ≤ (Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹) *
          (4 * T ^ (-q) + Cterm * T ^ (-q)) := by
        simpa only [mul_add, mul_assoc] using
          mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond)
            hBaseNonneg
      _ = K * T ^ (-q) := by dsimp only [K]; ring
  have hLogCancel : Real.log T ^ p * Real.log T ^ (-p) = 1 := by
    rw [← Real.rpow_add hlogTPos]
    norm_num
  have hSmall' : K * T ^ (-q) ≤ Real.log T ^ (-p) / 2 := by
    calc
      K * T ^ (-q) =
          (2 * K * Real.log T ^ p * T ^ (-q)) *
            Real.log T ^ (-p) / 2 := by
        field_simp
        rw [mul_assoc, hLogCancel, mul_one]
      _ ≤ 1 * Real.log T ^ (-p) / 2 := by gcongr
      _ = Real.log T ^ (-p) / 2 := by ring
  exact hOff.trans (hSmall'.trans
    (div_le_div_of_nonneg_right hThresholdT (by norm_num)))

#print axioms eventually_pintz2023_equation419_absorption

end

end GafniTao
