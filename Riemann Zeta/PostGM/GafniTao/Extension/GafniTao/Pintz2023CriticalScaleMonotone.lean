import GafniTao.Pintz2023DetectorArithmetic
import GafniTao.Pintz2023CorollaryThree

/-!
# Monotonicity of Pintz's common critical scale

Pintz splits every coefficient at the single worst-case scale
`N(k,eta,T)`.  A detected zero has the smaller exponent
`xi = eta_j - 1/lambda`; this file proves that its own Corollary-3 scale is
bounded by the common scale.  This is what keeps the split coefficients
independent of the selected ordinate.
-/

namespace GafniTao

noncomputable section

theorem pintz2023CriticalScale_mono_xi
    {r : ℕ} {xi eta epsilon T : ℝ}
    (hr : 0 < r) (hxi : xi ≤ eta) (hT : 1 ≤ T)
    (hdenEta : 0 <
      1 - ((r : ℝ) - 1) * eta - 6 * (r : ℝ) * epsilon) :
    pintz2023CriticalScale r xi epsilon T ≤
      pintz2023CriticalScale r eta epsilon T := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hrMinus : 0 ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  let dXi : ℝ :=
    1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon
  let dEta : ℝ :=
    1 - ((r : ℝ) - 1) * eta - 6 * (r : ℝ) * epsilon
  have hdEta : 0 < dEta := by simpa only [dEta] using hdenEta
  have hdOrder : dEta ≤ dXi := by
    dsimp only [dEta, dXi]
    nlinarith [mul_le_mul_of_nonneg_left hxi hrMinus]
  have hdXi : 0 < dXi := hdEta.trans_le hdOrder
  have hprod : (r : ℝ) * dEta ≤ (r : ℝ) * dXi :=
    mul_le_mul_of_nonneg_left hdOrder hrReal.le
  have hexponent : pintz2023CriticalScaleExponent r xi epsilon ≤
      pintz2023CriticalScaleExponent r eta epsilon := by
    unfold pintz2023CriticalScaleExponent
    exact one_div_le_one_div_of_le (mul_pos hrReal hdEta) hprod
  unfold pintz2023CriticalScale
  exact Real.rpow_le_rpow_of_exponent_le hT hexponent

theorem one_le_pintz2023CriticalScale
    {r : ℕ} {xi epsilon T : ℝ}
    (hr : 0 < r) (hT : 1 ≤ T)
    (hden : 0 <
      1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon) :
    1 ≤ pintz2023CriticalScale r xi epsilon T := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hexp : 0 ≤ pintz2023CriticalScaleExponent r xi epsilon := by
    unfold pintz2023CriticalScaleExponent
    positivity
  unfold pintz2023CriticalScale
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hT hexp

#print axioms pintz2023CriticalScale_mono_xi
#print axioms one_le_pintz2023CriticalScale

end

end GafniTao
