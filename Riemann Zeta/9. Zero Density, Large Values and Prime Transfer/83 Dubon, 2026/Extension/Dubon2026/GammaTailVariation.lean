import Dubon2026.GammaDyadicAmplitude
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Integrable derivative variation of the genuine Gamma amplitude on upper tails -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- At the critical power the actual Gamma amplitude derivative has integrable three-halves decay. -/
theorem abs_deriv_doubleGammaAmplitude_le_rpow {a b c d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ)) (ht : 1 ≤ t) :
    |deriv (doubleGammaAmplitude a b c d) t| ≤
      doubleGammaVariationConstant a b c d * doubleGammaAmplitudeConstant a b c d * t ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hh := (abs_deriv_doubleGammaAmplitude_le ha hb hc hd ht).trans
    (mul_le_mul_of_nonneg_left (doubleGammaAmplitude_le_inv_sqrt ha hb hc hd hp ht)
      (by unfold doubleGammaVariationConstant; positivity))
  convert hh using 1
  rw [show -(3 / 2 : ℝ) = -1 + -(1 / 2 : ℝ) by norm_num,
    Real.rpow_add ht0, Real.rpow_neg_one, Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow]
  ring

/-- The literal integral of the three-halves majorant has an inverse-square-root upper-tail bound. -/
theorem integral_three_halves_le {T u : ℝ} (hT : 0 < T) (hu : T ≤ u) :
    (∫ t in T..u, t ^ (-(3 / 2 : ℝ))) ≤ 2 / Real.sqrt T := by
  have hn : (0 : ℝ) ∉ uIcc T u := by
    rw [uIcc_of_le hu]
    intro h
    exact (not_le_of_gt hT) h.1
  have he := integral_rpow (a := T) (b := u)
    (r := -(3 / 2 : ℝ)) (Or.inr ⟨by norm_num, hn⟩)
  rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num] at he
  rw [he, Real.rpow_neg hT.le, ← Real.sqrt_eq_rpow]
  have hpos := Real.rpow_nonneg (hT.le.trans hu) (-(1 / 2 : ℝ))
  calc
    _ = 2 / Real.sqrt T - 2 * u ^ (-(1 / 2 : ℝ)) := by ring
    _ ≤ _ := by linarith

/-- The genuine amplitude's total derivative variation over any upper-tail interval has the sharp decay. -/
theorem doubleGammaAmplitude_tail_variation_le {a b c d T u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ)) (hT : 1 ≤ T) (hu : T ≤ u) :
    doubleGammaAmplitude a b c d u + (∫ t in T..u, |deriv (doubleGammaAmplitude a b c d) t|) ≤
      doubleGammaAmplitudeConstant a b c d * (1 + 2 * doubleGammaVariationConstant a b c d) / Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  have hn : (0 : ℝ) ∉ uIcc T u := by
    rw [uIcc_of_le hu]
    intro h
    exact (not_le_of_gt hT0) h.1
  have hDC : 0 ≤ doubleGammaVariationConstant a b c d * doubleGammaAmplitudeConstant a b c d := by
    unfold doubleGammaVariationConstant doubleGammaAmplitudeConstant
    positivity
  have hi : (∫ t in T..u, |deriv (doubleGammaAmplitude a b c d) t|) ≤
      2 * doubleGammaVariationConstant a b c d * doubleGammaAmplitudeConstant a b c d / Real.sqrt T := by
    calc
      _ ≤ ∫ t in T..u, doubleGammaVariationConstant a b c d * doubleGammaAmplitudeConstant a b c d *
          t ^ (-(3 / 2 : ℝ)) := intervalIntegral.integral_mono_on hu
        ((continuous_deriv_doubleGammaAmplitude ha hb hc hd).abs.intervalIntegrable _ _)
        ((intervalIntegral.intervalIntegrable_rpow (Or.inr hn)).const_mul _)
        (fun t ht => abs_deriv_doubleGammaAmplitude_le_rpow ha hb hc hd hp (hT.trans ht.1))
      _ = (doubleGammaVariationConstant a b c d * doubleGammaAmplitudeConstant a b c d) *
          (∫ t in T..u, t ^ (-(3 / 2 : ℝ))) := intervalIntegral.integral_const_mul _ _
      _ ≤ (doubleGammaVariationConstant a b c d * doubleGammaAmplitudeConstant a b c d) *
          (2 / Real.sqrt T) := mul_le_mul_of_nonneg_left (integral_three_halves_le hT0 hu) hDC
      _ = _ := by ring
  convert add_le_add (doubleGammaAmplitude_le_on_dyadic ha hb hc hd hp hT hu) hi using 1
  ring

end
end Dubon2026
