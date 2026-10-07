import Dubon2026.DoubleGammaAmplitude

/-! # Actual Gamma amplitudes and total derivative variation on dyadic intervals -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- At the critical horizontal exponent the actual product amplitude is bounded by inverse square root. -/
theorem doubleGammaAmplitude_le_inv_sqrt {a b c d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ)) (ht : 1 ≤ t) :
    doubleGammaAmplitude a b c d t ≤ doubleGammaAmplitudeConstant a b c d / Real.sqrt t := by
  have hh := doubleGammaAmplitude_le ha hb hc hd ht
  rw [hp, Real.rpow_neg (by linarith : 0 ≤ t), ← Real.sqrt_eq_rpow, ← div_eq_mul_inv] at hh
  exact hh

/-- The true amplitude has a uniform inverse-square-root bound throughout a positive dyadic block. -/
theorem doubleGammaAmplitude_le_on_dyadic {a b c d T t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ)) (hT : 1 ≤ T) (ht : T ≤ t) :
    doubleGammaAmplitude a b c d t ≤ doubleGammaAmplitudeConstant a b c d / Real.sqrt T := by
  apply (doubleGammaAmplitude_le_inv_sqrt ha hb hc hd hp (hT.trans ht)).trans
  exact div_le_div_of_nonneg_left (by unfold doubleGammaAmplitudeConstant; positivity)
    (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt ht)

/-- The genuine amplitude derivative is uniformly bounded on each positive dyadic block. -/
theorem abs_deriv_doubleGammaAmplitude_le_on_dyadic {a b c d T t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ)) (hT : 1 ≤ T) (ht : T ≤ t) :
    |deriv (doubleGammaAmplitude a b c d) t| ≤
      doubleGammaVariationConstant a b c d / T * (doubleGammaAmplitudeConstant a b c d / Real.sqrt T) := by
  apply (abs_deriv_doubleGammaAmplitude_le ha hb hc hd (hT.trans ht)).trans
  apply mul_le_mul
    (div_le_div_of_nonneg_left (by unfold doubleGammaVariationConstant; positivity) (by linarith) ht)
    (doubleGammaAmplitude_le_on_dyadic ha hb hc hd hp hT ht)
    (doubleGammaAmplitude_pos ha hb hc hd t).le
  unfold doubleGammaVariationConstant
  positivity

/-- The actual terminal modulus and total derivative variation have the required dyadic decay. -/
theorem doubleGammaAmplitude_variation_le {a b c d T l r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ)) (hT : 1 ≤ T)
    (hl : T ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * T) :
    doubleGammaAmplitude a b c d r + (∫ t in l..r, |deriv (doubleGammaAmplitude a b c d) t|) ≤
      doubleGammaAmplitudeConstant a b c d * (1 + doubleGammaVariationConstant a b c d) / Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  have hi : (∫ t in l..r, |deriv (doubleGammaAmplitude a b c d) t|) ≤
      doubleGammaVariationConstant a b c d * doubleGammaAmplitudeConstant a b c d / Real.sqrt T := by
    calc
      _ ≤ ∫ _ in l..r, doubleGammaVariationConstant a b c d / T *
          (doubleGammaAmplitudeConstant a b c d / Real.sqrt T) :=
        intervalIntegral.integral_mono_on hlr
          ((continuous_deriv_doubleGammaAmplitude ha hb hc hd).abs.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
          (fun t ht => abs_deriv_doubleGammaAmplitude_le_on_dyadic ha hb hc hd hp hT (hl.trans ht.1))
      _ = (r - l) * (doubleGammaVariationConstant a b c d / T *
          (doubleGammaAmplitudeConstant a b c d / Real.sqrt T)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ T * (doubleGammaVariationConstant a b c d / T *
          (doubleGammaAmplitudeConstant a b c d / Real.sqrt T)) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (by unfold doubleGammaVariationConstant doubleGammaAmplitudeConstant; positivity)
      _ = _ := by field_simp
  have he := add_le_add (doubleGammaAmplitude_le_on_dyadic ha hb hc hd hp hT (hl.trans hlr)) hi
  convert he using 1
  ring

end
end Dubon2026
