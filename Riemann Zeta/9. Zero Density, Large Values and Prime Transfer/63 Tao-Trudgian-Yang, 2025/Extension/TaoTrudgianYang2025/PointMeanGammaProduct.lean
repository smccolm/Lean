import TaoTrudgianYang2025.PointMeanGammaConvolution

/-!
# Actual Gamma-product consumers for the local-mean contour

The numerical convolution estimate is applied to the literal Gamma functions
on either choice of displaced line. Integrability, pole avoidance, and the
single logarithmic loss at displacement `1 / log t` are derived here.
These are contour-kernel estimates, not a pointwise zeta inequality.
-/

noncomputable section

open Complex MeasureTheory

namespace TaoTrudgianYang2025

def pointMeanGammaProduct (a b u w : ℝ) : ℝ :=
  ‖Complex.Gamma ((a : ℂ) + (w : ℂ) * I)‖ *
    ‖Complex.Gamma ((b : ℂ) + ((u - w : ℝ) : ℂ) * I)‖

/-- Neither displaced line meets a Gamma pole, including at zero ordinate. -/
theorem continuous_Gamma_small_shift {a : ℝ} (ha : a ≠ 0)
    (haLower : -1 < a) :
    Continuous (fun w : ℝ => Complex.Gamma ((a : ℂ) + (w : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro w
  apply ContinuousAt.comp (Complex.continuousAt_Gamma _ ?_)
  · fun_prop
  · intro n hn
    have hre := congrArg Complex.re hn
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, neg_re, natCast_re] at hre
    by_cases hn0 : n = 0
    · subst n
      norm_num at hre
      exact ha hre
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      linarith

/-- The actual two-Gamma product is continuous on each pair of displaced lines. -/
theorem continuous_pointMeanGammaProduct {a b : ℝ}
    (ha : a ≠ 0) (haLower : -1 < a)
    (hb : b ≠ 0) (hbLower : -1 < b) (u : ℝ) :
    Continuous (pointMeanGammaProduct a b u) := by
  exact (continuous_Gamma_small_shift ha haLower).norm.mul
    (((continuous_Gamma_small_shift hb hbLower).comp
      (continuous_const.sub continuous_id)).norm)

/-- Both signs of each Gamma displacement are covered with a single constant.
The literal product is integrable and its integral loses only `delta⁻¹`. -/
theorem exists_pointMeanGammaProduct_integral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta a b u : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      (a = delta ∨ a = -delta) → (b = delta ∨ b = -delta) →
      Integrable (pointMeanGammaProduct a b u) ∧
      (∫ w : ℝ, pointMeanGammaProduct a b u w) ≤
        (C / delta) * Real.exp (-|u|) := by
  obtain ⟨B, hB, hKernel⟩ := exists_heathBrown_Gamma_shift_kernel_strong_bound
  refine ⟨B ^ 2 * Real.pi, by positivity, ?_⟩
  intro delta a b u hd hdUpper ha hb
  have hline {c : ℝ} (hc : c = delta ∨ c = -delta) (v : ℝ) :
      ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ ≤
        B * (Real.exp (-(4 / 3 : ℝ) * |v|) / (delta + |v|)) := by
    have h := hKernel delta v hd hdUpper
    have hprod : (delta + |v|) * ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ ≤
        B * Real.exp (-(4 / 3 : ℝ) * |v|) := by
      rcases hc with rfl | rfl
      · exact h.1
      · exact h.2
    have hdiv : ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ ≤
        (B * Real.exp (-(4 / 3 : ℝ) * |v|)) / (delta + |v|) :=
      (le_div_iff₀ (by positivity : 0 < delta + |v|)).2
      (by simpa only [mul_comm] using hprod)
    simpa only [mul_div_assoc] using hdiv
  have hab {c : ℝ} (hc : c = delta ∨ c = -delta) : c ≠ 0 ∧ -1 < c := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  have hmajor (w : ℝ) : pointMeanGammaProduct a b u w ≤
      B ^ 2 * heathBrownStrongGammaConvolutionIntegrand delta u w := by
    have h := mul_le_mul (hline ha w) (hline hb (u - w))
      (norm_nonneg _) (by positivity)
    unfold pointMeanGammaProduct heathBrownStrongGammaConvolutionIntegrand
    convert h using 1; ring
  have hintMajor := (integrable_heathBrownStrongGammaConvolutionIntegrand
    (u := u) hd).const_mul (B ^ 2)
  have hint : Integrable (pointMeanGammaProduct a b u) := by
    apply hintMajor.mono'
      (continuous_pointMeanGammaProduct (hab ha).1 (hab ha).2
        (hab hb).1 (hab hb).2 u).aestronglyMeasurable
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold pointMeanGammaProduct; positivity)]
    exact hmajor w
  refine ⟨hint, ?_⟩
  calc
    (∫ w : ℝ, pointMeanGammaProduct a b u w) ≤
        ∫ w : ℝ, B ^ 2 * heathBrownStrongGammaConvolutionIntegrand delta u w :=
      integral_mono hint hintMajor hmajor
    _ = B ^ 2 * ∫ w : ℝ, heathBrownStrongGammaConvolutionIntegrand delta u w :=
      integral_const_mul _ _
    _ ≤ B ^ 2 * ((Real.pi / delta) * Real.exp (-|u|)) :=
      mul_le_mul_of_nonneg_left (integral_heathBrownStrongGammaConvolutionIntegrand_le hd)
        (sq_nonneg B)
    _ = ((B ^ 2 * Real.pi) / delta) * Real.exp (-|u|) := by ring

/-- The displacement is linked to the actual height; no free logarithmic
loss or analytic convolution bound remains as a premise. -/
theorem exists_pointMeanGammaProduct_log_integral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (t a b u : ℝ),
      Real.exp 4 ≤ t →
      (a = 1 / Real.log t ∨ a = -(1 / Real.log t)) →
      (b = 1 / Real.log t ∨ b = -(1 / Real.log t)) →
      Integrable (pointMeanGammaProduct a b u) ∧
      (∫ w : ℝ, pointMeanGammaProduct a b u w) ≤
        C * Real.log t * Real.exp (-|u|) := by
  obtain ⟨C, hC, hbound⟩ := exists_pointMeanGammaProduct_integral_le
  refine ⟨C, hC, ?_⟩
  intro t a b u ht ha hb
  have hlog : 4 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 4) ht
    simpa only [Real.log_exp] using h
  have hd : 0 < 1 / Real.log t := by positivity
  have hdUpper : 1 / Real.log t ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) hlog
  simpa only [one_div, div_inv_eq_mul] using
    hbound (1 / Real.log t) a b u hd hdUpper ha hb

end TaoTrudgianYang2025
