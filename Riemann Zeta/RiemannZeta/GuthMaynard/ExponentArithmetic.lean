import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RiemannZeta.GuthMaynard.ZeroDetector

open Filter Asymptotics

namespace RiemannZeta.GuthMaynard

lemma denom_pos (σ : ℝ) (hσ : 7/10 ≤ σ) : 0 < 6 + 10 * σ := by linarith

noncomputable def alpha (σ : ℝ) : ℝ := 15 * (1 - σ) / ((3 + 5 * σ) * (18/5 - 4 * σ))
noncomputable def final_exponent (σ : ℝ) : ℝ := 15 * (1 - σ) / (3 + 5 * σ)

/-- Complete equation (13.1) scale selection. The lower detector scale gives
the uniform numerical bound on `k`; the final hypothesis is the sharp upper
bound needed in the large-scale `k = 2` branch. -/
theorem k_selection (N T σ : ℝ)
    (hN : 1 < N) (hT : 1 < T)
    (hσLower : 7 / 10 ≤ σ)
    (hScaleLower : T ^ (1 / 100 : ℝ) ≤ N)
    (hScaleUpper : N ^ (2 : ℝ) ≤ T ^ (15 / (6 + 10 * σ))) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ 101 ∧
      T ^ (10 / (6 + 10 * σ)) ≤ N ^ (k : ℝ) ∧
      N ^ (k : ℝ) ≤ T ^ (15 / (6 + 10 * σ)) := by
  let d := 6 + 10 * σ
  have hd : 0 < d := denom_pos σ hσLower
  have hdThirteen : 13 ≤ d := by
    dsimp [d]
    linarith
  have hTpos : 0 < T := by linarith
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hLowerLog : (1 / 100 : ℝ) * Real.log T ≤ Real.log N := by
    have hLog := (Real.log_le_log_iff
      (Real.rpow_pos_of_pos hTpos _) hNpos).2 hScaleLower
    rw [Real.log_rpow hTpos] at hLog
    exact hLog
  by_cases hSmall : N ≤ T ^ (5 / d)
  · have hSmallLog : Real.log N ≤ (5 / d) * Real.log T := by
      have hLog := (Real.log_le_log_iff hNpos
        (Real.rpow_pos_of_pos hTpos _)).2 hSmall
      simpa [Real.log_rpow hTpos] using hLog
    let B := (10 / d) * Real.log T / Real.log N
    have hBNonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    have hBTwo : (2 : ℝ) ≤ B := by
      rw [le_div_iff₀ hlogN]
      calc
        2 * Real.log N ≤ 2 * ((5 / d) * Real.log T) := by gcongr
        _ = (10 / d) * Real.log T := by ring
    have hLogRatio : Real.log T / Real.log N ≤ 100 := by
      rw [div_le_iff₀ hlogN]
      linarith
    have hTenDiv : 0 ≤ 10 / d ∧ 10 / d ≤ 1 := by
      constructor
      · positivity
      · exact (div_le_one hd).2 (by linarith)
    have hBHundred : B ≤ 100 := by
      dsimp [B]
      rw [mul_div_assoc]
      calc
        (10 / d) * (Real.log T / Real.log N)
            ≤ 1 * (Real.log T / Real.log N) := by
              gcongr
              exact hTenDiv.2
        _ ≤ 100 := by simpa using hLogRatio
    let k := ⌈B⌉₊
    have hBLeK : B ≤ (k : ℝ) := Nat.le_ceil B
    have hkLt : (k : ℝ) < B + 1 := Nat.ceil_lt_add_one hBNonneg
    have hkLower : 2 ≤ k := by
      exact_mod_cast hBTwo.trans hBLeK
    have hkUpper : k ≤ 101 := by
      have hkReal : (k : ℝ) < 101 := by linarith
      exact_mod_cast hkReal.le
    have hBmul : B * Real.log N = (10 / d) * Real.log T := by
      dsimp [B]
      field_simp
    have hLowerPower : T ^ (10 / d) ≤ N ^ (k : ℝ) := by
      apply (Real.log_le_log_iff
        (Real.rpow_pos_of_pos hTpos _) (Real.rpow_pos_of_pos hNpos _)).1
      rw [Real.log_rpow hTpos, Real.log_rpow hNpos]
      calc
        (10 / d) * Real.log T = B * Real.log N := hBmul.symm
        _ ≤ (k : ℝ) * Real.log N := by gcongr
    have hUpperLog : (k : ℝ) * Real.log N ≤ (15 / d) * Real.log T := by
      have hkMul : (k : ℝ) * Real.log N <
          (B + 1) * Real.log N := by gcongr
      rw [add_mul, hBmul] at hkMul
      calc
        (k : ℝ) * Real.log N ≤
            (10 / d) * Real.log T + Real.log N := by
              simpa only [one_mul] using hkMul.le
        _ ≤ (10 / d) * Real.log T + (5 / d) * Real.log T := by gcongr
        _ = (15 / d) * Real.log T := by ring
    have hUpperPower : N ^ (k : ℝ) ≤ T ^ (15 / d) := by
      apply (Real.log_le_log_iff
        (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hTpos _)).1
      simpa [Real.log_rpow hNpos, Real.log_rpow hTpos] using hUpperLog
    exact ⟨k, hkLower, hkUpper, hLowerPower, hUpperPower⟩
  · have hLarge : T ^ (5 / d) < N := lt_of_not_ge hSmall
    have hLowerPower : T ^ (10 / d) ≤ N ^ (2 : ℝ) := by
      have hSquare := Real.rpow_lt_rpow (Real.rpow_nonneg (le_of_lt hTpos) _)
        hLarge (by norm_num : (0 : ℝ) < 2)
      have hPowerIdentity : (T ^ (5 / d)) ^ (2 : ℝ) = T ^ (10 / d) := by
        rw [← Real.rpow_mul (le_of_lt hTpos)]
        congr 1
        ring
      rw [hPowerIdentity] at hSquare
      exact hSquare.le
    exact ⟨2, by norm_num, by norm_num, hLowerPower, hScaleUpper⟩

/-- The logarithmic factor in the detector's upper scale is eventually small
enough for the `k = 2` branch of equation (13.1), uniformly throughout the
central Section 13.1 sigma range. -/
theorem eventually_detectorScaleUpper_sq_le (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    ∀ᶠ T : ℝ in atTop,
      detectorScaleUpper T ^ (2 : ℕ) ≤ T ^ (15 / (6 + 10 * σ)) := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 14)
  have hLogEventually : ∀ᶠ T : ℝ in atTop,
      (Real.log T) ^ (4 : ℕ) ≤ T ^ (1 / 14 : ℝ) := by
    filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with T hLog hT
    have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT
    have hTNonneg : 0 ≤ T := le_trans (by norm_num) hT
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLogNonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hTNonneg _)] at hLog
    rw [← Real.rpow_natCast]
    exact hLog
  filter_upwards [hLogEventually, eventually_ge_atTop (1 : ℝ)] with T hLog hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hdPos : 0 < 6 + 10 * σ := denom_pos σ hσLower
  have hdUpper : 6 + 10 * σ ≤ 14 := by linarith
  have hExponent : (15 / 14 : ℝ) ≤ 15 / (6 + 10 * σ) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 14) hdPos]
    nlinarith
  calc
    detectorScaleUpper T ^ (2 : ℕ)
        = T ^ (1 : ℝ) * (Real.log T) ^ (4 : ℕ) := by
          rw [detectorScaleUpper, mul_pow]
          have hTpow : (T ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = T ^ (1 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hTpos)]
            norm_num
          rw [hTpow]
          ring
    _ ≤ T ^ (1 : ℝ) * T ^ (1 / 14 : ℝ) := by gcongr
    _ = T ^ (15 / 14 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      norm_num
    _ ≤ T ^ (15 / (6 + 10 * σ)) :=
      Real.rpow_le_rpow_of_exponent_le hT hExponent

lemma central_denominators_pos (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    0 < 3 + 5 * σ ∧ 0 < 18 / 5 - 4 * σ := by
  constructor <;> linarith

lemma alpha_pos (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    0 < alpha σ := by
  rcases central_denominators_pos σ hσLower hσUpper with ⟨hFirst, hSecond⟩
  unfold alpha
  exact div_pos (mul_pos (by norm_num) (by linarith)) (mul_pos hFirst hSecond)

lemma final_exponent_nonneg (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    0 ≤ final_exponent σ := by
  rcases central_denominators_pos σ hσLower hσUpper with ⟨hDenom, _⟩
  unfold final_exponent
  exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) hDenom.le

/-- The first large-values term uses the upper edge of (13.1). -/
lemma first_term_exponent_identity (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) :
    (15 / (6 + 10 * σ)) * (2 - 2 * σ) = final_exponent σ := by
  have hDenom : 0 < 3 + 5 * σ := by linarith
  unfold final_exponent
  field_simp
  ring

/-- The middle large-values term defines the splitting exponent `alpha`. -/
lemma second_term_exponent_identity (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    alpha σ * (18 / 5 - 4 * σ) = final_exponent σ := by
  rcases central_denominators_pos σ hσLower hσUpper with ⟨hFirst, hSecond⟩
  have hSecondNe : 18 - σ * 5 * 4 ≠ 0 := by linarith
  unfold alpha final_exponent
  field_simp [hFirst.ne', hSecond.ne', hSecondNe]

/-- The third large-values term uses the lower edge of (13.1). -/
lemma third_term_exponent_identity (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) :
    1 + (10 / (6 + 10 * σ)) * (12 / 5 - 4 * σ) =
      final_exponent σ := by
  have hDenom : 0 < 3 + 5 * σ := by linarith
  unfold final_exponent
  field_simp
  ring

/-- Equation (13.2), the exponent comparison in the mean-value branch. -/
lemma mean_value_exponent_le (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    1 + alpha σ * (1 - 2 * σ) ≤ final_exponent σ := by
  rcases central_denominators_pos σ hσLower hσUpper with ⟨hFirst, hSecond⟩
  unfold alpha final_exponent
  rw [le_div_iff₀ hFirst]
  have hRewrite :
      (1 + 15 * (1 - σ) / ((3 + 5 * σ) * (18 / 5 - 4 * σ)) *
          (1 - 2 * σ)) * (3 + 5 * σ) =
        (3 + 5 * σ) + 15 * (1 - σ) * (1 - 2 * σ) /
          (18 / 5 - 4 * σ) := by
    field_simp [hFirst.ne', hSecond.ne']
  rw [hRewrite]
  have hFrac :
      15 * (1 - σ) * (1 - 2 * σ) / (18 / 5 - 4 * σ) ≤
        15 * (1 - σ) - (3 + 5 * σ) := by
    rw [div_le_iff₀ hSecond]
    nlinarith [sq_nonneg (σ - 3 / 4)]
  linarith

/-- F-09, first term. -/
theorem large_values_first_term_le (σ T Q : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5)
    (hT : 1 ≤ T) (hQ : 0 ≤ Q)
    (hUpper : Q ≤ T ^ (15 / (6 + 10 * σ))) :
    Q ^ (2 - 2 * σ) ≤ T ^ final_exponent σ := by
  have hExponent : 0 ≤ 2 - 2 * σ := by linarith
  calc
    Q ^ (2 - 2 * σ) ≤
        (T ^ (15 / (6 + 10 * σ))) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hQ hUpper hExponent
    _ = T ^ ((15 / (6 + 10 * σ)) * (2 - 2 * σ)) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ T)]
    _ = T ^ final_exponent σ := by rw [first_term_exponent_identity σ hσLower]

/-- F-09, middle term in the small-`Q` branch. -/
theorem large_values_second_term_le (σ T Q : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5)
    (hT : 1 ≤ T) (hQ : 0 ≤ Q)
    (hUpper : Q ≤ T ^ alpha σ) :
    Q ^ (18 / 5 - 4 * σ) ≤ T ^ final_exponent σ := by
  have hExponent : 0 ≤ 18 / 5 - 4 * σ :=
    (central_denominators_pos σ hσLower hσUpper).2.le
  calc
    Q ^ (18 / 5 - 4 * σ) ≤ (T ^ alpha σ) ^ (18 / 5 - 4 * σ) :=
      Real.rpow_le_rpow hQ hUpper hExponent
    _ = T ^ (alpha σ * (18 / 5 - 4 * σ)) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ T)]
    _ = T ^ final_exponent σ := by
      rw [second_term_exponent_identity σ hσLower hσUpper]

/-- F-09, height term using the lower edge of equation (13.1). -/
theorem large_values_third_term_le (σ T Q : ℝ)
    (hσLower : 7 / 10 ≤ σ)
    (hT : 1 ≤ T)
    (hLower : T ^ (10 / (6 + 10 * σ)) ≤ Q) :
    T * Q ^ (12 / 5 - 4 * σ) ≤ T ^ final_exponent σ := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hExponent : 12 / 5 - 4 * σ ≤ 0 := by linarith
  have hPower : Q ^ (12 / 5 - 4 * σ) ≤
      (T ^ (10 / (6 + 10 * σ))) ^ (12 / 5 - 4 * σ) :=
    Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hTpos _) hLower hExponent
  calc
    T * Q ^ (12 / 5 - 4 * σ) ≤
        T * (T ^ (10 / (6 + 10 * σ))) ^ (12 / 5 - 4 * σ) := by
      gcongr
    _ = T ^ (1 + (10 / (6 + 10 * σ)) * (12 / 5 - 4 * σ)) := by
      rw [← Real.rpow_mul hTpos.le]
      nth_rewrite 1 [← Real.rpow_one T]
      exact (Real.rpow_add hTpos _ _).symm
    _ = T ^ final_exponent σ := by rw [third_term_exponent_identity σ hσLower]

/-- F-10, the height term in the mean-value branch. -/
theorem mean_value_height_term_le (σ T Q : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5)
    (hT : 1 ≤ T) (hLower : T ^ alpha σ ≤ Q) :
    T * Q ^ (1 - 2 * σ) ≤ T ^ final_exponent σ := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hExponent : 1 - 2 * σ ≤ 0 := by linarith
  have hPower : Q ^ (1 - 2 * σ) ≤ (T ^ alpha σ) ^ (1 - 2 * σ) :=
    Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hTpos _) hLower hExponent
  calc
    T * Q ^ (1 - 2 * σ) ≤ T * (T ^ alpha σ) ^ (1 - 2 * σ) := by gcongr
    _ = T ^ (1 + alpha σ * (1 - 2 * σ)) := by
      rw [← Real.rpow_mul hTpos.le]
      nth_rewrite 1 [← Real.rpow_one T]
      exact (Real.rpow_add hTpos _ _).symm
    _ ≤ T ^ final_exponent σ :=
      Real.rpow_le_rpow_of_exponent_le hT
        (mean_value_exponent_le σ hσLower hσUpper)

/-- All three source large-values terms have the target exponent in the
small-`Q` branch. -/
theorem large_values_terms_le (σ T Q : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5)
    (hT : 1 ≤ T) (hQ : 0 ≤ Q)
    (hEquationLower : T ^ (10 / (6 + 10 * σ)) ≤ Q)
    (hEquationUpper : Q ≤ T ^ (15 / (6 + 10 * σ)))
    (hSmall : Q ≤ T ^ alpha σ) :
    Q ^ (2 - 2 * σ) + Q ^ (18 / 5 - 4 * σ) +
        T * Q ^ (12 / 5 - 4 * σ) ≤
      3 * T ^ final_exponent σ := by
  have hFirst := large_values_first_term_le σ T Q hσLower hσUpper hT hQ hEquationUpper
  have hSecond := large_values_second_term_le σ T Q hσLower hσUpper hT hQ hSmall
  have hThird := large_values_third_term_le σ T Q hσLower hT hEquationLower
  linarith

/-- Both source mean-value terms have the target exponent in the large-`Q`
branch. -/
theorem mean_value_terms_le (σ T Q : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5)
    (hT : 1 ≤ T) (hQ : 0 ≤ Q)
    (hEquationUpper : Q ≤ T ^ (15 / (6 + 10 * σ)))
    (hLarge : T ^ alpha σ ≤ Q) :
    Q ^ (2 - 2 * σ) + T * Q ^ (1 - 2 * σ) ≤
      2 * T ^ final_exponent σ := by
  have hFirst := large_values_first_term_le σ T Q hσLower hσUpper hT hQ hEquationUpper
  have hSecond := mean_value_height_term_le σ T Q hσLower hσUpper hT hLarge
  linarith

/-- The residual Type-II exponent is no larger than the central target. -/
lemma residual_exponent_le_final (σ : ℝ)
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    2 - 2 * σ ≤ final_exponent σ := by
  have hDenom : 0 < 3 + 5 * σ := (central_denominators_pos σ hσLower hσUpper).1
  unfold final_exponent
  rw [le_div_iff₀ hDenom]
  nlinarith [mul_nonneg (sub_nonneg.mpr hσUpper) (by linarith : 0 ≤ 9 / 10 - σ)]

/-- Huxley's high-sigma exponent is no larger than the Guth--Maynard target. -/
lemma huxley_exponent_le_final (σ : ℝ)
    (hσLower : 4 / 5 ≤ σ) (hσUpper : σ ≤ 1) :
    3 * (1 - σ) / (3 * σ - 1) ≤ final_exponent σ := by
  have hHuxleyDenom : 0 < 3 * σ - 1 := by linarith
  have hFinalDenom : 0 < 3 + 5 * σ := by linarith
  unfold final_exponent
  rw [div_le_div_iff₀ hHuxleyDenom hFinalDenom]
  nlinarith [mul_nonneg (sub_nonneg.mpr hσUpper) (sub_nonneg.mpr hσLower)]
