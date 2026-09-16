import Tao2026.StationaryFourierSourceBlock

/-!
# Coordinate-axis Fourier modes

This module treats Fourier modes for which exactly one reciprocal coefficient
vanishes.  The pure quadratic axis is unconditional from the existing unequal
prime theorem; the pure linear prime-sum axis is kept separate because the
current Type II theorem assumes a nonzero quadratic coefficient.
-/

open Complex Filter MeasureTheory Set
open scoped Interval ComplexConjugate

namespace Tao2026

noncomputable section

theorem unequalQuadraticIntegralAmplitudeDeriv_nonneg_zero_linear
    {B t : ℝ} (hB : 0 < B) (ht : 2 ≤ t) :
    0 ≤ unequalQuadraticIntegralAmplitudeDeriv 0 B t := by
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog : (1 / 2 : ℝ) ≤ Real.log t :=
    hlogTwo.trans (Real.log_le_log (by norm_num) ht)
  have hbracket :
      0 ≤ (2 * 0 * t + 6 * B) * Real.log t - (0 * t + 2 * B) := by
    nlinarith
  unfold unequalQuadraticIntegralAmplitudeDeriv
  exact div_nonneg (mul_nonneg (sq_nonneg t) hbracket) (sq_nonneg _)

theorem abs_unequalQuadraticIntegralAmplitude_zero_linear_le_dyadic
    {B P t : ℝ} (hB : 0 < B) (hP : 2 ≤ P)
    (hPt : P ≤ t) (htP : t ≤ 2 * P) :
    |unequalQuadraticIntegralAmplitude 0 B t| ≤
      4 * P ^ 3 / (B * Real.log P) := by
  have hPpos : 0 < P := by linarith
  have htpos : 0 < t := hPpos.trans_le hPt
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogMono : Real.log P ≤ Real.log t := Real.log_le_log hPpos hPt
  have htCube : t ^ 3 ≤ 8 * P ^ 3 := by
    calc
      t ^ 3 ≤ (2 * P) ^ 3 := pow_le_pow_left₀ htpos.le htP 3
      _ = 8 * P ^ 3 := by ring
  have hden : 2 * B * Real.log P ≤ 2 * B * Real.log t := by gcongr
  unfold unequalQuadraticIntegralAmplitude
  simp only [zero_mul, zero_add]
  rw [abs_div, abs_pow, abs_of_pos htpos, abs_mul, abs_of_pos (by positivity),
    abs_of_pos hlogt]
  calc
    t ^ 3 / (2 * B * Real.log t) ≤
        8 * P ^ 3 / (2 * B * Real.log P) := by
      exact div_le_div₀ (by positivity) htCube (by positivity) hden
    _ = 4 * P ^ 3 / (B * Real.log P) := by ring

theorem norm_quadraticIntervalIntegral_zero_linear_le_dyadic_of_pos
    {B P a b : ℝ} (hB : 0 < B) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase 0 B 2 t) / Real.log t‖ ≤
      16 * P ^ 3 / (B * Real.log P) := by
  have hlin : ∀ t ∈ Set.Icc a b, 0 * t + 2 * B ≠ 0 := by
    intro t ht
    norm_num [hB.ne']
  have hderiv : ∀ t ∈ Set.Icc a b,
      0 ≤ unequalQuadraticIntegralAmplitudeDeriv 0 B t := by
    intro t ht
    exact unequalQuadraticIntegralAmplitudeDeriv_nonneg_zero_linear
      hB (hP.trans (hPa.trans ht.1))
  have hraw := norm_quadraticIntervalIntegral_le_of_amplitudeDeriv_nonneg
    (A := 0) (B := B) (a := a) (b := b)
    (hP.trans hPa) hab hlin hderiv
  have hampA := abs_unequalQuadraticIntegralAmplitude_zero_linear_le_dyadic
    hB hP hPa (hab.trans hbP)
  have hampB := abs_unequalQuadraticIntegralAmplitude_zero_linear_le_dyadic
    hB hP (hPa.trans hab) hbP
  have hfactor : ‖unequalQuadraticIntegralFactor‖ ≤ 1 := by
    rw [norm_unequalQuadraticIntegralFactor]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase 0 B 2 t) / Real.log t‖ ≤
      2 * ‖unequalQuadraticIntegralFactor‖ *
        (|unequalQuadraticIntegralAmplitude 0 B a| +
          |unequalQuadraticIntegralAmplitude 0 B b|) := hraw
    _ ≤ 2 * 1 *
        (4 * P ^ 3 / (B * Real.log P) +
          4 * P ^ 3 / (B * Real.log P)) := by gcongr
    _ = 16 * P ^ 3 / (B * Real.log P) := by ring

theorem norm_quadraticIntervalIntegral_zero_linear_le_dyadic
    {B P a b : ℝ} (hB : B ≠ 0) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase 0 B 2 t) / Real.log t‖ ≤
      16 * P ^ 3 / (|B| * Real.log P) := by
  by_cases hBpos : 0 < B
  · simpa only [abs_of_pos hBpos] using
      norm_quadraticIntervalIntegral_zero_linear_le_dyadic_of_pos
        hBpos hP hPa hab hbP
  · have hBneg : B < 0 := lt_of_le_of_ne (le_of_not_gt hBpos) hB
    rw [norm_intervalIntegral_quadratic_eq_neg_coefficients 0 B a b]
    have hraw := norm_quadraticIntervalIntegral_zero_linear_le_dyadic_of_pos
      (B := -B) (by linarith) hP hPa hab hbP
    simpa only [neg_zero, abs_of_neg hBneg] using hraw

theorem reciprocalPhaseScale_zero_linear
    {B P : ℝ} :
    reciprocalPhaseScale 0 B 2 (4 * P) = |B| / (16 * P ^ 2) := by
  unfold reciprocalPhaseScale
  norm_num [mul_pow]

theorem norm_quadraticIntervalIntegral_zero_linear_le_sourceScale
    {B P L a b : ℝ} (hB : B ≠ 0) (hP : 2 ≤ P) (hL : 0 < L)
    (hscale : L ≤ reciprocalPhaseScale 0 B 2 (4 * P))
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase 0 B 2 t) / Real.log t‖ ≤
      P / (L * Real.log P) := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hBLower : 16 * P ^ 2 * L ≤ |B| := by
    rw [reciprocalPhaseScale_zero_linear] at hscale
    have hden : 0 < 16 * P ^ 2 := by positivity
    have := (le_div_iff₀ hden).mp hscale
    nlinarith
  have hraw := norm_quadraticIntervalIntegral_zero_linear_le_dyadic
    hB hP hPa hab hbP
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase 0 B 2 t) / Real.log t‖ ≤
      16 * P ^ 3 / (|B| * Real.log P) := hraw
    _ ≤ 16 * P ^ 3 / ((16 * P ^ 2 * L) * Real.log P) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    _ = P / (L * Real.log P) := by
      field_simp

theorem norm_fourierModeIntegral_Ico_le_zero_linear_sourceScale
    {q : ℤ × ℤ} {N M P L a b : ℝ}
    (hlinear : (q.1 : ℝ) * N = 0) (hquadratic : (q.2 : ℝ) * M ≠ 0)
    (hP : 2 ≤ P) (hL : 0 < L)
    (hscale : L ≤ reciprocalPhaseScale
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 (4 * P))
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖fourierModeIntegral (Set.Ico a b) q N M 2‖ ≤
      P / (L * Real.log P) := by
  have hraw := norm_quadraticIntervalIntegral_zero_linear_le_sourceScale
    (B := (q.2 : ℝ) * M) hquadratic hP hL
    (by simpa only [hlinear] using hscale) hPa hab hbP
  unfold fourierModeIntegral
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simpa only [hlinear] using hraw

theorem eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_zero_linear
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M L : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      (q.1 : ℝ) * N = 0 → (q.2 : ℝ) * M ≠ 0 → 0 < L →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤ L →
      L ≤ reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2
        (4 * (P : ℝ)) →
      |(q.1 : ℝ) * N| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      |(q.2 : ℝ) * M| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-S) +
          (P : ℝ) / (L * Real.log P) := by
  have hprime := eventually_norm_primeReciprocalPhaseSum_le_sourceRange_unequal
    hVinogradov hA₀ hε haexp hS
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with P hprimeP hP
  intro a b q N M L hPa hab hbP hlinear hquadratic hL hlogLower
    hlower hNupper hMupper
  have hsum := primeFourierModeSum_Ico_eq_reciprocalPhaseSum
    hP hPa hbP q N M
  have hprimeBound := hprimeP a b ((q.1 : ℝ) * N) ((q.2 : ℝ) * M)
    hPa hab hbP hquadratic (hlogLower.trans hlower) hNupper hMupper
  have hintegralBound := norm_fourierModeIntegral_Ico_le_zero_linear_sourceScale
    (q := q) (N := N) (M := M) (P := (P : ℝ)) (L := L)
    (a := (a : ℝ)) (b := (b : ℝ)) hlinear hquadratic
    (by exact_mod_cast hP) hL hlower (by exact_mod_cast hPa)
    (by exact_mod_cast hab.le) (by exact_mod_cast hbP)
  rw [hsum]
  exact (norm_sub_le _ _).trans (add_le_add hprimeBound hintegralBound)

theorem norm_quadraticIntervalIntegral_zero_quadratic_le_dyadic
    {A P a b : ℝ} (hA : A ≠ 0) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A 0 2 t) / Real.log t‖ ≤
      6 * P ^ 2 / (|A| * Real.log P) := by
  by_cases hApos : 0 < A
  · simpa only [abs_of_pos hApos] using
      norm_unequalQuadraticIntervalIntegral_le_dyadic_of_pos_nonneg
        hApos (by norm_num : (0 : ℝ) ≤ 0) hP hPa hab hbP
  · have hAneg : A < 0 := lt_of_le_of_ne (le_of_not_gt hApos) hA
    simpa only [abs_of_neg hAneg] using
      norm_unequalQuadraticIntervalIntegral_le_dyadic_of_neg_nonpos
        hAneg (by norm_num : (0 : ℝ) ≤ 0) hP hPa hab hbP

theorem reciprocalPhaseScale_zero_quadratic
    {A P : ℝ} :
    reciprocalPhaseScale A 0 2 (4 * P) = |A| / (4 * P) := by
  unfold reciprocalPhaseScale
  norm_num

theorem norm_quadraticIntervalIntegral_zero_quadratic_le_sourceScale
    {A P L a b : ℝ} (hA : A ≠ 0) (hP : 2 ≤ P) (hL : 0 < L)
    (hscale : L ≤ reciprocalPhaseScale A 0 2 (4 * P))
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A 0 2 t) / Real.log t‖ ≤
      2 * P / (L * Real.log P) := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hALower : 4 * P * L ≤ |A| := by
    rw [reciprocalPhaseScale_zero_quadratic] at hscale
    simpa [mul_comm, mul_left_comm] using
      (le_div_iff₀ (by positivity : 0 < 4 * P)).mp hscale
  have hraw := norm_quadraticIntervalIntegral_zero_quadratic_le_dyadic
    hA hP hPa hab hbP
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A 0 2 t) / Real.log t‖ ≤
      6 * P ^ 2 / (|A| * Real.log P) := hraw
    _ ≤ 6 * P ^ 2 / ((4 * P * L) * Real.log P) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    _ = (3 / 2 : ℝ) * P / (L * Real.log P) := by
      field_simp
      ring
    _ ≤ 2 * P / (L * Real.log P) := by
      have hbase : 0 ≤ P / (L * Real.log P) := by positivity
      calc
        (3 / 2 : ℝ) * P / (L * Real.log P) =
            (3 / 2 : ℝ) * (P / (L * Real.log P)) := by ring
        _ ≤ 2 * (P / (L * Real.log P)) := by gcongr; norm_num
        _ = 2 * P / (L * Real.log P) := by ring

theorem norm_fourierModeIntegral_Ico_le_zero_quadratic_sourceScale
    {q : ℤ × ℤ} {N M P L a b : ℝ}
    (hlinear : (q.1 : ℝ) * N ≠ 0) (hquadratic : (q.2 : ℝ) * M = 0)
    (hP : 2 ≤ P) (hL : 0 < L)
    (hscale : L ≤ reciprocalPhaseScale
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 (4 * P))
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖fourierModeIntegral (Set.Ico a b) q N M 2‖ ≤
      2 * P / (L * Real.log P) := by
  have hraw := norm_quadraticIntervalIntegral_zero_quadratic_le_sourceScale
    (A := (q.1 : ℝ) * N) hlinear hP hL
    (by simpa only [hquadratic] using hscale) hPa hab hbP
  unfold fourierModeIntegral
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simpa only [hquadratic] using hraw

end
end Tao2026
