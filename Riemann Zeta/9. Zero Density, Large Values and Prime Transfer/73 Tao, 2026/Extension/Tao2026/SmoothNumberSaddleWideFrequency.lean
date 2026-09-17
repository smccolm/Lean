import Tao2026.SmoothNumberSaddleMainTermGrowth

/-!
# Wide-frequency decay for the smooth-number saddle

This module extends the prime-local characteristic-function contraction from
the central Taylor window to the full principal prime-phase window.  It gives
a uniform Gaussian envelope up to normalized radius
`pi * standardDeviation / log y` and proves, by dominated convergence, that
the annulus between this radius and the expanding central saddle window has
vanishing total Fourier contribution in every critical smooth regime.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

theorem one_div_one_add_le_exp_neg_div_96
    {x : ℝ} (hx0 : 0 ≤ x) (hx48 : x ≤ 48) :
    1 / (1 + x) ≤ Real.exp (-x / 96) := by
  have hscaled0 : 0 ≤ x / 48 := by positivity
  have hscaled1 : x / 48 ≤ 1 := by linarith
  calc
    1 / (1 + x) ≤ 1 / (1 + x / 48) := by
      apply one_div_le_one_div_of_le
      all_goals nlinarith
    _ ≤ Real.exp (-(x / 48) / 2) :=
      one_div_one_add_le_exp_neg_half hscaled0 hscaled1
    _ = Real.exp (-x / 96) := by
      congr 1
      ring

theorem norm_smoothTiltedPrimeCharacteristic_sq_le_wide_exp
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma)
    (t : ℝ) (ht : |t * Real.log (p : ℝ)| ≤ Real.pi) :
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 ≤
      Real.exp (-(1 / (24 * Real.pi ^ 2) *
        (p : ℝ) ^ (-sigma) * (t * Real.log (p : ℝ)) ^ 2 /
          (1 - (p : ℝ) ^ (-sigma)) ^ 2)) := by
  have hsigmaPos : 0 < sigma := by linarith
  let A : ℝ := (1 - (p : ℝ) ^ (-sigma)) ^ 2
  let B : ℝ := 4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
    (t * Real.log (p : ℝ)) ^ 2
  let q : ℝ := B / A
  have haPos : 0 < (p : ℝ) ^ (-sigma) := by positivity
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp)
      (neg_neg_of_pos hsigmaPos)
  have hApos : 0 < A := sq_pos_of_pos (sub_pos.mpr haLt)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hq0 : 0 ≤ q := div_nonneg hB0 hApos.le
  have hpow := four_thirds_le_prime_rpow (show 2 ≤ p by omega) hsigma
  have hpPos : (0 : ℝ) < p := by
    exact_mod_cast (show 0 < p by omega)
  have ha34 : (p : ℝ) ^ (-sigma) ≤ 3 / 4 := by
    rw [Real.rpow_neg hpPos.le]
    rw [inv_le_iff_one_le_mul₀' (Real.rpow_pos_of_pos hpPos sigma)]
    nlinarith
  have hthetaSq : (t * Real.log (p : ℝ)) ^ 2 ≤ Real.pi ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) Real.pi_pos.le).2 ht
  have hB3 : B ≤ 3 := by
    dsimp [B]
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    rw [show 4 / Real.pi ^ 2 * (p : ℝ) ^ (-sigma) *
        (t * Real.log (p : ℝ)) ^ 2 =
      (4 * (p : ℝ) ^ (-sigma) * (t * Real.log (p : ℝ)) ^ 2) /
        Real.pi ^ 2 by ring]
    rw [div_le_iff₀ hpiSq]
    have hprod := mul_le_mul ha34 hthetaSq
      (sq_nonneg (t * Real.log (p : ℝ))) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    nlinarith
  have hA16 : (1 / 16 : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg (1 - (p : ℝ) ^ (-sigma))]
  have hq48 : q ≤ 48 := by
    dsimp [q]
    rw [div_le_iff₀ hApos]
    nlinarith
  have hratio : A / (A + B) = 1 / (1 + q) := by
    dsimp [q]
    field_simp [hApos.ne']
  calc
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 ≤ A / (A + B) := by
      simpa [A, B] using
        norm_smoothTiltedPrimeCharacteristic_sq_le_quadratic
          hp hsigmaPos t ht
    _ = 1 / (1 + q) := hratio
    _ ≤ Real.exp (-q / 96) :=
      one_div_one_add_le_exp_neg_div_96 hq0 hq48
    _ = Real.exp (-(1 / (24 * Real.pi ^ 2) *
        (p : ℝ) ^ (-sigma) * (t * Real.log (p : ℝ)) ^ 2 /
          (1 - (p : ℝ) ^ (-sigma)) ^ 2)) := by
      congr 1
      dsimp [q, B, A]
      field_simp [Real.pi_ne_zero]
      ring

theorem norm_smoothTiltedCharacteristic_sq_le_wide_exp_phiTwo
    (y : ℕ) {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) (t : ℝ)
    (hphase : ∀ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
      |t * Real.log (p : ℝ)| ≤ Real.pi) :
    ‖smoothTiltedCharacteristic y sigma t‖ ^ 2 ≤
      Real.exp (-(1 / (24 * Real.pi ^ 2) * t ^ 2 *
        smoothSaddlePhiTwo y sigma)) := by
  let S := (Finset.Icc 2 y).filter Nat.Prime
  let C : ℝ := 1 / (24 * Real.pi ^ 2) * t ^ 2
  have hsigmaPos : 0 < sigma := by linarith
  have hlocal (p : ℕ) (hp : p ∈ S) :
      ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 ≤
        Real.exp (-(C * smoothSaddleSecondPrimeTerm p sigma)) := by
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have h := norm_smoothTiltedPrimeCharacteristic_sq_le_wide_exp
      hpPrime.one_lt hsigma t (hphase p hp)
    convert h using 1
    congr 2
    rw [← rpow_neg_mul_log_sq_div_one_sub_sq_eq_secondPrimeTerm
      hpPrime.one_lt hsigmaPos]
    dsimp [C]
    ring
  rw [smoothTiltedCharacteristic_eq_sourcePrimeProduct y hsigmaPos t,
    norm_prod, ← Finset.prod_pow]
  calc
    (∏ p ∈ S, ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2) ≤
        ∏ p ∈ S, Real.exp (-(C * smoothSaddleSecondPrimeTerm p sigma)) := by
      exact Finset.prod_le_prod (fun p hp => sq_nonneg _)
        (fun p hp => hlocal p hp)
    _ = Real.exp (∑ p ∈ S,
          -(C * smoothSaddleSecondPrimeTerm p sigma)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(1 / (24 * Real.pi ^ 2) * t ^ 2 *
        smoothSaddlePhiTwo y sigma)) := by
      congr 1
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      rfl

theorem norm_smoothSaddleNormalizedCharacteristic_sq_le_wide_exp
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) (t : ℝ)
    (hphase : ∀ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
      |(t / smoothSaddleStandardDeviation X y) *
        Real.log (p : ℝ)| ≤ Real.pi) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ^ 2 ≤
      Real.exp (-(1 / (24 * Real.pi ^ 2) * t ^ 2)) := by
  have hsdPos := smoothSaddleStandardDeviation_pos hX hy
  have hphiPos := smoothSaddlePhiTwo_pos hy
    (smoothSaddlePoint_pos hX hy)
  have hsdSq : smoothSaddleStandardDeviation X y ^ 2 =
      smoothSaddlePhiTwo y (smoothSaddlePoint X y) := by
    unfold smoothSaddleStandardDeviation
    exact Real.sq_sqrt hphiPos.le
  have h := norm_smoothTiltedCharacteristic_sq_le_wide_exp_phiTwo
    y hsigma (t / smoothSaddleStandardDeviation X y) hphase
  rw [smoothSaddleNormalizedCharacteristic, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  convert h using 1
  congr 2
  rw [div_pow, hsdSq]
  field_simp [hphiPos.ne']

theorem norm_smoothSaddleNormalizedCharacteristic_sq_le_wide_exp_of_range
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) (t : ℝ)
    (hrange : |t| * Real.log (y : ℝ) /
        smoothSaddleStandardDeviation X y ≤ Real.pi) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ^ 2 ≤
      Real.exp (-(1 / (24 * Real.pi ^ 2) * t ^ 2)) := by
  have hsdPos := smoothSaddleStandardDeviation_pos hX hy
  apply norm_smoothSaddleNormalizedCharacteristic_sq_le_wide_exp
    hX hy hsigma t
  intro p hp
  have hpBounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  have hpPos : (0 : ℝ) < p := by
    exact_mod_cast (show 0 < p by omega)
  have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have hlogpy : Real.log (p : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log hpPos (by exact_mod_cast hpBounds.2)
  calc
    |(t / smoothSaddleStandardDeviation X y) * Real.log (p : ℝ)| =
        |t| * Real.log (p : ℝ) /
          smoothSaddleStandardDeviation X y := by
      rw [abs_mul, abs_div, abs_of_pos hsdPos, abs_of_nonneg hlogp0]
      ring
    _ ≤ |t| * Real.log (y : ℝ) /
          smoothSaddleStandardDeviation X y := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogpy (abs_nonneg t)) hsdPos.le
    _ ≤ Real.pi := hrange

theorem norm_smoothSaddleNormalizedCharacteristic_le_wide_exp_of_range
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) (t : ℝ)
    (hrange : |t| * Real.log (y : ℝ) /
        smoothSaddleStandardDeviation X y ≤ Real.pi) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ≤
      Real.exp (-(1 / (48 * Real.pi ^ 2) * t ^ 2)) := by
  have hsq :=
    norm_smoothSaddleNormalizedCharacteristic_sq_le_wide_exp_of_range
      hX hy hsigma t hrange
  have hgaussSq : Real.exp (-(1 / (48 * Real.pi ^ 2) * t ^ 2)) ^ 2 =
      Real.exp (-(1 / (24 * Real.pi ^ 2) * t ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp
  rw [hgaussSq]
  exact hsq

/-- The full normalized-frequency radius on which every prime phase is at
most `pi`. -/
noncomputable def smoothSaddleWideRadius (X y : ℕ) : ℝ :=
  Real.pi * smoothSaddleStandardDeviation X y / Real.log (y : ℝ)

/-- The annulus between the central Gaussian window and the full
prime-phase window. -/
noncomputable def smoothSaddleWideAnnularFourierIntegrand
    (X y : ℕ) (t : ℝ) : ℂ :=
  (Set.Icc (-smoothSaddleWideRadius X y)
      (-smoothSaddleCentralRadius X y) ∪
    Set.Icc (smoothSaddleCentralRadius X y)
      (smoothSaddleWideRadius X y)).indicator
    (fun u => smoothSaddleNormalizedCharacteristic X y u *
      smoothSaddleLaplaceFourierKernel X y u) t

theorem smoothSaddleWideRadius_pos
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    0 < smoothSaddleWideRadius X y := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold smoothSaddleWideRadius
  positivity [Real.pi_pos]

theorem smoothSaddleWideRadius_mul_log_div_sd
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleWideRadius X y * Real.log (y : ℝ) /
        smoothSaddleStandardDeviation X y = Real.pi := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold smoothSaddleWideRadius
  field_simp [hsd.ne', hlog.ne']

theorem aestronglyMeasurable_smoothSaddleWideAnnularFourierIntegrand
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    AEStronglyMeasurable (smoothSaddleWideAnnularFourierIntegrand X y) := by
  unfold smoothSaddleWideAnnularFourierIntegrand
  apply AEStronglyMeasurable.indicator
  · exact ((continuous_smoothSaddleNormalizedCharacteristic hX hy).mul
      (continuous_smoothSaddleLaplaceFourierKernel X y)).aestronglyMeasurable
  · exact measurableSet_Icc.union measurableSet_Icc

theorem norm_smoothSaddleWideAnnularFourierIntegrand_le_gaussian
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) (t : ℝ) :
    ‖smoothSaddleWideAnnularFourierIntegrand X y t‖ ≤
      Real.exp (-(1 / (48 * Real.pi ^ 2) * t ^ 2)) := by
  unfold smoothSaddleWideAnnularFourierIntegrand
  by_cases ht : t ∈
      Set.Icc (-smoothSaddleWideRadius X y)
          (-smoothSaddleCentralRadius X y) ∪
        Set.Icc (smoothSaddleCentralRadius X y)
          (smoothSaddleWideRadius X y)
  · rw [Set.indicator_of_mem ht, norm_mul]
    have habs : |t| ≤ smoothSaddleWideRadius X y := by
      have hw := smoothSaddleWideRadius_pos hX hy
      have hc := smoothSaddleCentralRadius_pos hX hy
      rcases ht with ht | ht
      · rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      · rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
    have hrange : |t| * Real.log (y : ℝ) /
        smoothSaddleStandardDeviation X y ≤ Real.pi := by
      have hlog : 0 ≤ Real.log (y : ℝ) :=
        (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).le
      have hsd := smoothSaddleStandardDeviation_pos hX hy
      calc
        |t| * Real.log (y : ℝ) /
            smoothSaddleStandardDeviation X y ≤
            smoothSaddleWideRadius X y * Real.log (y : ℝ) /
              smoothSaddleStandardDeviation X y := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right habs hlog) hsd.le
        _ = Real.pi := smoothSaddleWideRadius_mul_log_div_sd hX hy
    calc
      ‖smoothSaddleNormalizedCharacteristic X y t‖ *
          ‖smoothSaddleLaplaceFourierKernel X y t‖ ≤
          Real.exp (-(1 / (48 * Real.pi ^ 2) * t ^ 2)) * 1 :=
        mul_le_mul
          (norm_smoothSaddleNormalizedCharacteristic_le_wide_exp_of_range
            hX hy hsigma t hrange)
          (norm_smoothSaddleLaplaceFourierKernel_le_one X y t)
          (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-(1 / (48 * Real.pi ^ 2) * t ^ 2)) := by ring
  · simp only [Set.indicator, ht, ↓reduceIte, norm_zero]
    exact (Real.exp_pos _).le

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleWideAnnularFourierIntegrand_zero
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddleWideAnnularFourierIntegrand (X n) (y n) t)
      atTop (nhds 0) := by
  have hout : ∀ᶠ n in atTop,
      |t| < smoothSaddleCentralRadius (X n) (y n) :=
    (hregime.tendsto_smoothSaddleCentralRadius_atTop_critical hα).eventually
      (eventually_gt_atTop |t|)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hout] with n hn
  symm
  unfold smoothSaddleWideAnnularFourierIntegrand
  have hnot : t ∉
      Set.Icc (-smoothSaddleWideRadius (X n) (y n))
          (-smoothSaddleCentralRadius (X n) (y n)) ∪
        Set.Icc (smoothSaddleCentralRadius (X n) (y n))
          (smoothSaddleWideRadius (X n) (y n)) := by
    intro ht
    rcases ht with ht | ht <;> linarith [ht.1, ht.2, le_abs_self t,
      neg_le_abs t]
  simp only [Set.indicator, hnot, ↓reduceIte]

theorem IsTaoCriticalSmoothRegime.tendsto_integral_smoothSaddleWideAnnularFourierIntegrand_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => ∫ t : ℝ,
      smoothSaddleWideAnnularFourierIntegrand (X n) (y n) t)
      atTop (nhds 0) := by
  let bound : ℝ → ℝ := fun t =>
    Real.exp (-(1 / (48 * Real.pi ^ 2) * t ^ 2))
  have hboundIntegrable : Integrable bound := by
    have hpos : 0 < (1 / (48 * Real.pi ^ 2) : ℝ) := by
      positivity [Real.pi_pos]
    simpa [bound] using integrable_exp_neg_mul_sq hpos
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable
        (smoothSaddleWideAnnularFourierIntegrand (X n) (y n)) := by
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    exact aestronglyMeasurable_smoothSaddleWideAnnularFourierIntegrand hX hy
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t : ℝ,
      ‖smoothSaddleWideAnnularFourierIntegrand (X n) (y n) t‖ ≤ bound t := by
    have hsigma : ∀ᶠ n in atTop,
        (1 / 2 : ℝ) ≤ smoothSaddlePoint (X n) (y n) :=
      (hregime.tendsto_smoothSaddlePoint_one hα).eventually
        (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα,
      hsigma] with n hX hy hsigma
    exact ae_of_all _ fun t =>
      norm_smoothSaddleWideAnnularFourierIntegrand_le_gaussian
        hX hy hsigma t
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun n =>
      smoothSaddleWideAnnularFourierIntegrand (X n) (y n) t)
      atTop (nhds 0) := ae_of_all _ fun t =>
    hregime.tendsto_smoothSaddleWideAnnularFourierIntegrand_zero hα
  simpa using (tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hboundIntegrable hlim)

end

end Tao2026
