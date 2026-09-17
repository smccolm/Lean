import Tao2026.SmoothNumberSaddleCentralWindow

/-!
# Quantitative lower curvature at the critical smooth saddle

This module strengthens mere divergence of the exact saddle curvature to the
scale needed by the expanding central Fourier window.  The main finite input
is that the second saddle sum decreases with the saddle parameter.  A coarse
comparison point, eight logarithmic Rankin displacements below one, then
gives enough room for a secant lower bound on the curvature.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- Every second-saddle prime summand decreases as the positive saddle
parameter increases. -/
theorem smoothSaddleSecondPrimeTerm_anti
    {p : ℕ} (hp : 2 ≤ p) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    smoothSaddleSecondPrimeTerm p b ≤
      smoothSaddleSecondPrimeTerm p a := by
  have hpPos : (0 : ℝ) < p := by positivity
  have hqaPos : 0 < (p : ℝ) ^ a := Real.rpow_pos_of_pos hpPos _
  have hqbPos : 0 < (p : ℝ) ^ b := Real.rpow_pos_of_pos hpPos _
  have hqaOne : 1 < (p : ℝ) ^ a :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < p by omega)) ha
  have hqbOne : 1 < (p : ℝ) ^ b := hqaOne.trans_le
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ p by omega)) hab)
  have hqab : (p : ℝ) ^ a ≤ (p : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ p by omega)) hab
  unfold smoothSaddleSecondPrimeTerm
  rw [mul_div_assoc, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [div_le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hqbOne))
    (sq_pos_of_pos (sub_pos.mpr hqaOne))]
  nlinarith [mul_nonneg (sub_nonneg.mpr hqab)
    (sub_nonneg.mpr (show (1 : ℝ) ≤ (p : ℝ) ^ a * (p : ℝ) ^ b by
      nlinarith))]

/-- The full second saddle sum is antitone on the positive axis. -/
theorem smoothSaddlePhiTwo_anti
    (y : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    smoothSaddlePhiTwo y b ≤ smoothSaddlePhiTwo y a := by
  unfold smoothSaddlePhiTwo
  exact Finset.sum_le_sum fun p hpMem =>
    smoothSaddleSecondPrimeTerm_anti
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hpMem).1).1 ha hab

/-- The drop of `phiOne` from the exact saddle to `1` is controlled by the
curvature at the saddle times the saddle displacement. -/
theorem smoothSaddlePhiOne_sub_one_le_phiTwo_mul_one_sub
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsaddleOne : smoothSaddlePoint X y < 1) :
    smoothSaddlePhiOne y (smoothSaddlePoint X y) -
        smoothSaddlePhiOne y 1 ≤
      smoothSaddlePhiTwo y (smoothSaddlePoint X y) *
        (1 - smoothSaddlePoint X y) := by
  obtain ⟨xi, hxi, hsecant⟩ := exists_smoothSaddlePhiTwo_secant y
    (smoothSaddlePoint_pos hX hy) hsaddleOne
  rw [hsecant]
  exact mul_le_mul_of_nonneg_right
    (smoothSaddlePhiTwo_anti y (smoothSaddlePoint_pos hX hy) hxi.1.le)
    (sub_nonneg.mpr hsaddleOne.le)

/-- A coarse moving comparison point below one.  Eight logarithmic Rankin
displacements are deliberately more than the sharp saddle asymptotic needs;
this makes the elementary prime-counting lower bound sufficient. -/
noncomputable def smoothSaddleEightLogPoint (X y : ℕ) : ℝ :=
  1 - 8 * Real.log (smoothRankinRatio X y) / Real.log (y : ℝ)

/-- At the eight-log comparison point the endpoint prime power is exactly
`y / u^8`, where `u = log X / log y`. -/
theorem rpow_smoothSaddleEightLogPoint
    {X y : ℕ} (hy : 2 ≤ y) (hu : 0 < smoothRankinRatio X y) :
    (y : ℝ) ^ smoothSaddleEightLogPoint X y =
      (y : ℝ) / smoothRankinRatio X y ^ (8 : ℕ) := by
  have hyPos : (0 : ℝ) < y := by positivity
  have hlogy : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).ne'
  have hexp : Real.exp (8 * Real.log (smoothRankinRatio X y)) =
      smoothRankinRatio X y ^ (8 : ℕ) := by
    calc
      Real.exp (8 * Real.log (smoothRankinRatio X y)) =
          Real.exp (Real.log (smoothRankinRatio X y)) ^ (8 : ℕ) := by
        simpa using
          (Real.exp_nat_mul (Real.log (smoothRankinRatio X y)) 8)
      _ = smoothRankinRatio X y ^ (8 : ℕ) := by
        rw [Real.exp_log hu]
  rw [Real.rpow_def_of_pos hyPos]
  unfold smoothSaddleEightLogPoint
  rw [show
      Real.log (y : ℝ) *
          (1 - 8 * Real.log (smoothRankinRatio X y) / Real.log (y : ℝ)) =
        Real.log (y : ℝ) -
          8 * Real.log (smoothRankinRatio X y) by
    field_simp [hlogy],
    Real.exp_sub, Real.exp_log hyPos, hexp]

/-- The moving comparison point is eventually positive in every critical
smooth regime. -/
theorem IsTaoCriticalSmoothRegime.eventually_smoothSaddleEightLogPoint_pos
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, 0 < smoothSaddleEightLogPoint (X n) (y n) := by
  have hratio : Tendsto (fun n =>
      8 * (Real.log (smoothRankinRatio (X n) (y n)) /
        Real.log (y n : ℝ))) atTop (nhds 0) := by
    simpa using
      (hregime.tendsto_log_rankinRatio_div_log_y_zero hα).const_mul 8
  filter_upwards [hratio.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with n hn
  unfold smoothSaddleEightLogPoint
  rw [show 8 * Real.log (smoothRankinRatio (X n) (y n)) /
      Real.log (y n : ℝ) =
    8 * (Real.log (smoothRankinRatio (X n) (y n)) /
      Real.log (y n : ℝ)) by ring]
  linarith

/-- The eighth power at the coarse comparison point dominates the two
logarithmic factors in the saddle equation. -/
theorem IsTaoCriticalSmoothRegime.eventually_log_y_sq_lt_rankinRatio_pow_seven
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      Real.log (y n : ℝ) ^ 2 <
        ((9 : ℝ) / 10 * Real.log 2) *
          smoothRankinRatio (X n) (y n) ^ (7 : ℕ) := by
  let c : ℝ := (9 : ℝ) / 10 * Real.log 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hdecay :=
    (hregime.tendsto_log_y_div_rankinRatio_sq_zero hα).eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  filter_upwards [hdecay,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_gt_atTop (0 : ℝ)),
    huTop.eventually (eventually_gt_atTop (max 1 (1 / c)))] with n hsmall
      hlogyPos hu
  have huOne : 1 < smoothRankinRatio (X n) (y n) :=
    (le_max_left _ _).trans_lt hu
  have huInv : 1 / c < smoothRankinRatio (X n) (y n) :=
    (le_max_right _ _).trans_lt hu
  have huPos : 0 < smoothRankinRatio (X n) (y n) := by linarith
  have huSqPos : 0 < smoothRankinRatio (X n) (y n) ^ (2 : ℕ) :=
    pow_pos huPos _
  have hlogy : Real.log (y n : ℝ) <
      smoothRankinRatio (X n) (y n) ^ (2 : ℕ) := by
    exact (div_lt_one huSqPos).mp hsmall
  have hlogSq : Real.log (y n : ℝ) ^ 2 <
      smoothRankinRatio (X n) (y n) ^ (4 : ℕ) := by
    nlinarith
  have hcCube : 1 < c * smoothRankinRatio (X n) (y n) ^ (3 : ℕ) := by
    have hcinv : 1 < c * smoothRankinRatio (X n) (y n) := by
      rw [div_lt_iff₀ hc] at huInv
      simpa [mul_comm] using huInv
    have huSqOne : 1 ≤ smoothRankinRatio (X n) (y n) ^ (2 : ℕ) := by
      nlinarith
    calc
      1 < c * smoothRankinRatio (X n) (y n) := hcinv
      _ ≤ (c * smoothRankinRatio (X n) (y n)) *
          smoothRankinRatio (X n) (y n) ^ (2 : ℕ) := by
        exact le_mul_of_one_le_right (by positivity) huSqOne
      _ = c * smoothRankinRatio (X n) (y n) ^ (3 : ℕ) := by ring
  calc
    Real.log (y n : ℝ) ^ 2 <
        smoothRankinRatio (X n) (y n) ^ (4 : ℕ) := hlogSq
    _ = 1 * smoothRankinRatio (X n) (y n) ^ (4 : ℕ) := by ring
    _ < (c * smoothRankinRatio (X n) (y n) ^ (3 : ℕ)) *
        smoothRankinRatio (X n) (y n) ^ (4 : ℕ) :=
      mul_lt_mul_of_pos_right hcCube (pow_pos huPos _)
    _ = ((9 : ℝ) / 10 * Real.log 2) *
        smoothRankinRatio (X n) (y n) ^ (7 : ℕ) := by
      dsimp [c]
      ring

/-- At the eight-log comparison point, the first saddle sum is eventually
strictly larger than its target value `log X`. -/
theorem IsTaoCriticalSmoothRegime.eventually_log_X_lt_phiOne_eightLogPoint
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      Real.log (X n : ℝ) <
        smoothSaddlePhiOne (y n)
          (smoothSaddleEightLogPoint (X n) (y n)) := by
  filter_upwards [hregime.eventually_smoothSaddleEightLogPoint_pos hα,
    hregime.eventually_log_y_sq_lt_rankinRatio_pow_seven hα,
    hregime.eventually_primeCounting_lower hα,
    hregime.eventually_two_le_X, hregime.eventually_two_le_y hα,
    (hregime.tendsto_rankinRatio_atTop hα).eventually
      (eventually_gt_atTop (0 : ℝ))] with n hsigma hscale hprime hX hy hu
  have hyPos : (0 : ℝ) < y n := by positivity
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have huPow : 0 < smoothRankinRatio (X n) (y n) ^ (8 : ℕ) :=
    pow_pos hu _
  have hmain :
      smoothRankinRatio (X n) (y n) * Real.log (y n : ℝ) <
        ((9 : ℝ) / 10 * Real.log 2) *
          smoothRankinRatio (X n) (y n) ^ (8 : ℕ) /
            Real.log (y n : ℝ) := by
    rw [lt_div_iff₀ hlogy]
    calc
      smoothRankinRatio (X n) (y n) * Real.log (y n : ℝ) *
          Real.log (y n : ℝ) =
        smoothRankinRatio (X n) (y n) * Real.log (y n : ℝ) ^ 2 := by ring
      _ < smoothRankinRatio (X n) (y n) *
          (((9 : ℝ) / 10 * Real.log 2) *
            smoothRankinRatio (X n) (y n) ^ (7 : ℕ)) :=
        mul_lt_mul_of_pos_left hscale hu
      _ = ((9 : ℝ) / 10 * Real.log 2) *
          smoothRankinRatio (X n) (y n) ^ (8 : ℕ) := by ring
  have hprimeFactor : 0 ≤ Real.log 2 /
      (y n : ℝ) ^ smoothSaddleEightLogPoint (X n) (y n) := by
    positivity
  calc
    Real.log (X n : ℝ) =
        smoothRankinRatio (X n) (y n) * Real.log (y n : ℝ) := by
      symm
      exact smoothRankinRatio_mul_log hy
    _ < ((9 : ℝ) / 10 * Real.log 2) *
          smoothRankinRatio (X n) (y n) ^ (8 : ℕ) /
            Real.log (y n : ℝ) := hmain
    _ = ((9 : ℝ) / 10 * (y n : ℝ) /
          Real.log (y n : ℝ)) *
        (Real.log 2 /
          (y n : ℝ) ^ smoothSaddleEightLogPoint (X n) (y n)) := by
      rw [rpow_smoothSaddleEightLogPoint hy hu]
      field_simp [hyPos.ne', hlogy.ne', huPow.ne']
    _ ≤ (Nat.primeCounting (y n) : ℝ) *
        (Real.log 2 /
          (y n : ℝ) ^ smoothSaddleEightLogPoint (X n) (y n)) :=
      mul_le_mul_of_nonneg_right hprime hprimeFactor
    _ ≤ smoothSaddlePhiOne (y n)
          (smoothSaddleEightLogPoint (X n) (y n)) :=
      primeCounting_mul_log_two_div_rpow_le_smoothSaddlePhiOne hsigma

/-- The exact saddle eventually lies above the coarse eight-log comparison
point. -/
theorem IsTaoCriticalSmoothRegime.eventually_eightLogPoint_lt_smoothSaddlePoint
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      smoothSaddleEightLogPoint (X n) (y n) <
        smoothSaddlePoint (X n) (y n) := by
  filter_upwards [hregime.eventually_log_X_lt_phiOne_eightLogPoint hα,
    hregime.eventually_smoothSaddleEightLogPoint_pos hα,
    hregime.eventually_two_le_X, hregime.eventually_two_le_y hα] with
      n hphi hproxy hX hy
  apply lt_of_not_ge
  intro hsaddleProxy
  have hmono := (smoothSaddlePhiOne_strictAntiOn hy).antitoneOn
    (smoothSaddlePoint_pos hX hy) hproxy hsaddleProxy
  rw [smoothSaddlePhiOne_smoothSaddlePoint hX hy] at hmono
  exact (not_le_of_gt hphi) hmono

/-- Quantitative upper bound for the exact critical saddle displacement. -/
theorem IsTaoCriticalSmoothRegime.eventually_one_sub_saddle_lt_eight_log_ratio
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      1 - smoothSaddlePoint (X n) (y n) <
        8 * Real.log (smoothRankinRatio (X n) (y n)) /
          Real.log (y n : ℝ) := by
  filter_upwards [hregime.eventually_eightLogPoint_lt_smoothSaddlePoint hα]
    with n hn
  unfold smoothSaddleEightLogPoint at hn
  linarith

/-- The value of the first saddle sum at one is eventually at most half of
the target logarithm. -/
theorem IsTaoCriticalSmoothRegime.eventually_two_mul_phiOne_one_le_log_X
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      2 * smoothSaddlePhiOne (y n) 1 ≤ Real.log (X n : ℝ) := by
  have huLarge := (hregime.tendsto_rankinRatio_atTop hα).eventually
    (eventually_ge_atTop (12 * Real.log 4))
  have hlogy := (hregime.tendsto_log_y_atTop hα).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [huLarge, hlogy, hregime.eventually_two_le_y hα] with
      n hu hlogy hy
  have hlogFour : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  calc
    2 * smoothSaddlePhiOne (y n) 1 ≤
        2 * (2 * Real.log 4 * (2 + Real.log (y n : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (smoothSaddlePhiOne_one_le (y n) (by omega)) (by norm_num)
    _ = 4 * Real.log 4 * (2 + Real.log (y n : ℝ)) := by ring
    _ ≤ (12 * Real.log 4) * Real.log (y n : ℝ) := by
      nlinarith [mul_nonneg hlogFour (sub_nonneg.mpr hlogy)]
    _ ≤ smoothRankinRatio (X n) (y n) * Real.log (y n : ℝ) := by
      exact mul_le_mul_of_nonneg_right hu (by linarith)
    _ = Real.log (X n : ℝ) := smoothRankinRatio_mul_log hy

/-- Quantitative critical curvature lower bound in the normalization relevant
to the central Fourier radius. -/
theorem IsTaoCriticalSmoothRegime.eventually_rankin_div_log_le_normalized_curvature
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      smoothRankinRatio (X n) (y n) /
          (16 * Real.log (smoothRankinRatio (X n) (y n))) ≤
        smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
          Real.log (y n : ℝ) ^ 2 := by
  filter_upwards [
    hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα,
    hregime.eventually_two_mul_phiOne_one_le_log_X hα,
    hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_two_le_X, hregime.eventually_two_le_y hα,
    (hregime.tendsto_rankinRatio_atTop hα).eventually
      (eventually_gt_atTop (1 : ℝ))] with n hgap hhalf hsaddleOne hX hy huOne
  have huPos : 0 < smoothRankinRatio (X n) (y n) := by linarith
  have hlogu : 0 < Real.log (smoothRankinRatio (X n) (y n)) :=
    Real.log_pos huOne
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have hphiTwo : 0 <
      smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) :=
    smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)
  have hdrop := smoothSaddlePhiOne_sub_one_le_phiTwo_mul_one_sub
    hX hy hsaddleOne
  have hcore :
      smoothRankinRatio (X n) (y n) * Real.log (y n : ℝ) / 2 <
        smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) *
          (8 * Real.log (smoothRankinRatio (X n) (y n)) /
            Real.log (y n : ℝ)) := by
    calc
      smoothRankinRatio (X n) (y n) * Real.log (y n : ℝ) / 2 =
          Real.log (X n : ℝ) / 2 := by
        rw [smoothRankinRatio_mul_log hy]
      _ ≤ Real.log (X n : ℝ) - smoothSaddlePhiOne (y n) 1 := by
        linarith
      _ = smoothSaddlePhiOne (y n) (smoothSaddlePoint (X n) (y n)) -
          smoothSaddlePhiOne (y n) 1 := by
        rw [smoothSaddlePhiOne_smoothSaddlePoint hX hy]
      _ ≤ smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) *
          (1 - smoothSaddlePoint (X n) (y n)) := hdrop
      _ < smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) *
          (8 * Real.log (smoothRankinRatio (X n) (y n)) /
            Real.log (y n : ℝ)) :=
        mul_lt_mul_of_pos_left hgap hphiTwo
  have htwoLogY : 0 < (2 : ℝ) * Real.log (y n : ℝ) :=
    mul_pos (by norm_num) hlogy
  have hcross := mul_lt_mul_of_pos_right hcore htwoLogY
  have hcross' :
      smoothRankinRatio (X n) (y n) * Real.log (y n : ℝ) ^ 2 <
        smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) *
          (16 * Real.log (smoothRankinRatio (X n) (y n))) := by
    convert hcross using 1 <;> field_simp [hlogy.ne']; ring
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hlogu)
    (sq_pos_of_pos hlogy)]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcross'.le

/-- The elementary Rankin ratio divided by its logarithm diverges. -/
theorem IsTaoCriticalSmoothRegime.tendsto_rankinRatio_div_sixteen_log_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothRankinRatio (X n) (y n) /
        (16 * Real.log (smoothRankinRatio (X n) (y n)))) atTop atTop := by
  let u : ℕ → ℝ := fun n => smoothRankinRatio (X n) (y n)
  have huTop : Tendsto u atTop atTop := hregime.tendsto_rankinRatio_atTop hα
  have hsmall : Tendsto (fun n => Real.log (u n) / u n)
      atTop (nhds 0) := by
    simpa [u, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp huTop
  have hsmallPos : ∀ᶠ n in atTop, 0 < Real.log (u n) / u n := by
    filter_upwards [huTop.eventually (eventually_gt_atTop (1 : ℝ))] with n hn
    exact div_pos (Real.log_pos hn) (by linarith)
  have hwithin : Tendsto (fun n => Real.log (u n) / u n)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, hsmallPos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  have hscaled := hinv.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 16)
  apply hscaled.congr'
  filter_upwards [huTop.eventually (eventually_gt_atTop (1 : ℝ))] with n hn
  have hu : 0 < u n := by linarith
  have hlogu : Real.log (u n) ≠ 0 := (Real.log_pos hn).ne'
  dsimp [u]
  field_simp [hu.ne', hlogu]

/-- The exact critical saddle curvature, divided by `log(y)^2`, tends to
infinity. -/
theorem IsTaoCriticalSmoothRegime.tendsto_normalized_saddle_curvature_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
        Real.log (y n : ℝ) ^ 2) atTop atTop := by
  refine tendsto_atTop_mono' atTop
    (hregime.eventually_rankin_div_log_le_normalized_curvature hα)
    (hregime.tendsto_rankinRatio_div_sixteen_log_atTop hα)

/-- Equivalently, the largest normalized prime logarithm tends to zero. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_y_div_saddleStandardDeviation_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      Real.log (y n : ℝ) /
        smoothSaddleStandardDeviation (X n) (y n)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt
      (smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
        Real.log (y n : ℝ) ^ 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (hregime.tendsto_normalized_saddle_curvature_atTop hα)
  have hinv : Tendsto (fun n => 1 / Real.sqrt
      (smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
        Real.log (y n : ℝ) ^ 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  apply hinv.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have hphiTwo : 0 <
      smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) :=
    smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)
  unfold smoothSaddleStandardDeviation
  rw [Real.sqrt_div hphiTwo.le, Real.sqrt_sq_eq_abs, abs_of_pos hlogy]
  field_simp [hlogy.ne', (Real.sqrt_pos.2 hphiTwo).ne']

/-- The exact normalized central Fourier radius diverges unconditionally in
every critical smooth regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleCentralRadius_atTop_critical
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleCentralRadius (X n) (y n))
      atTop atTop :=
  hregime.tendsto_smoothSaddleCentralRadius_atTop hα
    (hregime.tendsto_log_y_div_saddleStandardDeviation_zero hα)

/-- Hence every fixed normalized frequency eventually satisfies the universal
Gaussian envelope in the critical regime. -/
theorem IsTaoCriticalSmoothRegime.eventually_norm_normalizedCharacteristic_le_gaussian_critical
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      ‖smoothSaddleNormalizedCharacteristic (X n) (y n) t‖ ≤
        Real.exp (-(1 / Real.pi ^ 2 * t ^ 2)) :=
  hregime.eventually_norm_normalizedCharacteristic_le_gaussian hα
    (hregime.tendsto_log_y_div_saddleStandardDeviation_zero hα)

end

end Tao2026
