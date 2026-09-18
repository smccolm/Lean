import Tao2026.SmoothNumberSaddleHTPerronArithmeticSharp
import Tao2026.SpecializedGrowingFourier

/-!
# Absorption of the HT sharp-Perron truncation error

The harmonic-strength arithmetic bound has only fixed logarithmic losses.
For `0 < epsilon < 1`, the height exponent `3/2-epsilon` is strictly larger
than the target decay exponent `epsilon/2`.  This module makes that exponent
gap quantitative and absorbs the endpoint, near, and far terms into the
equation-(3.10) allowance.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- A fixed nonnegative constant and fixed logarithmic power can be inserted
into a stretched exponential with a strictly larger positive exponent. -/
theorem eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
    {C α β : ℝ} (hβ : 0 < β) (hαβ : α < β) (B : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      C * (Real.log y) ^ (B : ℝ) * Real.exp ((Real.log y) ^ α) ≤
        Real.exp ((Real.log y) ^ β) := by
  have hmain := eventually_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
    hβ hαβ (B + 1)
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hmain, hlogTop.eventually (eventually_ge_atTop C),
    eventually_ge_atTop 2] with y hmainY hCY hy
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hpow : C * (Real.log y) ^ (B : ℝ) ≤
      (Real.log y) ^ ((B + 1 : ℕ) : ℝ) := by
    calc
      C * (Real.log y) ^ (B : ℝ) ≤
          Real.log y * (Real.log y) ^ (B : ℝ) :=
        mul_le_mul_of_nonneg_right hCY (Real.rpow_nonneg hlogPos.le _)
      _ = (Real.log y) ^ ((B + 1 : ℕ) : ℝ) := by
        rw [show ((B + 1 : ℕ) : ℝ) = 1 + (B : ℝ) by push_cast; ring,
          Real.rpow_add hlogPos]
        simp
  exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans hmainY

theorem smoothSaddleHT_decayExponent_lt_heightExponent
    {ε : ℝ} (hε : ε < 1) :
    ε / 2 < (3 : ℝ) / 2 - ε := by linarith

theorem smoothSaddleHT_heightExponent_pos
    {ε : ℝ} (hε : ε < 1) :
    0 < (3 : ℝ) / 2 - ε := by linarith

theorem log_two_mul_natCast_le_two_log
    {y : ℕ} (hy : 2 ≤ y) :
    Real.log (2 * (y : ℝ)) ≤ 2 * Real.log y := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hlogTwoLe : Real.log 2 ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hy)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hyPos.ne']
  linarith

theorem log_natCast_add_one_le_two_log
    {y : ℕ} (hy : 2 ≤ y) :
    Real.log ((y : ℝ) + 1) ≤ 2 * Real.log y := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hsumPos : 0 < (y : ℝ) + 1 := by positivity
  have hsumLe : (y : ℝ) + 1 ≤ 2 * y := by
    have : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
    linarith
  exact (Real.log_le_log hsumPos hsumLe).trans
    (log_two_mul_natCast_le_two_log hy)

theorem one_add_log_natCast_add_one_le_three_log
    {y : ℕ} (hy : 2 ≤ y) (hlog : 1 ≤ Real.log y) :
    1 + Real.log ((y : ℝ) + 1) ≤ 3 * Real.log y := by
  linarith [log_natCast_add_one_le_two_log hy]

theorem log_add_const_le_one_add_const_mul_log
    {y : ℕ} {C : ℝ} (hC : 0 ≤ C) (hlog : 1 ≤ Real.log y) :
    Real.log y + C ≤ (1 + C) * Real.log y := by
  nlinarith

noncomputable def smoothSaddleHTPerronEndpointExplicitBound (y : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ)

noncomputable def smoothSaddleHTPerronNearExplicitBound
    (y : ℕ) (ε : ℝ) : ℝ :=
  (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
      (Real.pi * smoothSaddleHTContourHeight y ε)) *
    (8 * (1 + Real.log (y + 1)))

noncomputable def smoothSaddleHTPerronFarExplicitBound
    (C₀ : ℝ) (y : ℕ) (ε : ℝ) : ℝ :=
  (2 * (Real.exp 1 * y) /
      (Real.pi * smoothSaddleHTContourHeight y ε)) *
    (Real.log y + C₀)

noncomputable def smoothSaddleHTPerronTargetBound
    (y : ℕ) (ε : ℝ) : ℝ :=
  (y : ℝ) * Real.exp (-(Real.log y) ^ (ε / 2))

theorem eventually_smoothSaddleHTPerronEndpointExplicitBound_le_target_third
    {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      smoothSaddleHTPerronEndpointExplicitBound y ≤
        smoothSaddleHTPerronTargetBound y ε / 3 := by
  have hmain :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := (9 / 2 : ℝ)) (α := ε / 2) (β := 1)
      (by norm_num) (by linarith) 1
  filter_upwards [hmain, eventually_ge_atTop 2] with y hmainY hy
  have hyPos : 0 < (y : ℝ) := by positivity
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hLambda : ArithmeticFunction.vonMangoldt y ≤ Real.log y :=
    ArithmeticFunction.vonMangoldt_le_log
  have hendpoint : 3 * smoothSaddleHTPerronEndpointExplicitBound y ≤
      (9 / 2 : ℝ) * Real.log y := by
    unfold smoothSaddleHTPerronEndpointExplicitBound
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := y)]
  have hscaled : 3 * smoothSaddleHTPerronEndpointExplicitBound y *
      Real.exp ((Real.log y) ^ (ε / 2)) ≤ (y : ℝ) := by
    calc
      3 * smoothSaddleHTPerronEndpointExplicitBound y *
          Real.exp ((Real.log y) ^ (ε / 2)) ≤
        (9 / 2 : ℝ) * Real.log y *
          Real.exp ((Real.log y) ^ (ε / 2)) := by
            exact mul_le_mul_of_nonneg_right hendpoint (Real.exp_pos _).le
      _ ≤ Real.exp ((Real.log y) ^ (1 : ℝ)) := by
        simpa only [Nat.cast_one, Real.rpow_one] using hmainY
      _ = (y : ℝ) := by rw [Real.rpow_one, Real.exp_log hyPos]
  have hE : 0 < Real.exp ((Real.log y) ^ (ε / 2)) := Real.exp_pos _
  unfold smoothSaddleHTPerronTargetBound
  have hinv : Real.exp (-(Real.log y) ^ (ε / 2)) =
      (Real.exp ((Real.log y) ^ (ε / 2)))⁻¹ := by
    rw [Real.exp_neg]
  rw [hinv]
  calc
    smoothSaddleHTPerronEndpointExplicitBound y ≤
        (y : ℝ) / (3 * Real.exp ((Real.log y) ^ (ε / 2))) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hE)]
      rw [show smoothSaddleHTPerronEndpointExplicitBound y *
          (3 * Real.exp ((Real.log y) ^ (ε / 2))) =
        3 * smoothSaddleHTPerronEndpointExplicitBound y *
          Real.exp ((Real.log y) ^ (ε / 2)) by ring]
      exact hscaled
    _ = (y : ℝ) * (Real.exp ((Real.log y) ^ (ε / 2)))⁻¹ / 3 := by
      field_simp

theorem eventually_smoothSaddleHTPerronNearExplicitBound_le_target_third
    {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      smoothSaddleHTPerronNearExplicitBound y ε ≤
        smoothSaddleHTPerronTargetBound y ε / 3 := by
  let R := GafniTao.sharpPerronRatioBound
  have hR : 0 ≤ R :=
    (le_trans (by norm_num) GafniTao.one_le_sharpPerronRatioBound)
  have hgap := smoothSaddleHT_decayExponent_lt_heightExponent hε
  have hheight := smoothSaddleHT_heightExponent_pos hε
  have hmain :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := 288 * R) (α := ε / 2) (β := (3 : ℝ) / 2 - ε)
      hheight hgap 2
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hmain, hlogTop.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 2] with y hmainY hlog hy
  have hyPos : 0 < (y : ℝ) := by positivity
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogTwo := log_two_mul_natCast_le_two_log hy
  have hlogSucc := one_add_log_natCast_add_one_le_three_log hy hlog
  have hlogSuccNonneg : 0 ≤ 1 + Real.log ((y : ℝ) + 1) := by
    have : 0 ≤ Real.log ((y : ℝ) + 1) :=
      Real.log_nonneg (by
        have hy0 : (0 : ℝ) ≤ y := by positivity
        linarith)
    linarith
  let Ea := Real.exp ((Real.log y) ^ (ε / 2))
  let Eq := Real.exp ((Real.log y) ^ ((3 : ℝ) / 2 - ε))
  have hEa : 0 < Ea := by dsimp [Ea]; positivity
  have hEq : 0 < Eq := by dsimp [Eq]; positivity
  have hprod : R * Real.log (2 * (y : ℝ)) * (2 * y) *
      (8 * (1 + Real.log ((y : ℝ) + 1))) ≤
        96 * R * y * (Real.log y) ^ 2 := by
    calc
      R * Real.log (2 * (y : ℝ)) * (2 * y) *
          (8 * (1 + Real.log ((y : ℝ) + 1))) ≤
        R * (2 * Real.log y) * (2 * y) *
          (8 * (3 * Real.log y)) := by
            gcongr
      _ = 96 * R * y * (Real.log y) ^ 2 := by ring
  have hden : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hnum :
      (R * Real.log (2 * (y : ℝ)) * (2 * y) *
          (8 * (1 + Real.log ((y : ℝ) + 1)))) / (2 * Real.pi) ≤
        96 * R * y * (Real.log y) ^ 2 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    have hnonneg : 0 ≤ 96 * R * y * (Real.log y) ^ 2 := by positivity
    exact hprod.trans (by
      nlinarith [mul_le_mul_of_nonneg_left hden hnonneg])
  have hnear : smoothSaddleHTPerronNearExplicitBound y ε ≤
      (96 * R * y * (Real.log y) ^ 2) / Eq := by
    unfold smoothSaddleHTPerronNearExplicitBound
      smoothSaddleHTContourHeight smoothSaddleHTFrequencyCeiling
    change
      (R * Real.log (2 * (y : ℝ)) * (2 * y) /
          (Real.pi * (2 * Eq))) *
          (8 * (1 + Real.log ((y : ℝ) + 1))) ≤
        (96 * R * y * (Real.log y) ^ 2) / Eq
    rw [show (R * Real.log (2 * (y : ℝ)) * (2 * y) /
          (Real.pi * (2 * Eq))) *
          (8 * (1 + Real.log ((y : ℝ) + 1))) =
        ((R * Real.log (2 * (y : ℝ)) * (2 * y) *
          (8 * (1 + Real.log ((y : ℝ) + 1)))) / (2 * Real.pi)) /
            Eq by ring]
    exact div_le_div_of_nonneg_right hnum hEq.le
  have hmainY' : 288 * R * (Real.log y) ^ 2 * Ea ≤ Eq := by
    dsimp [R, Ea, Eq]
    simpa only [Nat.cast_ofNat, Real.rpow_two] using hmainY
  unfold smoothSaddleHTPerronTargetBound
  have hinv : Real.exp (-(Real.log y) ^ (ε / 2)) = Ea⁻¹ := by
    dsimp [Ea]
    rw [Real.exp_neg]
  rw [hinv]
  calc
    smoothSaddleHTPerronNearExplicitBound y ε ≤
        (96 * R * y * (Real.log y) ^ 2) / Eq := hnear
    _ ≤ (y : ℝ) / (3 * Ea) := by
      rw [div_le_div_iff₀ hEq (mul_pos (by norm_num) hEa)]
      have hmul := mul_le_mul_of_nonneg_right hmainY' hyPos.le
      nlinarith
    _ = (y : ℝ) * Ea⁻¹ / 3 := by field_simp

theorem eventually_smoothSaddleHTPerronFarExplicitBound_le_target_third
    {C₀ ε : ℝ} (hC₀ : 0 ≤ C₀) (hε : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      smoothSaddleHTPerronFarExplicitBound C₀ y ε ≤
        smoothSaddleHTPerronTargetBound y ε / 3 := by
  have hgap := smoothSaddleHT_decayExponent_lt_heightExponent hε
  have hheight := smoothSaddleHT_heightExponent_pos hε
  have hmain :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := 3 * Real.exp 1 * (1 + C₀))
      (α := ε / 2) (β := (3 : ℝ) / 2 - ε) hheight hgap 1
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hmain, hlogTop.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 2] with y hmainY hlog hy
  have hyPos : 0 < (y : ℝ) := by positivity
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogC := log_add_const_le_one_add_const_mul_log hC₀ hlog
  let Ea := Real.exp ((Real.log y) ^ (ε / 2))
  let Eq := Real.exp ((Real.log y) ^ ((3 : ℝ) / 2 - ε))
  have hEa : 0 < Ea := by dsimp [Ea]; positivity
  have hEq : 0 < Eq := by dsimp [Eq]; positivity
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hnumNonneg : 0 ≤ Real.exp 1 * (y : ℝ) *
      ((1 + C₀) * Real.log y) := by positivity
  have hnum :
      (Real.exp 1 * (y : ℝ) * (Real.log y + C₀)) / Real.pi ≤
        Real.exp 1 * y * ((1 + C₀) * Real.log y) := by
    rw [div_le_iff₀ Real.pi_pos]
    have hfirst : Real.exp 1 * (y : ℝ) * (Real.log y + C₀) ≤
        Real.exp 1 * y * ((1 + C₀) * Real.log y) := by
      gcongr
    exact hfirst.trans (by
      nlinarith [mul_le_mul_of_nonneg_left hpi hnumNonneg])
  have hfar : smoothSaddleHTPerronFarExplicitBound C₀ y ε ≤
      (Real.exp 1 * y * ((1 + C₀) * Real.log y)) / Eq := by
    unfold smoothSaddleHTPerronFarExplicitBound
      smoothSaddleHTContourHeight smoothSaddleHTFrequencyCeiling
    change
      (2 * (Real.exp 1 * y) / (Real.pi * (2 * Eq))) *
          (Real.log y + C₀) ≤
        (Real.exp 1 * y * ((1 + C₀) * Real.log y)) / Eq
    rw [show (2 * (Real.exp 1 * y) / (Real.pi * (2 * Eq))) *
          (Real.log y + C₀) =
        ((Real.exp 1 * y * (Real.log y + C₀)) / Real.pi) / Eq by ring]
    exact div_le_div_of_nonneg_right hnum hEq.le
  have hmainY' : 3 * Real.exp 1 * (1 + C₀) * Real.log y * Ea ≤ Eq := by
    dsimp [Ea, Eq]
    simpa only [Nat.cast_one, Real.rpow_one] using hmainY
  unfold smoothSaddleHTPerronTargetBound
  have hinv : Real.exp (-(Real.log y) ^ (ε / 2)) = Ea⁻¹ := by
    dsimp [Ea]
    rw [Real.exp_neg]
  rw [hinv]
  calc
    smoothSaddleHTPerronFarExplicitBound C₀ y ε ≤
        (Real.exp 1 * y * ((1 + C₀) * Real.log y)) / Eq := hfar
    _ ≤ (y : ℝ) / (3 * Ea) := by
      rw [div_le_div_iff₀ hEq (mul_pos (by norm_num) hEa)]
      have hmul := mul_le_mul_of_nonneg_right hmainY' hyPos.le
      nlinarith
    _ = (y : ℝ) * Ea⁻¹ / 3 := by field_simp

/-- The complete scalar Perron majorant is eventually absorbed by the
equation-(3.10) stretched-exponential term. -/
theorem eventually_tsum_smoothSaddleHTPerronTruncationMajorant_le_target
    {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      (∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y
        (smoothSaddleHTContourHeight y ε) n) ≤
          smoothSaddleHTPerronTargetBound y ε := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    exists_tsum_smoothSaddleHTPerronTruncationMajorant_le_sharp_explicit
  filter_upwards
    [eventually_smoothSaddleHTPerronEndpointExplicitBound_le_target_third hε,
      eventually_smoothSaddleHTPerronNearExplicitBound_le_target_third hε,
      eventually_smoothSaddleHTPerronFarExplicitBound_le_target_third hC₀ hε,
      eventually_ge_atTop 2] with y hend hnear hfar hy
  have hsum := hbound y (smoothSaddleHTContourHeight y ε) hy
    (smoothSaddleHTContourHeight_pos y ε)
  have hsum' :
      (∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y
        (smoothSaddleHTContourHeight y ε) n) ≤
          smoothSaddleHTPerronEndpointExplicitBound y +
            smoothSaddleHTPerronNearExplicitBound y ε +
            smoothSaddleHTPerronFarExplicitBound C₀ y ε := by
    simpa [smoothSaddleHTPerronEndpointExplicitBound,
      smoothSaddleHTPerronNearExplicitBound,
      smoothSaddleHTPerronFarExplicitBound] using hsum
  calc
    (∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y
        (smoothSaddleHTContourHeight y ε) n) ≤
      smoothSaddleHTPerronEndpointExplicitBound y +
        smoothSaddleHTPerronNearExplicitBound y ε +
        smoothSaddleHTPerronFarExplicitBound C₀ y ε := hsum'
    _ ≤ smoothSaddleHTPerronTargetBound y ε / 3 +
          smoothSaddleHTPerronTargetBound y ε / 3 +
          smoothSaddleHTPerronTargetBound y ε / 3 :=
      add_le_add (add_le_add hend hnear) hfar
    _ = smoothSaddleHTPerronTargetBound y ε := by ring

/-- The complete complex truncation error has the desired source decay,
uniformly in `beta` and the frequency `t`. -/
theorem eventually_norm_smoothSaddleHTContourTruncationError_le_target
    {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ (beta t : ℝ), 0 < beta →
      ‖smoothSaddleHTContourTruncationError y beta ε t‖ ≤
        (y : ℝ) ^ beta * Real.exp (-(Real.log y) ^ (ε / 2)) := by
  filter_upwards
    [eventually_tsum_smoothSaddleHTPerronTruncationMajorant_le_target hε,
      eventually_ge_atTop 2] with y hsum hy
  intro beta t hbeta
  have hfirst :=
    norm_smoothSaddleHTContourTruncationError_le_tsum_majorant
      (ε := ε) (t := t) hy hbeta
  have hpow0 : 0 ≤ (y : ℝ) ^ (beta - 1) := by positivity
  calc
    ‖smoothSaddleHTContourTruncationError y beta ε t‖ ≤
        (y : ℝ) ^ (beta - 1) *
          ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y
            (smoothSaddleHTContourHeight y ε) n := hfirst
    _ ≤ (y : ℝ) ^ (beta - 1) *
          smoothSaddleHTPerronTargetBound y ε :=
      mul_le_mul_of_nonneg_left hsum hpow0
    _ = (y : ℝ) ^ beta * Real.exp (-(Real.log y) ^ (ε / 2)) := by
      unfold smoothSaddleHTPerronTargetBound
      have hyPos : 0 < (y : ℝ) := by positivity
      have hp : (y : ℝ) ^ (beta - 1) * (y : ℝ) = (y : ℝ) ^ beta := by
        calc
          (y : ℝ) ^ (beta - 1) * (y : ℝ) =
              (y : ℝ) ^ (beta - 1) * (y : ℝ) ^ (1 : ℝ) := by simp
          _ = (y : ℝ) ^ ((beta - 1) + 1) := by
            rw [Real.rpow_add hyPos]
          _ = (y : ℝ) ^ beta := by ring_nf
      rw [← mul_assoc, hp]

/-- In particular, the truncation error is eventually bounded by the full
HT Lemma-6 error allowance for every `0<beta<1`. -/
theorem eventually_norm_smoothSaddleHTContourTruncationError_le_mangoldtError
    {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ (beta t : ℝ), 0 < beta → beta < 1 →
      ‖smoothSaddleHTContourTruncationError y beta ε t‖ ≤
        smoothSaddleHTMangoldtError y beta ε := by
  filter_upwards
    [eventually_norm_smoothSaddleHTContourTruncationError_le_target hε]
      with y hbound
  intro beta t hbeta hbetaOne
  have htarget0 : 0 ≤ (y : ℝ) ^ beta *
      Real.exp (-(Real.log y) ^ (ε / 2)) := by positivity
  have hinv : 1 ≤ (1 / beta : ℝ) := by
    rw [le_div_iff₀ hbeta]
    linarith
  refine (hbound beta t hbeta).trans ?_
  unfold smoothSaddleHTMangoldtError
  let X := (y : ℝ) ^ beta * Real.exp (-(Real.log y) ^ (ε / 2))
  have hX : 0 ≤ X := htarget0
  calc
    X ≤ 1 + X := by linarith
    _ = 1 * (1 + X) := by ring
    _ ≤ (1 / beta) * (1 + X) :=
      mul_le_mul_of_nonneg_right hinv (add_nonneg (by norm_num) hX)

end

end Tao2026
