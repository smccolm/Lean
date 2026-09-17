import Tao2026.SmoothNumberSaddleIndexedDiagonal

/-!
# Explicit loss scales for indexed outer shells

The four-fifths logarithmic retention gives the natural fixed-index exponent
`(4/5) * 2^(-k)`.  This module converts the raw CEP cofactor loss into an
explicit power of the critical Rankin ratio and proves that the resulting
loss scale diverges for every fixed index.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval Chebyshev

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleIndexedOuterExponent (k : ℕ) : ℝ :=
  (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k

theorem smoothSaddleIndexedOuterExponent_pos (k : ℕ) :
    0 < smoothSaddleIndexedOuterExponent k := by
  unfold smoothSaddleIndexedOuterExponent
  positivity

noncomputable def smoothSaddleIndexedOuterLossScale
    (k X y : ℕ) : ℝ :=
  (Real.exp (-16) *
      (smoothRankinRatio X y / (15 * Real.log 4)) ^
        smoothSaddleIndexedOuterExponent k) /
    (16 * Real.log 2 * Real.log (smoothRankinRatio X y))

/-- The indexed Rankin-ratio power fits inside the retained iterated-root
scale power at the saddle. -/
theorem rankinRatio_rpow_indexedExponent_le_iteratedPrimeScale_rpow
    {X y k : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hlogYOne : 1 ≤ Real.log (y : ℝ))
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y ≤ 1)
    (hscaleLower : smoothSaddleIndexedOuterExponent k *
      Real.log (y : ℝ) ≤
        Real.log (smoothSaddleIteratedPrimeScale k y : ℝ)) :
    (smoothRankinRatio X y / (15 * Real.log 4)) ^
        smoothSaddleIndexedOuterExponent k ≤
      (smoothSaddleIteratedPrimeScale k y : ℝ) ^
        (1 - smoothSaddlePoint X y) := by
  let u := smoothRankinRatio X y
  let sigma := smoothSaddlePoint X y
  let N := smoothSaddleIteratedPrimeScale k y
  let e := 1 - sigma
  let β := smoothSaddleIndexedOuterExponent k
  have he : 0 ≤ e := by dsimp only [e, sigma]; linarith
  have hβ : 0 ≤ β := by
    dsimp only [β]
    exact (smoothSaddleIndexedOuterExponent_pos k).le
  have hyPos : (0 : ℝ) < y := by positivity
  have hN : 2 ≤ N := by
    by_contra hnot
    have hlogN : Real.log (N : ℝ) ≤ 0 := by
      have hNle : N ≤ 1 := by omega
      exact Real.log_nonpos (by positivity) (by exact_mod_cast hNle)
    have hβlog : 0 < β * Real.log (y : ℝ) := by
      exact mul_pos (smoothSaddleIndexedOuterExponent_pos k)
        (by linarith : 0 < Real.log (y : ℝ))
    have : β * Real.log (y : ℝ) ≤ Real.log (N : ℝ) := by
      simpa only [β, N] using hscaleLower
    linarith
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have huPos : 0 < u := by
    dsimp only [u]
    exact smoothRankinRatio_pos hX hy
  have hCPos : 0 < 15 * Real.log 4 := by positivity
  have hbase : u / (15 * Real.log 4) ≤ (y : ℝ) ^ e := by
    simpa only [u, sigma, e] using
      rankinRatio_div_fifteen_log_four_le_saddle_rpow
        hX hy hlogYOne hsigmaHalf hsigmaOne
  have hraise : (u / (15 * Real.log 4)) ^ β ≤
      ((y : ℝ) ^ e) ^ β :=
    Real.rpow_le_rpow (div_nonneg huPos.le hCPos.le) hbase hβ
  have hexponent : β * e * Real.log (y : ℝ) ≤
      e * Real.log (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (show β * Real.log (y : ℝ) ≤ Real.log (N : ℝ) by
        simpa only [β, N] using hscaleLower) he
    nlinarith
  calc
    (smoothRankinRatio X y / (15 * Real.log 4)) ^
        smoothSaddleIndexedOuterExponent k =
        (u / (15 * Real.log 4)) ^ β := by rfl
    _ ≤ ((y : ℝ) ^ e) ^ β := hraise
    _ = (y : ℝ) ^ (e * β) := by rw [Real.rpow_mul hyPos.le]
    _ ≤ (N : ℝ) ^ e := by
      rw [Real.rpow_def_of_pos hyPos, Real.rpow_def_of_pos hNPos]
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (smoothSaddleIteratedPrimeScale k y : ℝ) ^
        (1 - smoothSaddlePoint X y) := by rfl

/-- The raw indexed CEP loss dominates the explicit fixed-index Rankin loss
scale. -/
theorem indexedOuterMultiShell_cosineLoss_lower_at_saddle
    {B X y k : ℕ} {t : ℝ} (hk : 2 ≤ k) (hB : 4 ≤ B)
    (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hterminal : 4 ≤ smoothSaddleIteratedPrimeScale k y)
    (hlogYOne : 1 ≤ Real.log (y : ℝ))
    (hlogU : 12 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huN : smoothRankinRatio X y ≤
      Real.sqrt (smoothSaddleIteratedPrimeScale k y))
    (hscaleLower : smoothSaddleIndexedOuterExponent k *
      Real.log (y : ℝ) ≤
        Real.log (smoothSaddleIteratedPrimeScale k y : ℝ))
    (hscaleUpper : Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) ≤
      (1 / 2 : ℝ) ^ k * Real.log (y : ℝ))
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y ≤ 1)
    (hdisplacement : 1 - smoothSaddlePoint X y ≤
      8 * Real.log (smoothRankinRatio X y) / Real.log (y : ℝ))
    (htLower : smoothSaddleIndexedOuterUpperHeight (k - 1) y ≤ t)
    (htUpper : t ≤ smoothSaddleIndexedOuterUpperHeight k y) :
    smoothSaddleIndexedOuterLossScale k X y ≤
      smoothSaddleCosineLoss y (smoothSaddlePoint X y) t := by
  let u := smoothRankinRatio X y
  let sigma := smoothSaddlePoint X y
  let N := smoothSaddleIteratedPrimeScale k y
  let w := cepDyadicCofactorCutoff N u
  have hN : 2 ≤ N := by dsimp only [N]; omega
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hlogNPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hNleY : N ≤ y := by
    dsimp only [N]
    exact smoothSaddleIteratedPrimeScale_le k y
  have hlogNLeY : Real.log (N : ℝ) ≤ Real.log (y : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hNleY)
  have he : 0 ≤ 1 - sigma := by dsimp only [sigma]; linarith
  have hdispMul : (1 - sigma) * Real.log (y : ℝ) ≤ 8 * Real.log u := by
    apply (le_div_iff₀ hlogyPos).mp
    simpa only [u, sigma] using hdisplacement
  have hdispN : 1 - sigma ≤ 8 * Real.log u / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlogNPos).mpr
    calc
      (1 - sigma) * Real.log (N : ℝ) ≤
          (1 - sigma) * Real.log (y : ℝ) :=
        mul_le_mul_of_nonneg_left hlogNLeY he
      _ ≤ 8 * Real.log u := hdispMul
  have hrankin :=
    rankinRatio_rpow_indexedExponent_le_iteratedPrimeScale_rpow
      hX hy hlogYOne hsigmaHalf hsigmaOne hscaleLower
  have hcofactor := exp_neg_sixteen_mul_rpow_le_cofactor_rpow
    hB hN (by linarith) hBu huN hsigmaOne hdispN
  have hmulti := indexedOuterMultiShell_cosineLoss_lower
    hk hB hN hy (smoothSaddleIteratedPrimeScale_le k y)
    hlogU hBu huN hscaleLower hscaleUpper hpnt hsigmaOne htLower htUpper
  have hleft : Real.exp (-16) *
      (u / (15 * Real.log 4)) ^ smoothSaddleIndexedOuterExponent k ≤
      (w : ℝ) ^ (1 - sigma) := by
    calc
      Real.exp (-16) *
          (u / (15 * Real.log 4)) ^ smoothSaddleIndexedOuterExponent k ≤
          Real.exp (-16) * (N : ℝ) ^ (1 - sigma) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [u, sigma, N] using hrankin) (Real.exp_pos _).le
      _ ≤ (w : ℝ) ^ (1 - sigma) := by
        simpa only [u, sigma, N, w] using hcofactor
  have hden : 0 < 16 * Real.log 2 * Real.log u := by
    have : 0 < Real.log u := by dsimp only [u]; linarith
    positivity
  unfold smoothSaddleIndexedOuterLossScale
  change (Real.exp (-16) *
      (u / (15 * Real.log 4)) ^ smoothSaddleIndexedOuterExponent k) /
        (16 * Real.log 2 * Real.log u) ≤ _
  exact (div_le_div_of_nonneg_right hleft hden.le).trans (by
    simpa only [u, sigma, N, w] using hmulti)

/-- Every fixed indexed shell eventually dominates its explicit loss scale. -/
theorem IsTaoCriticalSmoothRegime.eventually_indexedOuterLossScale_le_cosineLoss
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      smoothSaddleIndexedOuterUpperHeight (k - 1) (y n) ≤ t →
      t ≤ smoothSaddleIndexedOuterUpperHeight k (y n) →
      smoothSaddleIndexedOuterLossScale k (X n) (y n) ≤
        smoothSaddleCosineLoss (y n)
          (smoothSaddlePoint (X n) (y n)) t := by
  obtain ⟨B, hB, hpnt⟩ := exists_chebyshevTheta_quarter_threshold
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  have hloguTop := Real.tendsto_log_atTop.comp huTop
  have hsaddleHalf := (hregime.tendsto_smoothSaddlePoint_one hα).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    hloguTop.eventually (eventually_ge_atTop (12 : ℝ)),
    huTop.eventually (eventually_ge_atTop (B : ℝ)),
    hregime.eventually_indexedIteratedRoot_scale_bounds hα k,
    hregime.eventually_rankinRatio_le_sqrt_iteratedPrimeScale hα k,
    hsaddleHalf, hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα] with
      n hX hy hlogYOne hlogU hBu hscale huN hsigmaHalf hsigmaOne hdisp
  intro t htLower htUpper
  exact indexedOuterMultiShell_cosineLoss_lower_at_saddle
    hk hB hX hy hscale.1 hlogYOne hlogU hBu huN
    hscale.2.1 hscale.2.2 hpnt hsigmaHalf.le hsigmaOne.le hdisp.le
    htLower htUpper

/-- A fixed positive power divided by one logarithm still tends to infinity. -/
theorem tendsto_rpow_div_log_atTop
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => (u n) ^ β / Real.log (u n)) atTop atTop := by
  let γ := β / 2
  have hγ : 0 < γ := by dsimp only [γ]; linarith
  have hpow : Tendsto (fun n => (u n) ^ γ) atTop atTop :=
    (tendsto_rpow_atTop hγ).comp hu
  have hlogSmall := (isLittleO_log_rpow_atTop hγ).def
    (by norm_num : (0 : ℝ) < 1)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [hu.eventually hlogSmall,
    hu.eventually (eventually_gt_atTop (1 : ℝ))] with n hlog huOne
  have huPos : 0 < u n := lt_trans zero_lt_one huOne
  have hlogPos : 0 < Real.log (u n) := Real.log_pos huOne
  have hpowPos : 0 < (u n) ^ γ := Real.rpow_pos_of_pos huPos _
  have hlogLe : Real.log (u n) ≤ (u n) ^ γ := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogPos,
      abs_of_pos hpowPos, one_mul] using hlog
  rw [le_div_iff₀ hlogPos]
  calc
    (u n) ^ γ * Real.log (u n) ≤ (u n) ^ γ * (u n) ^ γ :=
      mul_le_mul_of_nonneg_left hlogLe hpowPos.le
    _ = (u n) ^ β := by
      rw [← Real.rpow_add huPos]
      congr 1
      dsimp only [γ]
      ring

/-- At every fixed indexed depth, the explicit loss scale diverges. -/
theorem IsTaoCriticalSmoothRegime.tendsto_indexedOuterLossScale_atTop
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (k : ℕ) :
    Tendsto (fun n => smoothSaddleIndexedOuterLossScale k (X n) (y n))
      atTop atTop := by
  let β := smoothSaddleIndexedOuterExponent k
  let C : ℝ := 15 * Real.log 4
  let A : ℝ := Real.exp (-16) / (C ^ β * (16 * Real.log 2))
  have hβ : 0 < β := by
    dsimp only [β]
    exact smoothSaddleIndexedOuterExponent_pos k
  have hC : 0 < C := by dsimp only [C]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hbase := tendsto_rpow_div_log_atTop
    (hregime.tendsto_rankinRatio_atTop hα) hβ
  have hscaled := hbase.const_mul_atTop hA
  apply hscaled.congr'
  filter_upwards [(hregime.tendsto_rankinRatio_atTop hα).eventually
    (eventually_gt_atTop (1 : ℝ))] with n hu
  have huPos : 0 < smoothRankinRatio (X n) (y n) := lt_trans zero_lt_one hu
  have hlogu : Real.log (smoothRankinRatio (X n) (y n)) ≠ 0 :=
    (Real.log_pos hu).ne'
  unfold smoothSaddleIndexedOuterLossScale
  dsimp only [A, C, β]
  rw [Real.div_rpow huPos.le hC.le]
  field_simp [hlogu, hC.ne',
    (Real.rpow_pos_of_pos hC (smoothSaddleIndexedOuterExponent k)).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

end

end Tao2026
