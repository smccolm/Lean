import Tao2026.SmoothNumberSaddlePoint
import Tao2026.SmoothNumberCriticalLower
import Tao2026.SmoothNumberCEPBootstrap
import Tao2026.CoefficientBounds

/-!
# The exact saddle point in Tao's critical regime

This file locates the exact finite-prime saddle parameter in the critical
smooth-number regime.  The upper comparison at `sigma = 1` uses the explicit
Abel--Chebyshev estimate for `sum_{p <= y} log p / p`; the lower comparison at
a fixed `sigma < 1` uses the elementary lower bound supplied by the number of
primes up to `y`.  Together these show that the exact saddle tends to `1`.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- At `sigma = 1`, a saddle summand is at most twice the corresponding
weighted prime-log summand. -/
theorem smoothSaddlePrimeTerm_one_le {p : ℕ} (hp : 2 ≤ p) :
    smoothSaddlePrimeTerm p 1 ≤ 2 * (Real.log p / p) := by
  unfold smoothSaddlePrimeTerm
  rw [Real.rpow_one]
  have hpReal : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < p := by positivity
  have hdenPos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlogNonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by linarith)
  rw [div_le_iff₀ hdenPos]
  field_simp [hpPos.ne']
  nlinarith

/-- Explicit `O(log y)` upper bound for the first saddle sum at `sigma = 1`.
-/
theorem smoothSaddlePhiOne_one_le (y : ℕ) (hy : 0 < y) :
    smoothSaddlePhiOne y 1 ≤
      2 * Real.log 4 * (2 + Real.log y) := by
  calc
    smoothSaddlePhiOne y 1 ≤
        ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
          2 * (Real.log p / p) := by
      unfold smoothSaddlePhiOne
      exact Finset.sum_le_sum fun p hp =>
        smoothSaddlePrimeTerm_one_le
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    _ = 2 * weightedPrimeLogSum y := by
      rw [weightedPrimeLogSum, Finset.mul_sum]
    _ ≤ 2 * (Real.log 4 * (2 + Real.log y)) := by
      gcongr
      exact weightedPrimeLogSum_le y hy
    _ = 2 * Real.log 4 * (2 + Real.log y) := by ring

/-- Every prime contributes at least `log 2 / y^sigma` to the first saddle
sum when `0 < sigma` and `p <= y`. -/
theorem log_two_div_rpow_le_smoothSaddlePrimeTerm
    {y p : ℕ} {sigma : ℝ} (hp : p.Prime) (hpy : p ≤ y)
    (hsigma : 0 < sigma) :
    Real.log 2 / (y : ℝ) ^ sigma ≤ smoothSaddlePrimeTerm p sigma := by
  have hp2 : 2 ≤ p := hp.two_le
  have hy2 : 2 ≤ y := hp2.trans hpy
  have hpPos : (0 : ℝ) < p := by positivity
  have hyPos : (0 : ℝ) < y := by positivity
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hpPos
      (by exact_mod_cast hp2)
  have hpPowLe : (p : ℝ) ^ sigma ≤ (y : ℝ) ^ sigma :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpy) hsigma.le
  have hdenPos : 0 < (p : ℝ) ^ sigma - 1 :=
    smoothSaddle_denominator_pos hp2 hsigma
  have hdenLe : (p : ℝ) ^ sigma - 1 ≤ (y : ℝ) ^ sigma :=
    (sub_le_self _ (by norm_num)).trans hpPowLe
  unfold smoothSaddlePrimeTerm
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hyPos sigma) hdenPos]
  exact mul_le_mul hlog hdenLe hdenPos.le
    (Real.log_nonneg (by exact_mod_cast hp.one_le))

/-- A finite prime-counting lower bound for the first saddle sum. -/
theorem primeCounting_mul_log_two_div_rpow_le_smoothSaddlePhiOne
    {y : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) :
    (Nat.primeCounting y : ℝ) *
        (Real.log 2 / (y : ℝ) ^ sigma) ≤
      smoothSaddlePhiOne y sigma := by
  rw [smoothSaddlePhiOne]
  have hset : (Finset.Icc 2 y).filter Nat.Prime = y.primesLE := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    constructor
    · intro hp
      exact ⟨hp.1.2, hp.2⟩
    · intro hp
      exact ⟨⟨hp.2.two_le, hp.1⟩, hp.2⟩
  have hcard : ((Finset.Icc 2 y).filter Nat.Prime).card =
      Nat.primeCounting y := by
    rw [hset, Nat.primesLE_card_eq_primeCounting]
  rw [← hcard]
  calc
    (((Finset.Icc 2 y).filter Nat.Prime).card : ℝ) *
          (Real.log 2 / (y : ℝ) ^ sigma) =
        ∑ _p ∈ (Finset.Icc 2 y).filter Nat.Prime,
          Real.log 2 / (y : ℝ) ^ sigma := by simp
    _ ≤ ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
          smoothSaddlePrimeTerm p sigma :=
      Finset.sum_le_sum fun p hp =>
        log_two_div_rpow_le_smoothSaddlePrimeTerm
          (Finset.mem_filter.mp hp).2
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 hsigma

/-- The second saddle summand dominates `log 2` times the first one. -/
theorem log_two_mul_smoothSaddlePrimeTerm_le_second
    {p : ℕ} (hp : 2 ≤ p) {sigma : ℝ} (hsigma : 0 < sigma) :
    Real.log 2 * smoothSaddlePrimeTerm p sigma ≤
      smoothSaddleSecondPrimeTerm p sigma := by
  unfold smoothSaddlePrimeTerm smoothSaddleSecondPrimeTerm
  have hpPos : (0 : ℝ) < p := by positivity
  have hlogPos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogTwo : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hpPos
      (by exact_mod_cast hp)
  have hdenPos : 0 < (p : ℝ) ^ sigma - 1 :=
    smoothSaddle_denominator_pos hp hsigma
  have hpowPos : 0 < (p : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos hpPos sigma
  field_simp [hdenPos.ne']
  have hcore : Real.log 2 * ((p : ℝ) ^ sigma - 1) ≤
      Real.log (p : ℝ) * (p : ℝ) ^ sigma := by
    exact mul_le_mul hlogTwo (sub_le_self _ (by norm_num)) hdenPos.le
      hlogPos.le
  nlinarith

/-- Globally, `phiTwo` dominates `log 2 * phiOne` on the positive axis. -/
theorem log_two_mul_smoothSaddlePhiOne_le_phiTwo
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Real.log 2 * smoothSaddlePhiOne y sigma ≤
      smoothSaddlePhiTwo y sigma := by
  unfold smoothSaddlePhiOne smoothSaddlePhiTwo
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p hp =>
    log_two_mul_smoothSaddlePrimeTerm_le_second
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1 hsigma

/-- At its exact saddle, `phiTwo` is at least `log 2 * log X`. -/
theorem log_two_mul_log_le_smoothSaddlePhiTwo_saddle
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    Real.log 2 * Real.log (X : ℝ) ≤
      smoothSaddlePhiTwo y (smoothSaddlePoint X y) := by
  simpa [smoothSaddlePhiOne_smoothSaddlePoint hX hy] using
    log_two_mul_smoothSaddlePhiOne_le_phiTwo y
      (smoothSaddlePoint_pos hX hy)

/-- Exact finite sensitivity bound: increasing `X` changes the saddle by at
most the logarithmic increment divided by `log 2 * log X₁`. -/
theorem smoothSaddlePoint_sub_le_log_sub_div
    {X₁ X₂ y : ℕ} (hX₁ : 2 ≤ X₁) (hX : X₁ < X₂) (hy : 2 ≤ y) :
    smoothSaddlePoint X₁ y - smoothSaddlePoint X₂ y ≤
      (Real.log (X₂ : ℝ) - Real.log (X₁ : ℝ)) /
        (Real.log 2 * Real.log (X₁ : ℝ)) := by
  obtain ⟨xi, hxi, hsecant⟩ :=
    exists_smoothSaddlePoint_secant hX₁ hX hy
  have hX₂ : 2 ≤ X₂ := hX₁.trans hX.le
  have hxiPos : 0 < xi :=
    (smoothSaddlePoint_pos hX₂ hy).trans hxi.1
  have hX₁Real : (1 : ℝ) < X₁ := by
    exact_mod_cast (show 1 < X₁ by omega)
  have hdenPos : 0 < Real.log 2 * Real.log (X₁ : ℝ) :=
    mul_pos (Real.log_pos (by norm_num)) (Real.log_pos hX₁Real)
  have hphiOne : Real.log (X₁ : ℝ) < smoothSaddlePhiOne y xi := by
    have hstrict := (smoothSaddlePhiOne_strictAntiOn hy)
      hxiPos (smoothSaddlePoint_pos hX₁ hy) hxi.2
    simpa [smoothSaddlePhiOne_smoothSaddlePoint hX₁ hy] using hstrict
  have hcurvature : Real.log 2 * Real.log (X₁ : ℝ) <
      smoothSaddlePhiTwo y xi := by
    calc
      Real.log 2 * Real.log (X₁ : ℝ) <
          Real.log 2 * smoothSaddlePhiOne y xi :=
        mul_lt_mul_of_pos_left hphiOne (Real.log_pos (by norm_num))
      _ ≤ smoothSaddlePhiTwo y xi :=
        log_two_mul_smoothSaddlePhiOne_le_phiTwo y hxiPos
  have hsaddleDiff : 0 <
      smoothSaddlePoint X₁ y - smoothSaddlePoint X₂ y :=
    sub_pos.mpr (smoothSaddlePoint_strictAnti_left hX₁ hX hy)
  rw [le_div_iff₀ hdenPos]
  rw [hsecant]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hcurvature.le hsaddleDiff.le)

/-- The critical Rankin ratio is eventually smaller than every fixed
positive power of the smoothness cutoff. -/
theorem IsTaoCriticalSmoothRegime.eventually_rankinRatio_le_y_rpow
    {X y : ℕ → ℕ} {α δ : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ x in atTop,
      smoothRankinRatio (X x) (y x) ≤ (y x : ℝ) ^ δ := by
  have hratio :=
    (hregime.tendsto_log_rankinRatio_div_log_y_zero hα).eventually
      (Iio_mem_nhds hδ)
  filter_upwards [hratio, hregime.eventually_two_le_y hα] with x hx hy
  have hyPos : (0 : ℝ) < y x := by exact_mod_cast (show 0 < y x by omega)
  have hlogyPos : 0 < Real.log (y x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y x by omega))
  have hlogBound :
      Real.log (smoothRankinRatio (X x) (y x)) ≤
        δ * Real.log (y x) :=
    ((div_lt_iff₀ hlogyPos).mp hx).le
  exact Real.le_rpow_of_log_le hyPos hlogBound

/-- Every fixed positive power of `y` eventually dominates the Rankin ratio
and two logarithmic factors. -/
theorem IsTaoCriticalSmoothRegime.eventually_rankinRatio_mul_log_sq_lt_mul_rpow
    {X y : ℕ → ℕ} {α ε c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ x in atTop,
      smoothRankinRatio (X x) (y x) * (Real.log (y x)) ^ 2 <
        c * (y x : ℝ) ^ ε := by
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hrankin := hregime.eventually_rankinRatio_le_y_rpow hα hδ
  have hyTop : Tendsto (fun x => (y x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hregime.tendsto_y_atTop hα)
  have hypowTop : Tendsto (fun x => (y x : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp hyTop
  have hlarge : ∀ᶠ x in atTop,
      1 / δ ^ 2 < c * (y x : ℝ) ^ δ :=
    (hypowTop.const_mul_atTop hc).eventually
      (eventually_gt_atTop (1 / δ ^ 2))
  filter_upwards [hrankin, hlarge, hregime.eventually_two_le_y hα] with
      x hrankinX hlargeX hy
  have hyNonneg : (0 : ℝ) ≤ y x := by positivity
  have hyPos : (0 : ℝ) < y x := by positivity
  have hypowPos : 0 < (y x : ℝ) ^ δ := Real.rpow_pos_of_pos hyPos δ
  have hlogNonneg : 0 ≤ Real.log (y x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y x by omega))
  have hlogBound : Real.log (y x : ℝ) ≤ (y x : ℝ) ^ δ / δ :=
    Real.log_le_rpow_div hyNonneg hδ
  calc
    smoothRankinRatio (X x) (y x) * (Real.log (y x)) ^ 2 ≤
        (y x : ℝ) ^ δ * (((y x : ℝ) ^ δ / δ) ^ 2) := by
      gcongr
    _ = (1 / δ ^ 2) * (y x : ℝ) ^ (3 * δ) := by
      rw [show (3 : ℝ) * δ = δ + δ + δ by ring,
        Real.rpow_add hyPos, Real.rpow_add hyPos]
      field_simp [hδ.ne']
    _ < (c * (y x : ℝ) ^ δ) * (y x : ℝ) ^ (3 * δ) :=
      mul_lt_mul_of_pos_right hlargeX
        (Real.rpow_pos_of_pos hyPos (3 * δ))
    _ = c * (y x : ℝ) ^ ε := by
      calc
        (c * (y x : ℝ) ^ δ) * (y x : ℝ) ^ (3 * δ) =
            c * ((y x : ℝ) ^ δ * (y x : ℝ) ^ (3 * δ)) := by ring
        _ = c * (y x : ℝ) ^ (δ + 3 * δ) := by
          rw [Real.rpow_add hyPos]
        _ = c * (y x : ℝ) ^ ε := by
          congr 2
          dsimp [δ]
          ring

/-- In the critical regime the first saddle sum at `1` is eventually below
`log X`. -/
theorem IsTaoCriticalSmoothRegime.eventually_smoothSaddlePhiOne_one_lt_log_X
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    ∀ᶠ x in atTop,
      smoothSaddlePhiOne (y x) 1 < Real.log (X x) := by
  have hratio := (hregime.tendsto_rankinRatio_atTop hα).eventually
    (eventually_gt_atTop (6 * Real.log 4))
  have hlogy := (hregime.tendsto_log_y_atTop hα).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hratio, hlogy, hregime.eventually_two_le_y hα] with
      x hratioX hlogyX hy
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogyPos : 0 < Real.log (y x : ℝ) := by linarith
  calc
    smoothSaddlePhiOne (y x) 1 ≤
        2 * Real.log 4 * (2 + Real.log (y x)) :=
      smoothSaddlePhiOne_one_le (y x) (by omega)
    _ ≤ (6 * Real.log 4) * Real.log (y x) := by
      nlinarith [mul_nonneg hlog4 (sub_nonneg.mpr hlogyX)]
    _ < smoothRankinRatio (X x) (y x) * Real.log (y x) :=
      mul_lt_mul_of_pos_right hratioX hlogyPos
    _ = Real.log (X x) := smoothRankinRatio_mul_log hy

/-- At every fixed positive distance below `1`, the first saddle sum in the
critical regime is eventually above `log X`. -/
theorem IsTaoCriticalSmoothRegime.eventually_log_X_lt_smoothSaddlePhiOne_one_sub
    {X y : ℕ → ℕ} {α ε : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ x in atTop,
      Real.log (X x) < smoothSaddlePhiOne (y x) (1 - ε) := by
  have hc : 0 < (9 / 10 : ℝ) * Real.log 2 := by positivity
  have hgrowth :=
    hregime.eventually_rankinRatio_mul_log_sq_lt_mul_rpow hα hε hc
  filter_upwards [hgrowth, hregime.eventually_primeCounting_lower hα,
    hregime.eventually_two_le_y hα] with x hgrowthX hprimeCount hy
  have hyPos : (0 : ℝ) < y x := by positivity
  have hlogyPos : 0 < Real.log (y x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y x by omega))
  have hlogTwoNonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hsigma : 0 < (1 : ℝ) - ε := sub_pos.mpr hεOne
  have hsigmaPowPos : 0 < (y x : ℝ) ^ (1 - ε) :=
    Real.rpow_pos_of_pos hyPos _
  have hlogUpper :
      Real.log (X x) <
        (Nat.primeCounting (y x) : ℝ) * Real.log 2 /
          (y x : ℝ) ^ (1 - ε) := by
    rw [lt_div_iff₀ hsigmaPowPos]
    have hratioDiv :
        smoothRankinRatio (X x) (y x) * Real.log (y x) <
          ((9 / 10 : ℝ) * Real.log 2 * (y x : ℝ) ^ ε) /
            Real.log (y x) := by
      rw [lt_div_iff₀ hlogyPos]
      simpa [pow_two, mul_assoc] using hgrowthX
    rw [← smoothRankinRatio_mul_log hy]
    calc
      (smoothRankinRatio (X x) (y x) * Real.log (y x)) *
          (y x : ℝ) ^ (1 - ε) <
        (((9 / 10 : ℝ) * Real.log 2 * (y x : ℝ) ^ ε) /
          Real.log (y x)) * (y x : ℝ) ^ (1 - ε) :=
        mul_lt_mul_of_pos_right hratioDiv hsigmaPowPos
      _ = ((9 / 10 : ℝ) * (y x : ℝ) / Real.log (y x)) *
          Real.log 2 := by
        have hpows : (y x : ℝ) ^ ε * (y x : ℝ) ^ (1 - ε) =
            (y x : ℝ) := by
          rw [← Real.rpow_add hyPos]
          convert Real.rpow_one (y x : ℝ) using 2
          ring
        rw [div_mul_eq_mul_div]
        calc
          (9 / 10 : ℝ) * Real.log 2 * (y x : ℝ) ^ ε *
                (y x : ℝ) ^ (1 - ε) / Real.log (y x) =
              ((9 / 10 : ℝ) * Real.log 2) *
                ((y x : ℝ) ^ ε * (y x : ℝ) ^ (1 - ε)) /
                  Real.log (y x) := by ring
          _ = ((9 / 10 : ℝ) * (y x : ℝ) / Real.log (y x)) *
              Real.log 2 := by rw [hpows]; ring
      _ ≤ (Nat.primeCounting (y x) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hprimeCount hlogTwoNonneg
  have hphiLower :=
    primeCounting_mul_log_two_div_rpow_le_smoothSaddlePhiOne
      (y := y x) hsigma
  exact hlogUpper.trans_le (by
    simpa [div_eq_mul_inv, mul_assoc] using hphiLower)

/-- The exact critical saddle is eventually strictly below `1`. -/
theorem IsTaoCriticalSmoothRegime.eventually_smoothSaddlePoint_lt_one
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    ∀ᶠ x in atTop, smoothSaddlePoint (X x) (y x) < 1 := by
  filter_upwards [hregime.eventually_smoothSaddlePhiOne_one_lt_log_X hα,
    hregime.eventually_two_le_X, hregime.eventually_two_le_y hα] with
      x hphi hX hy
  apply lt_of_not_ge
  intro hsaddle
  have hmono := (smoothSaddlePhiOne_strictAntiOn hy).antitoneOn
    (show (0 : ℝ) < 1 by norm_num)
    (smoothSaddlePoint_pos hX hy) hsaddle
  rw [smoothSaddlePhiOne_smoothSaddlePoint hX hy] at hmono
  exact (not_le_of_gt hphi) hmono

/-- The exact critical saddle is eventually above `1 - ε` for every
`ε > 0`. -/
theorem IsTaoCriticalSmoothRegime.eventually_one_sub_lt_smoothSaddlePoint
    {X y : ℕ → ℕ} {α ε : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε) :
    ∀ᶠ x in atTop, 1 - ε < smoothSaddlePoint (X x) (y x) := by
  by_cases hεOne : ε < 1
  · filter_upwards [
      hregime.eventually_log_X_lt_smoothSaddlePhiOne_one_sub hα hε hεOne,
      hregime.eventually_two_le_X, hregime.eventually_two_le_y hα] with
        x hphi hX hy
    apply lt_of_not_ge
    intro hsaddle
    have hmono := (smoothSaddlePhiOne_strictAntiOn hy).antitoneOn
      (smoothSaddlePoint_pos hX hy) (sub_pos.mpr hεOne) hsaddle
    rw [smoothSaddlePhiOne_smoothSaddlePoint hX hy] at hmono
    exact (not_le_of_gt hphi) hmono
  · filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with x hX hy
    exact lt_of_le_of_lt (by linarith)
      (smoothSaddlePoint_pos hX hy)

/-- In every Tao critical smooth-number regime, the genuine finite-prime
saddle parameter tends to `1`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddlePoint_one
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    Tendsto (fun x => smoothSaddlePoint (X x) (y x)) atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hε : 0 < (1 : ℝ) - a := sub_pos.mpr ha
    simpa only [sub_sub_cancel] using
      hregime.eventually_one_sub_lt_smoothSaddlePoint hα hε
  · intro b hb
    filter_upwards [hregime.eventually_smoothSaddlePoint_lt_one hα] with
      x hx
    exact hx.trans hb

/-- The curvature at the exact critical saddle diverges.  The lower bound is
already `log 2 * log X`, directly from the saddle equation. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddlePhiTwo_saddle_atTop
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    Tendsto (fun x =>
      smoothSaddlePhiTwo (y x) (smoothSaddlePoint (X x) (y x)))
      atTop atTop := by
  have hlower : Tendsto (fun x => Real.log 2 * Real.log (X x))
      atTop atTop :=
    hregime.tendsto_log_X_atTop.const_mul_atTop
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with x hX hy
  exact log_two_mul_log_le_smoothSaddlePhiTwo_saddle hX hy

end

end Tao2026
