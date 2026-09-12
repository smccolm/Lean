import Tao2026.SmoothNumberCEPCoarse
import Tao2026.SmoothNumberSaddlePhase
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Multiplicative stability setup for critical smooth numbers

Granville's equation (3.24), cited in Tao's Proposition 2.1(i), compares
`Psi(cX,y)` with `Psi(X,y)` for a fixed positive real `c`.  This file fixes
the literal natural rounding convention and proves that fixed dilation
preserves the critical source regime.  It also records the exact remaining
stability conclusion as a proposition-valued contract; the contract is a
definition, not a theorem or an analytic assumption.
-/

open Filter Topology Asymptotics

namespace Tao2026

noncomputable section

/-- The literal natural cutoff corresponding to the real endpoint `cX`.
Using `Nat.floor` matches the closed interval `[1,cX]`. -/
noncomputable def taoNaturalDilation (c : ℝ) (X : ℕ) : ℕ :=
  ⌊c * (X : ℝ)⌋₊

/-- A fixed positive dilation has the expected real ratio after flooring. -/
theorem tendsto_taoNaturalDilation_div_nat
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℕ =>
      (taoNaturalDilation c X : ℝ) / (X : ℝ)) atTop (𝓝 c) := by
  have h := (tendsto_nat_floor_mul_div_atTop hc.le).comp
    tendsto_natCast_atTop_atTop
  simpa [taoNaturalDilation] using h

/-- A fixed positive dilated natural cutoff still tends to infinity. -/
theorem tendsto_taoNaturalDilation_atTop
    {c : ℝ} (hc : 0 < c) :
    Tendsto (taoNaturalDilation c) atTop atTop := by
  simpa [taoNaturalDilation] using tendsto_nat_floor_mul_atTop c hc

/-- Fixed multiplicative dilation changes the logarithm only by `o(log X)`,
with the floor convention included exactly. -/
theorem tendsto_log_taoNaturalDilation_div_log_nat
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℕ =>
      Real.log (taoNaturalDilation c X) / Real.log X) atTop (𝓝 1) := by
  have hratio := tendsto_taoNaturalDilation_div_nat hc
  have hlogRatio : Tendsto (fun X : ℕ =>
      Real.log ((taoNaturalDilation c X : ℝ) / (X : ℝ)))
      atTop (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hc.ne').tendsto.comp hratio
  have hlogNat : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun X : ℕ =>
      Real.log ((taoNaturalDilation c X : ℝ) / (X : ℝ)) /
        Real.log X) atTop (𝓝 0) :=
    hlogRatio.div_atTop hlogNat
  have hone : Tendsto (fun X : ℕ => Real.log (X : ℝ) / Real.log X)
      atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with X hX
    have hlogNe : Real.log (X : ℝ) ≠ 0 := by
      exact (Real.log_pos (by exact_mod_cast (show 1 < X by omega))).ne'
    field_simp
  have hsum := hsmall.add hone
  have hsum' : Tendsto (fun X : ℕ =>
      Real.log ((taoNaturalDilation c X : ℝ) / (X : ℝ)) /
          Real.log X + Real.log (X : ℝ) / Real.log X)
      atTop (𝓝 1) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_taoNaturalDilation_atTop hc).eventually
      (eventually_ge_atTop (1 : ℕ))] with X hX hdilated
  have hXPos : (0 : ℝ) < X := by exact_mod_cast hX
  have hdilatedPos : (0 : ℝ) < taoNaturalDilation c X := by
    exact_mod_cast hdilated
  rw [Real.log_div hdilatedPos.ne' hXPos.ne']
  ring

/-- A fixed positive dilation changes the logarithm by `log c`, including
the literal floor convention. -/
theorem tendsto_log_taoNaturalDilation_sub_log_nat
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℕ =>
      Real.log (taoNaturalDilation c X) - Real.log X)
      atTop (𝓝 (Real.log c)) := by
  have hlogRatio : Tendsto (fun X : ℕ =>
      Real.log ((taoNaturalDilation c X : ℝ) / (X : ℝ)))
      atTop (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hc.ne').tendsto.comp
      (tendsto_taoNaturalDilation_div_nat hc)
  apply hlogRatio.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_taoNaturalDilation_atTop hc).eventually
      (eventually_ge_atTop (1 : ℕ))] with X hX hdilated
  have hXPos : (0 : ℝ) < X := by exact_mod_cast hX
  have hdilatedPos : (0 : ℝ) < taoNaturalDilation c X := by
    exact_mod_cast hdilated
  rw [Real.log_div hdilatedPos.ne' hXPos.ne']

/-- The ambient natural cutoff in every critical source regime tends to
infinity. -/
theorem IsTaoCriticalSmoothRegime.tendsto_X_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) :
    Tendsto X atTop atTop := by
  have hlogX := hregime.tendsto_log_X_atTop
  have hXreal : Tendsto (fun n => (X n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlogX
    filter_upwards with n
    exact Real.log_le_self (Nat.cast_nonneg _)
  exact tendsto_natCast_atTop_iff.mp hXreal

/-- In a critical regime, `log y / log X = 1/u` tends to zero. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_y_div_log_X_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => Real.log (y n) / Real.log (X n))
      atTop (𝓝 0) := by
  have hinv := (hregime.tendsto_rankinRatio_atTop hα).inv_tendsto_atTop
  apply hinv.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  have hlogX : Real.log (X n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < X n by omega))).ne'
  have hlogy : Real.log (y n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < y n by omega))).ne'
  change (smoothRankinRatio (X n) (y n))⁻¹ =
    Real.log (y n) / Real.log (X n)
  rw [smoothRankinRatio]
  field_simp

/-- Fixed positive dilation of the ambient cutoff preserves both logarithmic
ratios in the critical smooth-number regime. -/
theorem IsTaoCriticalSmoothRegime.naturalDilation
    {X y : ℕ → ℕ} {α c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hc : 0 < c) :
    IsTaoCriticalSmoothRegime (fun n => taoNaturalDilation c (X n)) y α := by
  refine ⟨?_, hregime.2⟩
  have hrelative :=
    (tendsto_log_taoNaturalDilation_div_log_nat hc).comp hregime.tendsto_X_atTop
  have hproduct := hrelative.mul hregime.1
  have hproduct' : Tendsto (fun n =>
      (Real.log (taoNaturalDilation c (X n)) / Real.log (X n)) *
        (Real.log (X n) / Real.log n)) atTop (𝓝 1) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [hregime.tendsto_log_X_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))] with n hlogX hlogn
  field_simp [hlogX.ne', hlogn.ne']

/-- The exact saddle remains asymptotic to `1` after a fixed positive
dilation of the ambient cutoff. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddlePoint_naturalDilation
    {X y : ℕ → ℕ} {α c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hc : 0 < c) :
    Tendsto (fun n =>
      smoothSaddlePoint (taoNaturalDilation c (X n)) (y n))
      atTop (𝓝 1) :=
  (hregime.naturalDilation hc).tendsto_smoothSaddlePoint_one hα

/-- Fixed positive dilation changes the exact saddle by `o(1)`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddlePoint_naturalDilation_sub
    {X y : ℕ → ℕ} {α c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hc : 0 < c) :
    Tendsto (fun n =>
      smoothSaddlePoint (taoNaturalDilation c (X n)) (y n) -
        smoothSaddlePoint (X n) (y n)) atTop (𝓝 0) := by
  simpa using
    (hregime.tendsto_smoothSaddlePoint_naturalDilation hα hc).sub
      (hregime.tendsto_smoothSaddlePoint_one hα)

/-- On the prime scale, the saddle displacement under fixed dilation is
uniformly negligible. -/
theorem IsTaoCriticalSmoothRegime.tendsto_abs_smoothSaddlePoint_dilation_sub_mul_log_y
    {X y : ℕ → ℕ} {α c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hc : 0 < c) :
    Tendsto (fun n =>
      |smoothSaddlePoint (taoNaturalDilation c (X n)) (y n) -
        smoothSaddlePoint (X n) (y n)| * Real.log (y n))
      atTop (𝓝 0) := by
  rcases lt_trichotomy c 1 with hcOne | hcOne | hcOne
  · have hstrict : ∀ᶠ n in atTop, taoNaturalDilation c (X n) < X n := by
      have hratio := ((tendsto_taoNaturalDilation_div_nat hc).comp
        hregime.tendsto_X_atTop).eventually (Iio_mem_nhds hcOne)
      filter_upwards [hratio, hregime.eventually_two_le_X] with n hn hX
      have hXPos : (0 : ℝ) < X n := by positivity
      have hcast : (taoNaturalDilation c (X n) : ℝ) < X n :=
        (div_lt_one hXPos).mp hn
      exact_mod_cast hcast
    have hdlog := ((tendsto_log_taoNaturalDilation_sub_log_nat hc).comp
      hregime.tendsto_X_atTop).abs
    have hupperRaw := (hdlog.div_const (Real.log 2)).mul
      ((hregime.naturalDilation hc).tendsto_log_y_div_log_X_zero hα)
    have hupper : Tendsto (fun n =>
        |Real.log (taoNaturalDilation c (X n)) - Real.log (X n)| /
            Real.log 2 *
          (Real.log (y n) / Real.log (taoNaturalDilation c (X n))))
        atTop (𝓝 0) := by
      simpa using hupperRaw
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [hregime.eventually_two_le_y hα] with n hy
      exact mul_nonneg (abs_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y n by omega)))
    · filter_upwards [hstrict, hregime.eventually_two_le_X,
        (hregime.naturalDilation hc).eventually_two_le_X,
        hregime.eventually_two_le_y hα] with n hDX hX hD hy
      have hsaddle := smoothSaddlePoint_strictAnti_left hD hDX hy
      have hbound := smoothSaddlePoint_sub_le_log_sub_div hD hDX hy
      have hlogDPos : 0 < Real.log (taoNaturalDilation c (X n) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < taoNaturalDilation c (X n) by omega))
      have hlogyNonneg : 0 ≤ Real.log (y n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ y n by omega))
      have hDRealPos : (0 : ℝ) < taoNaturalDilation c (X n) := by
        exact_mod_cast (show 0 < taoNaturalDilation c (X n) by omega)
      have hXRealPos : (0 : ℝ) < X n := by
        exact_mod_cast (show 0 < X n by omega)
      have hlogDX : Real.log (taoNaturalDilation c (X n) : ℝ) <
          Real.log (X n : ℝ) :=
        Real.strictMonoOn_log hDRealPos hXRealPos (by exact_mod_cast hDX)
      have hdlogNeg : Real.log (taoNaturalDilation c (X n) : ℝ) -
          Real.log (X n : ℝ) < 0 := sub_neg.mpr hlogDX
      rw [abs_of_pos (sub_pos.mpr hsaddle), abs_of_neg hdlogNeg]
      calc
        (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n) -
            smoothSaddlePoint (X n) (y n)) * Real.log (y n) ≤
          ((Real.log (X n) - Real.log (taoNaturalDilation c (X n))) /
            (Real.log 2 * Real.log (taoNaturalDilation c (X n)))) *
              Real.log (y n) :=
          mul_le_mul_of_nonneg_right hbound hlogyNonneg
        _ = (-(Real.log (taoNaturalDilation c (X n)) - Real.log (X n)) /
            Real.log 2) *
              (Real.log (y n) /
                Real.log (taoNaturalDilation c (X n))) := by
          field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
            hlogDPos.ne']
          ring
  · subst c
    simp [taoNaturalDilation]
  · have hstrict : ∀ᶠ n in atTop, X n < taoNaturalDilation c (X n) := by
      have hratio := ((tendsto_taoNaturalDilation_div_nat hc).comp
        hregime.tendsto_X_atTop).eventually (Ioi_mem_nhds hcOne)
      filter_upwards [hratio, hregime.eventually_two_le_X] with n hn hX
      have hXPos : (0 : ℝ) < X n := by positivity
      have hcast : (X n : ℝ) < taoNaturalDilation c (X n) :=
        (one_lt_div hXPos).mp hn
      exact_mod_cast hcast
    have hdlog := ((tendsto_log_taoNaturalDilation_sub_log_nat hc).comp
      hregime.tendsto_X_atTop).abs
    have hupperRaw := (hdlog.div_const (Real.log 2)).mul
      (hregime.tendsto_log_y_div_log_X_zero hα)
    have hupper : Tendsto (fun n =>
        |Real.log (taoNaturalDilation c (X n)) - Real.log (X n)| /
            Real.log 2 *
          (Real.log (y n) / Real.log (X n))) atTop (𝓝 0) := by
      simpa using hupperRaw
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [hregime.eventually_two_le_y hα] with n hy
      exact mul_nonneg (abs_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y n by omega)))
    · filter_upwards [hstrict, hregime.eventually_two_le_X,
        hregime.eventually_two_le_y hα] with n hXD hX hy
      have hsaddle := smoothSaddlePoint_strictAnti_left hX hXD hy
      have hbound := smoothSaddlePoint_sub_le_log_sub_div hX hXD hy
      have hlogXPos : 0 < Real.log (X n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < X n by omega))
      have hlogyNonneg : 0 ≤ Real.log (y n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ y n by omega))
      have hXRealPos : (0 : ℝ) < X n := by
        exact_mod_cast (show 0 < X n by omega)
      have hDRealPos : (0 : ℝ) < taoNaturalDilation c (X n) := by
        exact_mod_cast (show 0 < taoNaturalDilation c (X n) by omega)
      have hlogXD : Real.log (X n : ℝ) <
          Real.log (taoNaturalDilation c (X n) : ℝ) :=
        Real.strictMonoOn_log hXRealPos hDRealPos (by exact_mod_cast hXD)
      have hdlogPos : 0 < Real.log (taoNaturalDilation c (X n) : ℝ) -
          Real.log (X n : ℝ) := sub_pos.mpr hlogXD
      rw [abs_of_neg (sub_neg.mpr hsaddle), abs_of_pos hdlogPos]
      simp only [neg_sub]
      calc
        (smoothSaddlePoint (X n) (y n) -
            smoothSaddlePoint (taoNaturalDilation c (X n)) (y n)) *
              Real.log (y n) ≤
          ((Real.log (taoNaturalDilation c (X n)) - Real.log (X n)) /
            (Real.log 2 * Real.log (X n))) * Real.log (y n) :=
          mul_le_mul_of_nonneg_right hbound hlogyNonneg
        _ = ((Real.log (taoNaturalDilation c (X n)) - Real.log (X n)) /
            Real.log 2) * (Real.log (y n) / Real.log (X n)) := by
          field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
            hlogXPos.ne']

/-- The minimized logarithmic saddle phase changes by `log c` under fixed
positive dilation. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddlePhase_naturalDilation_sub
    {X y : ℕ → ℕ} {α c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hc : 0 < c) :
    Tendsto (fun n =>
      smoothSaddlePhase (taoNaturalDilation c (X n)) (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n)) -
        smoothSaddlePhase (X n) (y n)
          (smoothSaddlePoint (X n) (y n)))
      atTop (𝓝 (Real.log c)) := by
  have hdlog :=
    (tendsto_log_taoNaturalDilation_sub_log_nat hc).comp
      hregime.tendsto_X_atTop
  have hlower :=
    (hregime.tendsto_smoothSaddlePoint_naturalDilation hα hc).mul hdlog
  have hupper := (hregime.tendsto_smoothSaddlePoint_one hα).mul hdlog
  have hresult : Tendsto (fun n =>
      smoothSaddlePhase (taoNaturalDilation c (X n)) (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n)) -
        smoothSaddlePhase (X n) (y n)
          (smoothSaddlePoint (X n) (y n)))
      atTop (𝓝 (1 * Real.log c)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    · filter_upwards [hregime.eventually_two_le_X,
        (hregime.naturalDilation hc).eventually_two_le_X,
        hregime.eventually_two_le_y hα] with n hX hdilated hy
      exact smoothSaddlePoint_mul_log_sub_le_phase_saddle_sub
        hX hdilated hy
    · filter_upwards [hregime.eventually_two_le_X,
        (hregime.naturalDilation hc).eventually_two_le_X,
        hregime.eventually_two_le_y hα] with n hX hdilated hy
      exact phase_saddle_sub_le_smoothSaddlePoint_mul_log_sub
        hX hdilated hy
  simpa using hresult

/-- Consequently, the exponential parts of the two saddle main terms have
quotient tending to the dilation factor `c`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_exp_smoothSaddlePhase_ratio
    {X y : ℕ → ℕ} {α c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hc : 0 < c) :
    Tendsto (fun n =>
      Real.exp (smoothSaddlePhase (taoNaturalDilation c (X n)) (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n))) /
        Real.exp (smoothSaddlePhase (X n) (y n)
          (smoothSaddlePoint (X n) (y n))))
      atTop (𝓝 c) := by
  have hphase := (Real.continuous_exp.tendsto _).comp
    (hregime.tendsto_smoothSaddlePhase_naturalDilation_sub hα hc)
  convert hphase using 1
  · funext n
    simp only [Function.comp_apply]
    rw [Real.exp_sub]
  · rw [Real.exp_log hc]

/-- Monotonicity of the exact smooth-number count in its ambient cutoff. -/
theorem psiNat_mono_left {X Y y : ℕ} (hXY : X ≤ Y) :
    psiNat X y ≤ psiNat Y y := by
  apply Finset.card_le_card
  intro n hn
  rw [mem_smoothNumbersUpTo_source] at hn ⊢
  exact ⟨hn.1.trans hXY, hn.2⟩

/-- Dilation by a factor at most one decreases the floored cutoff. -/
theorem taoNaturalDilation_le_self
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (X : ℕ) :
    taoNaturalDilation c X ≤ X := by
  have hfloor : (taoNaturalDilation c X : ℝ) ≤ c * X := by
    exact Nat.floor_le (mul_nonneg hc0 (Nat.cast_nonneg _))
  have hmul : c * (X : ℝ) ≤ (X : ℝ) := by
    exact mul_le_of_le_one_left (Nat.cast_nonneg X) hc1
  exact_mod_cast hfloor.trans hmul

/-- Dilation by a factor at least one increases the floored cutoff. -/
theorem self_le_taoNaturalDilation
    {c : ℝ} (hc1 : 1 ≤ c) (X : ℕ) :
    X ≤ taoNaturalDilation c X := by
  rw [taoNaturalDilation, Nat.le_floor_iff (mul_nonneg (by linarith)
    (Nat.cast_nonneg _))]
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg X))

/-- The easy direction of smooth-number stability when `0 < c ≤ 1`. -/
theorem psiNat_naturalDilation_le_of_le_one
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (X y : ℕ) :
    psiNat (taoNaturalDilation c X) y ≤ psiNat X y :=
  psiNat_mono_left (taoNaturalDilation_le_self hc0 hc1 X)

/-- The easy direction of smooth-number stability when `1 ≤ c`. -/
theorem psiNat_le_naturalDilation_of_one_le
    {c : ℝ} (hc1 : 1 ≤ c) (X y : ℕ) :
    psiNat X y ≤ psiNat (taoNaturalDilation c X) y :=
  psiNat_mono_left (self_le_taoNaturalDilation hc1 X)

/-- A positive limit for a quotient of eventually nonnegative functions
gives two-sided Landau comparability. -/
theorem isTheta_of_tendsto_div_pos
    {f g : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hfg : ∀ᶠ n in atTop, 0 ≤ f n ∧ 0 < g n)
    (hlim : Tendsto (fun n => f n / g n) atTop (𝓝 c)) :
    f =Θ[atTop] g := by
  constructor
  · refine IsBigO.of_bound (2 * c) ?_
    have hupper : ∀ᶠ n in atTop, f n / g n < 2 * c :=
      hlim.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hfg, hupper] with n hn hratio
    rw [Real.norm_of_nonneg hn.1, Real.norm_of_nonneg hn.2.le]
    exact ((div_lt_iff₀ hn.2).mp hratio).le
  · refine IsBigO.of_bound (2 / c) ?_
    have hlower : ∀ᶠ n in atTop, c / 2 < f n / g n :=
      hlim.eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [hfg, hlower] with n hn hratio
    rw [Real.norm_of_nonneg hn.2.le, Real.norm_of_nonneg hn.1]
    have hmul : c / 2 * g n < f n := (lt_div_iff₀ hn.2).mp hratio
    have hcne : c ≠ 0 := hc.ne'
    calc
      g n = (2 / c) * (c / 2 * g n) := by field_simp
      _ ≤ (2 / c) * f n := by
        exact mul_le_mul_of_nonneg_left hmul.le (by positivity)

/-- Limit form of Granville's equation (3.24) in every critical source
regime.  Since the saddle parameter tends to one, the cited formula predicts
the quotient limit `c`.  This is the sharp analytic target behind the weaker
`IsTheta` contract below; it is a definition, not an assumed theorem. -/
def TaoCriticalSmoothDilationLimitConclusion : Prop :=
  ∀ (c α : ℝ) (X y : ℕ → ℕ), 0 < c → 0 < α →
    IsTaoCriticalSmoothRegime X y α →
      Tendsto (fun n =>
        (psiNat (taoNaturalDilation c (X n)) (y n) : ℝ) /
          (psiNat (X n) (y n) : ℝ)) atTop (𝓝 c)

/-- Exact source-facing conclusion of the dilation clause in Proposition
2.1(i), with the real cutoff rounded down to a natural. This declaration is a
definition of the remaining analytic target, not an assumed theorem. -/
def TaoCriticalSmoothDilationStabilityConclusion : Prop :=
  ∀ (c α : ℝ) (X y : ℕ → ℕ), 0 < c → 0 < α →
    IsTaoCriticalSmoothRegime X y α →
      (fun n => (psiNat (taoNaturalDilation c (X n)) (y n) : ℝ)) =Θ[atTop]
        fun n => (psiNat (X n) (y n) : ℝ)

/-- Granville's quotient-limit formula implies the exact comparability
clause in Tao's Proposition 2.1(i). -/
theorem criticalSmoothDilationStability_of_limit
    (hlimit : TaoCriticalSmoothDilationLimitConclusion) :
    TaoCriticalSmoothDilationStabilityConclusion := by
  intro c α X y hc hα hregime
  apply isTheta_of_tendsto_div_pos hc
  · filter_upwards [hregime.eventually_two_le_X] with n hX
    exact ⟨Nat.cast_nonneg _, by
      exact_mod_cast one_le_psiNat (le_trans (by omega : 1 ≤ 2) hX)⟩
  · exact hlimit c α X y hc hα hregime

end

end Tao2026
