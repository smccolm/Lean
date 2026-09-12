import Tao2026.SmoothNumberPolylogRegimes
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.PNat.Factors
import Mathlib.Data.Sym.Card

/-!
# Finite lower bounds for smooth numbers

This module begins the lower half of Proposition 2.1 with Granville's exact
finite exponent-lattice construction.  It includes both the squarefree
subfamily and the full simplex of prime multisets of total degree at most
`k`; unique factorization makes their product maps injective, while stars and
bars gives the latter family the exact cardinality
`choose (k + π(y)) (π(y))`.
-/

namespace Tao2026

open scoped BigOperators
open Filter Topology

noncomputable section

/-- The maximal number of factors at most `y` whose product is forced below
`X`.  This integer depth is the finite lattice counterpart of the real
Rankin ratio `log X / log y`. -/
def smoothLowerDepth (X y : ℕ) : ℕ := Nat.log y X

theorem pow_smoothLowerDepth_le
    {X y : ℕ} (hX : X ≠ 0) :
    y ^ smoothLowerDepth X y ≤ X := by
  exact Nat.pow_log_le_self y hX

/-- The integer lattice depth lies below the real Rankin ratio. -/
theorem smoothLowerDepth_cast_le_rankinRatio
    {X y : ℕ} (hX : X ≠ 0) (hy : 2 ≤ y) :
    (smoothLowerDepth X y : ℝ) ≤ smoothRankinRatio X y := by
  have hpower : y ^ smoothLowerDepth X y ≤ X :=
    pow_smoothLowerDepth_le hX
  have hyPos : (0 : ℝ) < y := by positivity
  have hpowPos : (0 : ℝ) < (y : ℝ) ^ smoothLowerDepth X y := by positivity
  have hcastPower : ((y ^ smoothLowerDepth X y : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hpower
  simp only [Nat.cast_pow] at hcastPower
  have hlog := Real.log_le_log hpowPos hcastPower
  rw [Real.log_pow] at hlog
  rw [smoothRankinRatio, le_div_iff₀ (Real.log_pos (by exact_mod_cast hy))]
  simpa [mul_comm] using hlog

/-- The real Rankin ratio lies strictly below one more than the integer
lattice depth. -/
theorem rankinRatio_lt_smoothLowerDepth_cast_add_one
    (X : ℕ) {y : ℕ} (hy : 2 ≤ y) :
    smoothRankinRatio X y < (smoothLowerDepth X y : ℝ) + 1 := by
  by_cases hX : X = 0
  · simp [hX, smoothRankinRatio, smoothLowerDepth]
  have hpower : X < y ^ (smoothLowerDepth X y).succ := by
    exact Nat.lt_pow_succ_log_self (by omega) X
  have hXPos : (0 : ℝ) < X := by positivity
  have hpowPos : (0 : ℝ) < (y : ℝ) ^ (smoothLowerDepth X y).succ := by
    positivity
  have hcastPower : (X : ℝ) < ((y ^ (smoothLowerDepth X y).succ : ℕ) : ℝ) := by
    exact_mod_cast hpower
  simp only [Nat.cast_pow] at hcastPower
  have hlog := Real.strictMonoOn_log hXPos hpowPos hcastPower
  rw [Real.log_pow] at hlog
  rw [smoothRankinRatio, div_lt_iff₀ (Real.log_pos (by exact_mod_cast hy))]
  push_cast at hlog
  simpa [mul_add] using hlog

/-- The exact integral lattice depth has the same normalized limit as the
real Rankin ratio; the rounding error is at most one. -/
theorem IsTaoPolylogSmoothRegime.tendsto_smoothLowerDepth_div_taoPolylogUZero
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => (smoothLowerDepth (X x) (y x) : ℝ) /
      taoPolylogUZero x) atTop (𝓝 (1 / A)) := by
  have hinv : Tendsto (fun x : ℕ => 1 / taoPolylogUZero x)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_taoPolylogUZero_atTop
  have herror : Tendsto (fun x =>
      (smoothRankinRatio (X x) (y x) -
        (smoothLowerDepth (X x) (y x) : ℝ)) / taoPolylogUZero x)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun x : ℕ => 1 / taoPolylogUZero x)
    · filter_upwards [hregime.eventually_two_le_X,
        hregime.eventually_two_le_y hA,
        tendsto_taoPolylogUZero_atTop.eventually
          (eventually_gt_atTop (0 : ℝ))] with x hX hy huPos
      exact div_nonneg
        (sub_nonneg.mpr (smoothLowerDepth_cast_le_rankinRatio
          (by omega) hy)) huPos.le
    · filter_upwards [hregime.eventually_two_le_y hA,
        tendsto_taoPolylogUZero_atTop.eventually
          (eventually_gt_atTop (0 : ℝ))] with x hy huPos
      exact div_le_div_of_nonneg_right (by
        have hround := rankinRatio_lt_smoothLowerDepth_cast_add_one (X x) hy
        linarith) huPos.le
    · exact hinv
  have hlimit :=
    (hregime.tendsto_rankinRatio_div_taoPolylogUZero hA).sub herror
  have hlimit' : Tendsto (fun x =>
      smoothRankinRatio (X x) (y x) / taoPolylogUZero x -
        (smoothRankinRatio (X x) (y x) -
          (smoothLowerDepth (X x) (y x) : ℝ)) / taoPolylogUZero x)
      atTop (𝓝 (1 / A)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with x
  ring

/-- In the critical regime the same exact integral depth inherits the natural
`u₀/α` scale from the real Rankin ratio. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothLowerDepth_div_taoUZero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => (smoothLowerDepth (X x) (y x) : ℝ) /
      taoUZero x) atTop (𝓝 (1 / α)) := by
  have hinv : Tendsto (fun x : ℕ => 1 / taoUZero x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_taoUZero_atTop
  have herror : Tendsto (fun x =>
      (smoothRankinRatio (X x) (y x) -
        (smoothLowerDepth (X x) (y x) : ℝ)) / taoUZero x)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun x : ℕ => 1 / taoUZero x)
    · filter_upwards [hregime.eventually_two_le_X,
        hregime.eventually_two_le_y hα,
        tendsto_taoUZero_atTop.eventually
          (eventually_gt_atTop (0 : ℝ))] with x hX hy huPos
      exact div_nonneg
        (sub_nonneg.mpr (smoothLowerDepth_cast_le_rankinRatio
          (by omega) hy)) huPos.le
    · filter_upwards [hregime.eventually_two_le_y hα,
        tendsto_taoUZero_atTop.eventually
          (eventually_gt_atTop (0 : ℝ))] with x hy huPos
      exact div_le_div_of_nonneg_right (by
        have hround := rankinRatio_lt_smoothLowerDepth_cast_add_one (X x) hy
        linarith) huPos.le
    · exact hinv
  have hlimit := (hregime.tendsto_rankinRatio_div_taoUZero hα).sub herror
  have hlimit' : Tendsto (fun x =>
      smoothRankinRatio (X x) (y x) / taoUZero x -
        (smoothRankinRatio (X x) (y x) -
          (smoothLowerDepth (X x) (y x) : ℝ)) / taoUZero x)
      atTop (𝓝 (1 / α)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with x
  ring

/-- The logarithm of the critical integral depth is asymptotic to half of
`log₂ x`, exactly as for `u₀`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_smoothLowerDepth_div_iteratedLog
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
      iteratedLog x) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hnormalized := hregime.tendsto_smoothLowerDepth_div_taoUZero hα
  have hlogNormalized : Tendsto (fun x =>
      Real.log ((smoothLowerDepth (X x) (y x) : ℝ) / taoUZero x))
      atTop (𝓝 (Real.log (1 / α))) :=
    (Real.continuousAt_log (one_div_ne_zero hα.ne')).tendsto.comp hnormalized
  have hcorrection := hlogNormalized.div_atTop tendsto_iteratedLog_atTop
  have hsum := hcorrection.add tendsto_log_taoUZero_div_iteratedLog
  have hsumHalf : Tendsto (fun x =>
      Real.log ((smoothLowerDepth (X x) (y x) : ℝ) / taoUZero x) /
          iteratedLog x +
        Real.log (taoUZero x) / iteratedLog x) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using hsum
  apply hsumHalf.congr'
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds (one_div_pos.mpr hα)),
    tendsto_taoUZero_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hnormPos huPos
  have hproduct :
      ((smoothLowerDepth (X x) (y x) : ℝ) / taoUZero x) * taoUZero x =
        (smoothLowerDepth (X x) (y x) : ℝ) := by
    field_simp [huPos.ne']
  have hlogProduct :
      Real.log (smoothLowerDepth (X x) (y x) : ℝ) =
        Real.log ((smoothLowerDepth (X x) (y x) : ℝ) / taoUZero x) +
          Real.log (taoUZero x) := by
    conv_lhs => rw [← hproduct]
    rw [Real.log_mul hnormPos.ne' huPos.ne']
  rw [hlogProduct]
  ring

/-- The exact integral depth has the same critical Dickman saving
`(1/α) log z` as the real Rankin ratio. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothLowerDepth_mul_log_div_log_taoZ
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x =>
      (smoothLowerDepth (X x) (y x) : ℝ) *
          Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
        Real.log (taoZ x)) atTop (𝓝 (1 / α)) := by
  have hlogRatio :=
    (hregime.tendsto_log_smoothLowerDepth_div_iteratedLog hα).div
      tendsto_log_taoUZero_div_iteratedLog (by norm_num)
  have hlogRatio' : Tendsto
      ((fun x => Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
          iteratedLog x) /
        (fun x => Real.log (taoUZero x) / iteratedLog x))
      atTop (𝓝 1) := by
    simpa using hlogRatio
  have hlogRatioOne : Tendsto (fun x =>
      Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
        Real.log (taoUZero x)) atTop (𝓝 1) := by
    apply hlogRatio'.congr'
    filter_upwards [tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
      tendsto_taoUZero_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hiterPos huOne
    change
      (Real.log (smoothLowerDepth (X x) (y x) : ℝ) / iteratedLog x) /
          (Real.log (taoUZero x) / iteratedLog x) =
        Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
          Real.log (taoUZero x)
    field_simp [hiterPos.ne', (Real.log_pos huOne).ne']
  have hproduct :=
    (hregime.tendsto_smoothLowerDepth_div_taoUZero hα).mul
      tendsto_taoUZero_mul_log_div_log_taoZ_one |>.mul hlogRatioOne
  have hproduct' : Tendsto (fun x =>
      ((smoothLowerDepth (X x) (y x) : ℝ) / taoUZero x) *
        (taoUZero x * Real.log (taoUZero x) / Real.log (taoZ x)) *
        (Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
          Real.log (taoUZero x))) atTop (𝓝 (1 / α)) := by
    convert hproduct using 1
    all_goals field_simp [hα.ne']
  apply hproduct'.congr'
  filter_upwards [tendsto_taoUZero_atTop.eventually
      (eventually_gt_atTop (1 : ℝ)),
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x huOne hzOne
  field_simp [huOne.ne', (Real.log_pos huOne).ne',
    (Real.log_pos hzOne).ne']

/-- A convenient eventual `0.9 H/log H` lower bound for the prime-counting
function, extracted from the frozen prime number theorem. -/
theorem eventually_nine_tenths_mul_div_le_primeCounting :
    ∀ᶠ H : ℕ in atTop,
      (9 / 10 : ℝ) * H / Real.log H ≤ (H.primeCounting : ℝ) := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  simp only [div_one] at hc
  have hcNat : Tendsto (fun H : ℕ => c (H : ℝ)) atTop (𝓝 0) :=
    hc.comp tendsto_natCast_atTop_atTop
  have hsmall :
      ∀ᶠ H : ℕ in atTop, |c (H : ℝ)| < (1 / 10 : ℝ) := by
    simpa [Real.dist_eq] using
      (Metric.tendsto_atTop.1 hcNat (1 / 10 : ℝ) (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with H hcH hH
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast hH)
  have hcLower : (9 / 10 : ℝ) ≤ 1 + c (H : ℝ) := by
    have : -(1 / 10 : ℝ) ≤ c (H : ℝ) := by
      exact (neg_le_neg hcH.le).trans (neg_abs_le (c (H : ℝ)))
    linarith
  calc
    (9 / 10 : ℝ) * H / Real.log H ≤
        (1 + c (H : ℝ)) * H / Real.log H := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcLower (Nat.cast_nonneg H)) hlog.le
    _ = (H.primeCounting : ℝ) := by
      simpa using (hpi (H : ℝ)).symm

theorem IsTaoPolylogSmoothRegime.tendsto_y_atTop
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto y atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  have hlog := hregime.tendsto_log_y_atTop hA
  filter_upwards [hlog.eventually (eventually_ge_atTop (b : ℝ)),
    hregime.eventually_two_le_y hA] with x hx hy
  have hyPos : (0 : ℝ) < y x := by positivity
  have hlogLe : Real.log (y x : ℝ) ≤ (y x : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hyPos]
  exact_mod_cast hx.trans hlogLe

theorem IsTaoPolylogSmoothRegime.eventually_primeCounting_lower
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    ∀ᶠ x in atTop,
      (9 / 10 : ℝ) * y x / Real.log (y x) ≤
        (Nat.primeCounting (y x) : ℝ) :=
  (hregime.tendsto_y_atTop hA).eventually
    eventually_nine_tenths_mul_div_le_primeCounting

theorem IsTaoCriticalSmoothRegime.tendsto_y_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto y atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  have hlog := hregime.tendsto_log_y_atTop hα
  filter_upwards [hlog.eventually (eventually_ge_atTop (b : ℝ)),
    hregime.eventually_two_le_y hα] with x hx hy
  have hyPos : (0 : ℝ) < y x := by positivity
  have hlogLe : Real.log (y x : ℝ) ≤ (y x : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hyPos]
  exact_mod_cast hx.trans hlogLe

theorem IsTaoCriticalSmoothRegime.eventually_primeCounting_lower
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop,
      (9 / 10 : ℝ) * y x / Real.log (y x) ≤
        (Nat.primeCounting (y x) : ℝ) :=
  (hregime.tendsto_y_atTop hα).eventually
    eventually_nine_tenths_mul_div_le_primeCounting

/-- The secondary logarithm of the critical smoothness cutoff is negligible
on the `log z` scale. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_log_y_div_log_taoZ_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (Real.log (y x)) / Real.log (taoZ x))
      atTop (𝓝 0) := by
  have hnormalized := hregime.2
  have hlogNormalized : Tendsto (fun x =>
      Real.log (Real.log (y x) / Real.log (taoZ x)))
      atTop (𝓝 (Real.log α)) :=
    (Real.continuousAt_log hα.ne').tendsto.comp hnormalized
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hcorrection := hlogNormalized.div_atTop hlogZ
  have hlogLogZ : Tendsto (fun x =>
      Real.log (Real.log (taoZ x)) / Real.log (taoZ x)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogZ
  have hsum := hcorrection.add hlogLogZ
  have hsumZero : Tendsto (fun x =>
      Real.log (Real.log (y x) / Real.log (taoZ x)) /
          Real.log (taoZ x) +
        Real.log (Real.log (taoZ x)) / Real.log (taoZ x))
      atTop (𝓝 0) := by
    simpa using hsum
  apply hsumZero.congr'
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds hα),
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hnormPos hzOne
  have hzLogPos : 0 < Real.log (taoZ x) := Real.log_pos hzOne
  have hproduct :
      (Real.log (y x) / Real.log (taoZ x)) * Real.log (taoZ x) =
        Real.log (y x) := by
    field_simp [hzLogPos.ne']
  have hlogProduct : Real.log (Real.log (y x)) =
      Real.log (Real.log (y x) / Real.log (taoZ x)) +
        Real.log (Real.log (taoZ x)) := by
    conv_lhs => rw [← hproduct]
    rw [Real.log_mul hnormPos.ne' hzLogPos.ne']
  rw [hlogProduct]
  ring

/-- PNT specialization: the critical prime lattice has logarithmic size
`α log z`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_primeCounting_div_log_taoZ
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (Nat.primeCounting (y x) : ℝ) /
      Real.log (taoZ x)) atTop (𝓝 α) := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  simp only [div_one] at hc
  have hyCastTop : Tendsto (fun x => (y x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hregime.tendsto_y_atTop hα)
  have hcY : Tendsto (fun x => c (y x : ℝ)) atTop (𝓝 0) :=
    hc.comp hyCastTop
  have hcoefficient : Tendsto (fun x => 1 + c (y x : ℝ))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hcY
  have hlogCoefficient : Tendsto (fun x =>
      Real.log (1 + c (y x : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.continuousAt_log one_ne_zero).tendsto.comp hcoefficient
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hcoefficientTerm : Tendsto (fun x =>
      Real.log (1 + c (y x : ℝ)) / Real.log (taoZ x)) atTop (𝓝 0) :=
    hlogCoefficient.div_atTop hlogZ
  have hsum :=
    (hcoefficientTerm.add hregime.2).sub
      (hregime.tendsto_log_log_y_div_log_taoZ_zero hα)
  have hsumAlpha : Tendsto (fun x =>
      Real.log (1 + c (y x : ℝ)) / Real.log (taoZ x) +
          Real.log (y x) / Real.log (taoZ x) -
        Real.log (Real.log (y x)) / Real.log (taoZ x))
      atTop (𝓝 α) := by
    simpa using hsum
  apply hsumAlpha.congr'
  filter_upwards [hcoefficient.eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hregime.eventually_two_le_y hα] with x hcoeffPos hy
  have hyPos : (0 : ℝ) < y x := by positivity
  have hyLogPos : 0 < Real.log (y x : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hpiAt : (Nat.primeCounting (y x) : ℝ) =
      (1 + c (y x : ℝ)) * (y x : ℝ) / Real.log (y x : ℝ) := by
    simpa using hpi (y x : ℝ)
  rw [hpiAt, Real.log_div (mul_ne_zero hcoeffPos.ne' hyPos.ne')
    hyLogPos.ne', Real.log_mul hcoeffPos.ne' hyPos.ne']
  ring

theorem IsTaoCriticalSmoothRegime.tendsto_smoothLowerDepth_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => smoothLowerDepth (X x) (y x)) atTop atTop := by
  have hcast : Tendsto (fun x =>
      (smoothLowerDepth (X x) (y x) : ℝ)) atTop atTop := by
    have hproduct :=
      (hregime.tendsto_smoothLowerDepth_div_taoUZero hα).pos_mul_atTop
        (one_div_pos.mpr hα) tendsto_taoUZero_atTop
    apply hproduct.congr'
    filter_upwards [tendsto_taoUZero_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x huPos
    field_simp [huPos.ne']
  exact tendsto_natCast_atTop_iff.mp hcast

theorem IsTaoCriticalSmoothRegime.tendsto_log_smoothLowerDepth_div_log_taoZ_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
      Real.log (taoZ x)) atTop (𝓝 0) := by
  have hproduct :=
    (hregime.tendsto_log_smoothLowerDepth_div_iteratedLog hα).mul
      tendsto_iteratedLog_div_log_taoZ_zero
  have hzero : Tendsto (fun x =>
      (Real.log (smoothLowerDepth (X x) (y x) : ℝ) / iteratedLog x) *
        (iteratedLog x / Real.log (taoZ x))) atTop (𝓝 0) := by
    simpa using hproduct
  apply hzero.congr'
  filter_upwards [tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hiterPos hzOne
  field_simp [hiterPos.ne', (Real.log_pos hzOne).ne']

theorem IsTaoCriticalSmoothRegime.tendsto_log_primeCounting_sub_log_depth_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x =>
      Real.log (Nat.primeCounting (y x) : ℝ) -
        Real.log (smoothLowerDepth (X x) (y x) : ℝ)) atTop atTop := by
  have hnormalized :=
    (hregime.tendsto_log_primeCounting_div_log_taoZ hα).sub
      (hregime.tendsto_log_smoothLowerDepth_div_log_taoZ_zero hα)
  have hnormalized0 : Tendsto (fun x =>
      Real.log (Nat.primeCounting (y x) : ℝ) / Real.log (taoZ x) -
        Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
          Real.log (taoZ x)) atTop (𝓝 α) := by
    simpa using hnormalized
  have hnormalized' : Tendsto (fun x =>
      (Real.log (Nat.primeCounting (y x) : ℝ) -
        Real.log (smoothLowerDepth (X x) (y x) : ℝ)) /
          Real.log (taoZ x)) atTop (𝓝 α) := by
    apply hnormalized0.congr'
    filter_upwards with x
    ring
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hproduct := hnormalized'.pos_mul_atTop hα hlogZ
  apply hproduct.congr'
  filter_upwards [tendsto_taoZ_atTop.eventually
    (eventually_gt_atTop (1 : ℝ))] with x hzOne
  field_simp [(Real.log_pos hzOne).ne']

theorem IsTaoCriticalSmoothRegime.eventually_two_mul_depth_le_primeCounting
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop,
      2 * smoothLowerDepth (X x) (y x) ≤ Nat.primeCounting (y x) := by
  filter_upwards [
    (hregime.tendsto_log_primeCounting_sub_log_depth_atTop hα).eventually
      (eventually_gt_atTop (Real.log 2)),
    (hregime.tendsto_smoothLowerDepth_atTop hα).eventually
      (eventually_ge_atTop 1)] with x hmargin hk
  let k := smoothLowerDepth (X x) (y x)
  let n := Nat.primeCounting (y x)
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkLogNonneg : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  have hnLogPos : 0 < Real.log (n : ℝ) := by
    dsimp only [k, n] at hmargin ⊢
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hnPos : (0 : ℝ) < n :=
    lt_trans zero_lt_one ((Real.log_pos_iff (Nat.cast_nonneg n)).mp hnLogPos)
  have hlogMul : Real.log ((2 : ℝ) * k) =
      Real.log 2 + Real.log (k : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkPos.ne']
  have hlogLt : Real.log ((2 : ℝ) * k) < Real.log (n : ℝ) := by
    rw [hlogMul]
    dsimp only [k, n] at hmargin ⊢
    linarith
  have hrealLt : (2 : ℝ) * k < n :=
    (Real.strictMonoOn_log.lt_iff_lt (mul_pos (by norm_num) hkPos) hnPos).mp hlogLt
  exact_mod_cast hrealLt.le

/-- The logarithm of the integral lattice depth is asymptotic to `log₂ x`. -/
theorem IsTaoPolylogSmoothRegime.tendsto_log_smoothLowerDepth_div_iteratedLog_one
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => Real.log (smoothLowerDepth (X x) (y x) : ℝ) /
      iteratedLog x) atTop (𝓝 1) := by
  have hnormalized :=
    hregime.tendsto_smoothLowerDepth_div_taoPolylogUZero hA
  have hlogNormalized : Tendsto (fun x =>
      Real.log ((smoothLowerDepth (X x) (y x) : ℝ) /
        taoPolylogUZero x)) atTop (𝓝 (Real.log (1 / A))) :=
    (Real.continuousAt_log (one_div_ne_zero hA.ne')).tendsto.comp hnormalized
  have hcorrection := hlogNormalized.div_atTop tendsto_iteratedLog_atTop
  have hsum := hcorrection.add tendsto_log_taoPolylogUZero_div_iteratedLog_one
  have hsumOne : Tendsto (fun x =>
      Real.log ((smoothLowerDepth (X x) (y x) : ℝ) /
          taoPolylogUZero x) / iteratedLog x +
        Real.log (taoPolylogUZero x) / iteratedLog x) atTop (𝓝 1) := by
    simpa using hsum
  apply hsumOne.congr'
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds (one_div_pos.mpr hA)),
    tendsto_taoPolylogUZero_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hnormPos huPos
  have hproduct :
      ((smoothLowerDepth (X x) (y x) : ℝ) / taoPolylogUZero x) *
          taoPolylogUZero x = (smoothLowerDepth (X x) (y x) : ℝ) := by
    field_simp [huPos.ne']
  have hlogProduct :
      Real.log (smoothLowerDepth (X x) (y x) : ℝ) =
        Real.log ((smoothLowerDepth (X x) (y x) : ℝ) /
          taoPolylogUZero x) + Real.log (taoPolylogUZero x) := by
    conv_lhs => rw [← hproduct]
    rw [Real.log_mul hnormPos.ne' huPos.ne']
  rw [hlogProduct]
  ring

/-- The secondary logarithm `log log y` is negligible on the `log₂ x`
scale. -/
theorem IsTaoPolylogSmoothRegime.tendsto_log_log_y_div_iteratedLog_zero
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => Real.log (Real.log (y x)) / iteratedLog x)
      atTop (𝓝 0) := by
  have hnormalized := hregime.2
  have hlogNormalized : Tendsto (fun x =>
      Real.log (Real.log (y x) / iteratedLog x)) atTop (𝓝 (Real.log A)) :=
    (Real.continuousAt_log hA.ne').tendsto.comp hnormalized
  have hcorrection := hlogNormalized.div_atTop tendsto_iteratedLog_atTop
  have hlogIter : Tendsto (fun x =>
      Real.log (iteratedLog x) / iteratedLog x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_iteratedLog_atTop
  have hsum := hcorrection.add hlogIter
  have hsumZero : Tendsto (fun x =>
      Real.log (Real.log (y x) / iteratedLog x) / iteratedLog x +
        Real.log (iteratedLog x) / iteratedLog x) atTop (𝓝 0) := by
    simpa using hsum
  apply hsumZero.congr'
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds hA),
    tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hnormPos hiterPos
  have hproduct :
      (Real.log (y x) / iteratedLog x) * iteratedLog x =
        Real.log (y x) := by
    field_simp [hiterPos.ne']
  have hlogProduct : Real.log (Real.log (y x)) =
      Real.log (Real.log (y x) / iteratedLog x) +
        Real.log (iteratedLog x) := by
    conv_lhs => rw [← hproduct]
    rw [Real.log_mul hnormPos.ne' hiterPos.ne']
  rw [hlogProduct]
  ring

/-- The prime lattice below `y` has logarithmic size `A log₂ x`. -/
theorem IsTaoPolylogSmoothRegime.tendsto_log_primeCounting_div_iteratedLog
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => Real.log (Nat.primeCounting (y x) : ℝ) /
      iteratedLog x) atTop (𝓝 A) := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  simp only [div_one] at hc
  have hyCastTop : Tendsto (fun x => (y x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hregime.tendsto_y_atTop hA)
  have hcY : Tendsto (fun x => c (y x : ℝ)) atTop (𝓝 0) :=
    hc.comp hyCastTop
  have hcoefficient : Tendsto (fun x => 1 + c (y x : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hcY)
  have hlogCoefficient : Tendsto (fun x =>
      Real.log (1 + c (y x : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.continuousAt_log one_ne_zero).tendsto.comp hcoefficient
  have hcoefficientTerm : Tendsto (fun x =>
      Real.log (1 + c (y x : ℝ)) / iteratedLog x) atTop (𝓝 0) :=
    hlogCoefficient.div_atTop tendsto_iteratedLog_atTop
  have hsum :=
    (hcoefficientTerm.add hregime.2).sub
      (hregime.tendsto_log_log_y_div_iteratedLog_zero hA)
  have hsumA : Tendsto (fun x =>
      Real.log (1 + c (y x : ℝ)) / iteratedLog x +
          Real.log (y x) / iteratedLog x -
        Real.log (Real.log (y x)) / iteratedLog x) atTop (𝓝 A) := by
    simpa using hsum
  apply hsumA.congr'
  filter_upwards [hcoefficient.eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hregime.eventually_two_le_y hA] with x hcoeffPos hy
  have hyPos : (0 : ℝ) < y x := by positivity
  have hyLogPos : 0 < Real.log (y x : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hpiAt : (Nat.primeCounting (y x) : ℝ) =
      (1 + c (y x : ℝ)) * (y x : ℝ) / Real.log (y x : ℝ) := by
    simpa using hpi (y x : ℝ)
  rw [hpiAt, Real.log_div (mul_ne_zero hcoeffPos.ne' hyPos.ne')
    hyLogPos.ne', Real.log_mul hcoeffPos.ne' hyPos.ne']
  ring

theorem IsTaoPolylogSmoothRegime.tendsto_smoothLowerDepth_atTop
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => smoothLowerDepth (X x) (y x)) atTop atTop := by
  have hcast : Tendsto (fun x =>
      (smoothLowerDepth (X x) (y x) : ℝ)) atTop atTop := by
    have hproduct :=
      (hregime.tendsto_smoothLowerDepth_div_taoPolylogUZero hA).pos_mul_atTop
        (one_div_pos.mpr hA) tendsto_taoPolylogUZero_atTop
    apply hproduct.congr'
    filter_upwards [tendsto_taoPolylogUZero_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x huPos
    field_simp [huPos.ne']
  exact tendsto_natCast_atTop_iff.mp hcast

/-- The prime lattice has exponentially more coordinates than the selected
depth on the `log₂ x` scale. -/
theorem IsTaoPolylogSmoothRegime.tendsto_log_primeCounting_sub_log_depth_atTop
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) :
    Tendsto (fun x =>
      Real.log (Nat.primeCounting (y x) : ℝ) -
        Real.log (smoothLowerDepth (X x) (y x) : ℝ)) atTop atTop := by
  have hAPos : 0 < A := lt_trans zero_lt_one hA
  have hnormalized :=
    (hregime.tendsto_log_primeCounting_div_iteratedLog hAPos).sub
      (hregime.tendsto_log_smoothLowerDepth_div_iteratedLog_one hAPos)
  have hnormalized' : Tendsto (fun x =>
      (Real.log (Nat.primeCounting (y x) : ℝ) -
        Real.log (smoothLowerDepth (X x) (y x) : ℝ)) / iteratedLog x)
      atTop (𝓝 (A - 1)) := by
    apply hnormalized.congr'
    filter_upwards with x
    ring
  have hproduct := hnormalized'.pos_mul_atTop (sub_pos.mpr hA)
    tendsto_iteratedLog_atTop
  apply hproduct.congr'
  filter_upwards [tendsto_iteratedLog_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hiterPos
  field_simp [hiterPos.ne']

theorem IsTaoPolylogSmoothRegime.eventually_two_mul_depth_le_primeCounting
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) :
    ∀ᶠ x in atTop,
      2 * smoothLowerDepth (X x) (y x) ≤ Nat.primeCounting (y x) := by
  have hAPos : 0 < A := lt_trans zero_lt_one hA
  filter_upwards [
    (hregime.tendsto_log_primeCounting_sub_log_depth_atTop hA).eventually
      (eventually_gt_atTop (Real.log 2)),
    (hregime.tendsto_smoothLowerDepth_atTop hAPos).eventually
      (eventually_ge_atTop 1)] with x hmargin hk
  let k := smoothLowerDepth (X x) (y x)
  let n := Nat.primeCounting (y x)
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkLogNonneg : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  have hnLogPos : 0 < Real.log (n : ℝ) := by
    dsimp only [k, n] at hmargin ⊢
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hnPos : (0 : ℝ) < n :=
    lt_trans zero_lt_one ((Real.log_pos_iff (Nat.cast_nonneg n)).mp hnLogPos)
  have hlogMul : Real.log ((2 : ℝ) * k) =
      Real.log 2 + Real.log (k : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkPos.ne']
  have hlogLt : Real.log ((2 : ℝ) * k) < Real.log (n : ℝ) := by
    rw [hlogMul]
    dsimp only [k, n] at hmargin ⊢
    linarith
  have hrealLt : (2 : ℝ) * k < n :=
    (Real.strictMonoOn_log.lt_iff_lt (mul_pos (by norm_num) hkPos) hnPos).mp hlogLt
  exact_mod_cast hrealLt.le

/-- Integral binomial growth, rewritten as the logarithmic entropy lower
bound needed by the smooth-number lattice. -/
theorem mul_log_sub_log_le_log_choose
    {n k : ℕ} (hkPos : 1 ≤ k) (hk : k ≤ n) :
    (k : ℝ) * (Real.log n - Real.log k) ≤ Real.log (n.choose k : ℝ) := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_of_lt hkPos) hk)
  have hkRealPos : (0 : ℝ) < k := by exact_mod_cast hkPos
  have hchoosePos : (0 : ℝ) < n.choose k := by
    exact_mod_cast Nat.choose_pos hk
  have hbound : n ^ k ≤ n.choose k * k ^ k :=
    pow_le_choose_mul_pow hk
  have hboundReal : (n : ℝ) ^ k ≤ (n.choose k : ℝ) * (k : ℝ) ^ k := by
    exact_mod_cast hbound
  have hrightPos : (0 : ℝ) < (n.choose k : ℝ) * (k : ℝ) ^ k := by
    positivity
  have hlog := Real.log_le_log (pow_pos hnPos k) hboundReal
  rw [Real.log_pow, Real.log_mul hchoosePos.ne' (pow_ne_zero k hkRealPos.ne'),
    Real.log_pow] at hlog
  nlinarith

/-- The entropy lower exponent furnished by the prime subset lattice tends
to `1 - 1/A`. -/
theorem IsTaoPolylogSmoothRegime.tendsto_depth_mul_log_gap_div_log
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x =>
      (smoothLowerDepth (X x) (y x) : ℝ) *
          (Real.log (Nat.primeCounting (y x) : ℝ) -
            Real.log (smoothLowerDepth (X x) (y x) : ℝ)) /
        Real.log x) atTop (𝓝 (1 - 1 / A)) := by
  have hgap :=
    (hregime.tendsto_log_primeCounting_div_iteratedLog hA).sub
      (hregime.tendsto_log_smoothLowerDepth_div_iteratedLog_one hA)
  have hgap' : Tendsto (fun x =>
      (Real.log (Nat.primeCounting (y x) : ℝ) -
        Real.log (smoothLowerDepth (X x) (y x) : ℝ)) / iteratedLog x)
      atTop (𝓝 (A - 1)) := by
    apply hgap.congr'
    filter_upwards with x
    ring
  have hproduct :=
    (hregime.tendsto_smoothLowerDepth_div_taoPolylogUZero hA).mul hgap'
  have hproduct' : Tendsto (fun x =>
      ((smoothLowerDepth (X x) (y x) : ℝ) / taoPolylogUZero x) *
        ((Real.log (Nat.primeCounting (y x) : ℝ) -
          Real.log (smoothLowerDepth (X x) (y x) : ℝ)) / iteratedLog x))
      atTop (𝓝 (1 - 1 / A)) := by
    convert hproduct using 1
    all_goals field_simp [hA.ne']
  apply hproduct'.congr'
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hlogPos hiterPos
  rw [taoPolylogUZero_eq_log_div_iteratedLog hlogPos hiterPos]
  field_simp [hlogPos.ne', hiterPos.ne']

/-! ## Granville's full finite exponent simplex -/

/-- The finite type of primes at most `y`. -/
abbrev TaoBoundedPrime (y : ℕ) := ↥y.primesLE

/-- Forgetting the bound while retaining primality. -/
def taoBoundedPrimeAsPrime {y : ℕ} (p : TaoBoundedPrime y) : Nat.Primes :=
  ⟨p.1, Nat.prime_of_mem_primesLE p.2⟩

/-- The prime multiset associated to one fixed-degree exponent vector. -/
def smoothExponentPrimeMultiset {y d : ℕ}
    (s : Sym (TaoBoundedPrime y) d) : PrimeMultiset :=
  s.val.map taoBoundedPrimeAsPrime

/-- The integer represented by a fixed-degree exponent vector. -/
def smoothExponentValue {y d : ℕ} (s : Sym (TaoBoundedPrime y) d) : ℕ :=
  ((smoothExponentPrimeMultiset s).prod : ℕ)

/-- The symmetric power of the finite prime alphabet is finite.  The explicit
instance is useful because `Sym` is represented as a cardinality subtype of
multisets and does not synthesize this instance automatically. -/
noncomputable instance instFintypeSymTaoBoundedPrime (y d : ℕ) :
    Fintype (Sym (TaoBoundedPrime y) d) where
  elems := (Finset.univ : Finset (TaoBoundedPrime y)).sym d
  complete := by intro s; simp

/-- Unique factorization makes the product map injective on every fixed
degree of the exponent lattice. -/
theorem smoothExponentValue_injective_fixed {y d : ℕ} :
    Function.Injective (@smoothExponentValue y d) := by
  intro s t h
  have hpnat : (smoothExponentPrimeMultiset s).prod =
      (smoothExponentPrimeMultiset t).prod := PNat.eq h
  have hmulti : smoothExponentPrimeMultiset s =
      smoothExponentPrimeMultiset t := by
    rw [← PrimeMultiset.factorMultiset_prod (smoothExponentPrimeMultiset s),
      ← PrimeMultiset.factorMultiset_prod (smoothExponentPrimeMultiset t), hpnat]
  change s.val.map taoBoundedPrimeAsPrime =
    t.val.map taoBoundedPrimeAsPrime at hmulti
  apply Sym.ext
  have hinj : Function.Injective (@taoBoundedPrimeAsPrime y) := fun a b hab =>
    Subtype.ext (congrArg (fun p : Nat.Primes => (p : ℕ)) hab)
  exact (Multiset.map_injective hinj) hmulti

/-- All exponent vectors over the primes at most `y` whose total degree is at
most `d`. -/
noncomputable def smoothExponentRepresentations (y d : ℕ) :
    Finset (Σ j : ℕ, Sym (TaoBoundedPrime y) j) :=
  (Finset.range (d + 1)).sigma fun _j => Finset.univ

/-- Forget the total degree and evaluate an exponent vector. -/
def smoothExponentRepresentationValue {y : ℕ}
    (r : Σ j : ℕ, Sym (TaoBoundedPrime y) j) : ℕ :=
  smoothExponentValue r.2

theorem mem_smoothExponentRepresentations_iff {y d : ℕ}
    {r : Σ j : ℕ, Sym (TaoBoundedPrime y) j} :
    r ∈ smoothExponentRepresentations y d ↔ r.1 ≤ d := by
  simp [smoothExponentRepresentations]

/-- Products remain injective even after degrees up to `d` are combined:
the factorization recovers the multiset, and its cardinality recovers the
degree. -/
theorem injOn_smoothExponentRepresentationValue {y d : ℕ} :
    Set.InjOn (@smoothExponentRepresentationValue y)
      (smoothExponentRepresentations y d) := by
  rintro ⟨j, s⟩ _ ⟨k, t⟩ _ h
  change smoothExponentValue s = smoothExponentValue t at h
  have hpnat : (smoothExponentPrimeMultiset s).prod =
      (smoothExponentPrimeMultiset t).prod := PNat.eq h
  have hmulti : smoothExponentPrimeMultiset s =
      smoothExponentPrimeMultiset t := by
    rw [← PrimeMultiset.factorMultiset_prod (smoothExponentPrimeMultiset s),
      ← PrimeMultiset.factorMultiset_prod (smoothExponentPrimeMultiset t), hpnat]
  have hjk : j = k := by
    have hc := congrArg Multiset.card hmulti
    simpa [smoothExponentPrimeMultiset] using hc
  subst k
  have hst : s = t := smoothExponentValue_injective_fixed h
  subst t
  rfl

/-- Stars and bars counts Granville's complete exponent simplex. -/
theorem card_smoothExponentRepresentations (y d : ℕ) :
    (smoothExponentRepresentations y d).card =
      (d + Nat.primeCounting y).choose (Nat.primeCounting y) := by
  classical
  rw [smoothExponentRepresentations, Finset.card_sigma]
  simp_rw [Finset.card_univ, Sym.card_sym_eq_multichoose]
  rw [Fintype.card_coe, Nat.primesLE_card_eq_primeCounting]
  exact Nat.sum_range_multichoose d (Nat.primeCounting y)

/-- A multiset product of primes at most `y` is `y`-smooth. -/
theorem isSmooth_multiset_prod {y : ℕ} {s : Multiset ℕ}
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ y) : IsSmooth s.prod y := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [isSmooth_iff]
      exact ⟨one_ne_zero, fun p hp hpdvd => (hp.not_dvd_one hpdvd).elim⟩
  | @cons p s ih =>
      rw [Multiset.prod_cons]
      apply Nat.mul_mem_smoothNumbers
      · change IsSmooth p y
        rw [isSmooth_iff]
        refine ⟨(hs p (by simp)).1.ne_zero, ?_⟩
        intro q hq hqp
        have hqpEq : q = p :=
          (Nat.prime_dvd_prime_iff_eq hq (hs p (by simp)).1).mp hqp
        exact hqpEq ▸ (hs p (by simp)).2
      · apply ih
        intro q hq
        exact hs q (by simp [hq])

/-- Evaluation agrees literally with the product of the underlying bounded
primes. -/
theorem smoothExponentValue_eq_multisetProd {y d : ℕ}
    (s : Sym (TaoBoundedPrime y) d) :
    smoothExponentValue s = (s.val.map fun p => p.1).prod := by
  rw [smoothExponentValue, PrimeMultiset.coe_prod]
  simp [smoothExponentPrimeMultiset, PrimeMultiset.toNatMultiset,
    taoBoundedPrimeAsPrime, Multiset.map_map]

theorem smoothExponentValue_isSmooth {y d : ℕ}
    (s : Sym (TaoBoundedPrime y) d) :
    IsSmooth (smoothExponentValue s) y := by
  rw [smoothExponentValue_eq_multisetProd]
  apply isSmooth_multiset_prod
  intro p hp
  rw [Multiset.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩
  exact ⟨Nat.prime_of_mem_primesLE q.2, Nat.le_of_mem_primesLE q.2⟩

theorem smoothExponentValue_le_pow {y d : ℕ}
    (s : Sym (TaoBoundedPrime y) d) :
    smoothExponentValue s ≤ y ^ d := by
  rw [smoothExponentValue_eq_multisetProd]
  have hle := Multiset.prod_le_pow_card (s.val.map fun p => p.1) y (by
    intro p hp
    rw [Multiset.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    exact Nat.le_of_mem_primesLE q.2)
  simpa using hle

/-- The literal finite set of products arising from the exponent simplex. -/
noncomputable def smoothExponentProducts (y d : ℕ) : Finset ℕ :=
  (smoothExponentRepresentations y d).image
    smoothExponentRepresentationValue

theorem card_smoothExponentProducts (y d : ℕ) :
    (smoothExponentProducts y d).card =
      (d + Nat.primeCounting y).choose (Nat.primeCounting y) := by
  rw [smoothExponentProducts, Finset.card_image_iff.mpr
    injOn_smoothExponentRepresentationValue,
    card_smoothExponentRepresentations]

theorem mem_smoothExponentProducts_isSmooth {y d n : ℕ}
    (hn : n ∈ smoothExponentProducts y d) : IsSmooth n y := by
  rw [smoothExponentProducts, Finset.mem_image] at hn
  rcases hn with ⟨⟨j, s⟩, hs, rfl⟩
  exact smoothExponentValue_isSmooth s

theorem mem_smoothExponentProducts_le_pow {y d n : ℕ} (hy : 1 ≤ y)
    (hn : n ∈ smoothExponentProducts y d) : n ≤ y ^ d := by
  rw [smoothExponentProducts, Finset.mem_image] at hn
  rcases hn with ⟨⟨j, s⟩, hs, rfl⟩
  have hj : j ≤ d := mem_smoothExponentRepresentations_iff.mp hs
  exact (smoothExponentValue_le_pow s).trans
    (Nat.pow_le_pow_right (by omega) hj)

/-- Granville's exact finite exponent-lattice lower bound. -/
theorem primeCounting_add_depth_choose_le_psiNat
    {X y d : ℕ} (hy : 1 ≤ y) (hpower : y ^ d ≤ X) :
    (d + Nat.primeCounting y).choose (Nat.primeCounting y) ≤ psiNat X y := by
  rw [← card_smoothExponentProducts, psiNat_eq_card]
  apply Finset.card_le_card
  intro n hn
  rw [mem_smoothNumbersUpTo_source]
  exact ⟨(mem_smoothExponentProducts_le_pow hy hn).trans hpower,
    mem_smoothExponentProducts_isSmooth hn⟩

/-- The canonical integral-depth specialization of the full exponent-simplex
lower bound. -/
theorem primeCounting_add_smoothLowerDepth_choose_le_psiNat
    {X y : ℕ} (hX : X ≠ 0) (hy : 1 ≤ y) :
    (smoothLowerDepth X y + Nat.primeCounting y).choose
        (Nat.primeCounting y) ≤ psiNat X y :=
  primeCounting_add_depth_choose_le_psiNat hy (pow_smoothLowerDepth_le hX)

/-! ## Squarefree subfamily -/

/-- Products of all `k`-element subsets of the primes at most `y`. -/
def smoothPrimeSubsetProducts (y k : ℕ) : Finset ℕ :=
  (y.primesLE.powersetCard k).image fun s => ∏ p ∈ s, p

theorem primeSubsetProduct_injectiveOn (y k : ℕ) :
    Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p)
      (y.primesLE.powersetCard k) := by
  intro s hs t ht hprod
  have hsSub : s ⊆ y.primesLE := (Finset.mem_powersetCard.mp hs).1
  have htSub : t ⊆ y.primesLE := (Finset.mem_powersetCard.mp ht).1
  have hsPrime : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesLE (hsSub hp)
  have htPrime : ∀ p ∈ t, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesLE (htSub hp)
  have hfactor := congrArg Nat.primeFactors hprod
  simpa [Nat.primeFactors_prod hsPrime, Nat.primeFactors_prod htPrime] using hfactor

theorem card_smoothPrimeSubsetProducts (y k : ℕ) :
    (smoothPrimeSubsetProducts y k).card = (Nat.primeCounting y).choose k := by
  rw [smoothPrimeSubsetProducts, Finset.card_image_iff.mpr
    (primeSubsetProduct_injectiveOn y k), Finset.card_powersetCard,
    Nat.primesLE_card_eq_primeCounting]

theorem mem_smoothPrimeSubsetProducts_isSmooth
    {y k n : ℕ} (hn : n ∈ smoothPrimeSubsetProducts y k) : IsSmooth n y := by
  rw [smoothPrimeSubsetProducts, Finset.mem_image] at hn
  obtain ⟨s, hs, rfl⟩ := hn
  have hsSub : s ⊆ y.primesLE := (Finset.mem_powersetCard.mp hs).1
  have hsPrime : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesLE (hsSub hp)
  rw [isSmooth_iff]
  constructor
  · exact Finset.prod_ne_zero_iff.mpr fun p hp => (hsPrime p hp).ne_zero
  · intro p hp hpdvd
    have hprodNe : (∏ q ∈ s, q) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun q hq => (hsPrime q hq).ne_zero
    have hpMem : p ∈ Nat.primeFactors (∏ q ∈ s, q) :=
      (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hprodNe⟩)
    rw [Nat.primeFactors_prod hsPrime] at hpMem
    exact Nat.le_of_mem_primesLE (hsSub hpMem)

theorem mem_smoothPrimeSubsetProducts_le_pow
    {y k n : ℕ} (hn : n ∈ smoothPrimeSubsetProducts y k) : n ≤ y ^ k := by
  rw [smoothPrimeSubsetProducts, Finset.mem_image] at hn
  obtain ⟨s, hs, rfl⟩ := hn
  have hsData := Finset.mem_powersetCard.mp hs
  calc
    ∏ p ∈ s, p ≤ y ^ s.card :=
      Finset.prod_le_pow_card s id y fun p hp =>
        Nat.le_of_mem_primesLE (hsData.1 hp)
    _ = y ^ k := by rw [hsData.2]

/-- Finite squarefree lattice lower bound: if `y^k ≤ X`, then at least
`choose (π(y)) k` positive `y`-smooth naturals lie below `X`. -/
theorem primeCounting_choose_le_psiNat
    {X y k : ℕ} (hpower : y ^ k ≤ X) :
    (Nat.primeCounting y).choose k ≤ psiNat X y := by
  rw [← card_smoothPrimeSubsetProducts, psiNat_eq_card]
  apply Finset.card_le_card
  intro n hn
  rw [mem_smoothNumbersUpTo_source]
  exact ⟨(mem_smoothPrimeSubsetProducts_le_pow hn).trans hpower,
    mem_smoothPrimeSubsetProducts_isSmooth hn⟩

/-- Quantified binomial lower half of the polylogarithmic smooth-number
estimate. -/
theorem IsTaoPolylogSmoothRegime.eventually_rpow_le_primeCounting_choose
    {X y : ℕ → ℕ} {A ε : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (1 - 1 / A - ε) ≤
        ((Nat.primeCounting (y x)).choose
          (smoothLowerDepth (X x) (y x)) : ℝ) := by
  have hAPos : 0 < A := lt_trans zero_lt_one hA
  have hnormalized := hregime.tendsto_depth_mul_log_gap_div_log hAPos
  have hthreshold : 1 - 1 / A - ε < 1 - 1 / A := by linarith
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds hthreshold),
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    (hregime.tendsto_smoothLowerDepth_atTop hAPos).eventually
      (eventually_ge_atTop 1),
    hregime.eventually_two_mul_depth_le_primeCounting hA] with
      x hnormalized' hlogPos hkPos htwo
  let k := smoothLowerDepth (X x) (y x)
  let n := Nat.primeCounting (y x)
  have hk : k ≤ n := by dsimp only [k, n]; omega
  have hentropy : (k : ℝ) * (Real.log n - Real.log k) ≤
      Real.log (n.choose k : ℝ) :=
    mul_log_sub_log_le_log_choose (by simpa [k] using hkPos) hk
  have hscaled : (1 - 1 / A - ε) * Real.log x ≤
      (k : ℝ) * (Real.log n - Real.log k) := by
    have hstrict := (lt_div_iff₀ hlogPos).mp (by
      simpa only [k, n] using hnormalized')
    linarith
  have hchoosePos : (0 : ℝ) < n.choose k := by
    exact_mod_cast Nat.choose_pos hk
  have hxPos : (0 : ℝ) < x := by
    have : (1 : ℝ) < x := (Real.log_pos_iff (Nat.cast_nonneg x)).mp hlogPos
    linarith
  calc
    (x : ℝ) ^ (1 - 1 / A - ε) =
        Real.exp (Real.log x * (1 - 1 / A - ε)) := by
      rw [Real.rpow_def_of_pos hxPos]
    _ ≤ Real.exp (Real.log (n.choose k : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hscaled.trans hentropy]
    _ = (n.choose k : ℝ) := Real.exp_log hchoosePos

/-- Quantified lower half of Proposition 2.1(ii). -/
theorem IsTaoPolylogSmoothRegime.eventually_rpow_le_psiNat
    {X y : ℕ → ℕ} {A ε : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (1 - 1 / A - ε) ≤ (psiNat (X x) (y x) : ℝ) := by
  have hAPos : 0 < A := lt_trans zero_lt_one hA
  filter_upwards [hregime.eventually_rpow_le_primeCounting_choose hA hε,
    hregime.eventually_two_le_X] with x hlower hX
  exact hlower.trans (by
    exact_mod_cast primeCounting_choose_le_psiNat
      (pow_smoothLowerDepth_le (by omega : X x ≠ 0)))

end

end Tao2026
