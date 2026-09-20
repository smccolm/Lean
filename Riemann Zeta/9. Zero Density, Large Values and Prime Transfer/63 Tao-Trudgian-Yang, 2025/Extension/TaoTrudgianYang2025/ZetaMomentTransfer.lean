import TaoTrudgianYang2025.ZetaMomentKernel
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Separated convolution large values from the actual zeta twelfth moment

This proves the weighted-Hölder and summation step of `add-bound (ii)` on
the literal interval `[T/2,3T]`. The Perron entry inequality for a zeta
polynomial and the height bound on the twelfth moment remain separate.
-/

noncomputable section

open Finset MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def zetaMomentLogLoss (T : ℝ) : ℝ := 3 + 2 * Real.log ((⌈2 * T⌉₊ : ℝ) + 1)

theorem zetaMomentLogLoss_pos (T : ℝ) : 0 < zetaMomentLogLoss T := by
  have hlog : 0 ≤ Real.log ((⌈2 * T⌉₊ : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) ⌈2 * T⌉₊; linarith)
  unfold zetaMomentLogLoss
  linarith

theorem sum_zetaMomentKernel_on_source_window
    {T u : ℝ} (W : Finset ℝ) (hT : 0 < T)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc T (2 * T)) (hu : u ∈ Set.Icc (T / 2) (3 * T)) :
    (∑ t ∈ W, zetaMomentKernel t u) ≤ zetaMomentLogLoss T := by
  apply sum_zetaMomentKernel_le_log W u ⌈2 * T⌉₊ hSep
  intro t ht
  have htRange := hW t ht
  have hceil : 2 * T ≤ (⌈2 * T⌉₊ : ℝ) := Nat.le_ceil _
  apply abs_le.mpr
  constructor <;> linarith [hu.1, hu.2, htRange.1, htRange.2]

theorem integral_zetaMomentKernel_source_mass
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Set.Icc T (2 * T)) :
    0 < (∫ u in T / 2..3 * T, zetaMomentKernel t u) ∧
      (∫ u in T / 2..3 * T, zetaMomentKernel t u) ≤ zetaMomentLogLoss T := by
  constructor
  · apply intervalIntegral.integral_pos (by linarith)
      (continuous_zetaMomentKernel t).continuousOn
    · intro u hu
      exact (zetaMomentKernel_pos t u).le
    · exact ⟨T, ⟨by linarith, by linarith⟩, zetaMomentKernel_pos t T⟩
  · rw [integral_zetaMomentKernel (by linarith [ht.1]) (by linarith [ht.2])]
    have hc : 2 * T ≤ (⌈2 * T⌉₊ : ℝ) := Nat.le_ceil _
    have hleft := Real.log_le_log (by linarith [ht.1] : 0 < 1 + t - T / 2)
      (by linarith [ht.2] : 1 + t - T / 2 ≤ (⌈2 * T⌉₊ : ℝ) + 1)
    have hright := Real.log_le_log (by linarith [ht.2] : 0 < 1 + 3 * T - t)
      (by linarith [ht.1] : 1 + 3 * T - t ≤ (⌈2 * T⌉₊ : ℝ) + 1)
    unfold zetaMomentLogLoss
    linarith

/-- The analytic summation estimate for a nonnegative continuous function.
Its loss is logarithmic, not the length of the integration interval. -/
theorem sum_convolution_twelfth_le_moment
    {T : ℝ} (W : Finset ℝ) (hT : 0 < T)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc T (2 * T))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u) :
    (∑ t ∈ W, (∫ u in T / 2..3 * T, zetaMomentKernel t u * f u) ^ 12) ≤
      zetaMomentLogLoss T ^ 12 * ∫ u in T / 2..3 * T, f u ^ 12 := by
  have hab : T / 2 ≤ 3 * T := by linarith
  have hweighted (t : ℝ) : Continuous (fun u => zetaMomentKernel t u * f u ^ 12) :=
    (continuous_zetaMomentKernel t).mul (hf.pow 12)
  have hJensen (t : ℝ) (ht : t ∈ W) :
      (∫ u in T / 2..3 * T, zetaMomentKernel t u * f u) ^ 12 ≤
        zetaMomentLogLoss T ^ 11 *
          ∫ u in T / 2..3 * T, zetaMomentKernel t u * f u ^ 12 := by
    obtain ⟨hmass, hmassBound⟩ := integral_zetaMomentKernel_source_mass hT (hW t ht)
    have hraw := integral_weighted_twelfth (μ := volume.restrict (Set.Ioc (T / 2) (3 * T)))
      (fun u => (zetaMomentKernel_pos t u).le) hf0
      ((continuous_zetaMomentKernel t).intervalIntegrable (T / 2) (3 * T)).1
      (((continuous_zetaMomentKernel t).mul hf).intervalIntegrable (T / 2) (3 * T)).1
      ((hweighted t).intervalIntegrable (T / 2) (3 * T)).1
      (by simpa only [intervalIntegral.integral_of_le hab] using hmass)
    have hraw' :
        (∫ u in T / 2..3 * T, zetaMomentKernel t u * f u) ^ 12 ≤
          (∫ u in T / 2..3 * T, zetaMomentKernel t u) ^ 11 *
            ∫ u in T / 2..3 * T, zetaMomentKernel t u * f u ^ 12 := by
      simpa only [intervalIntegral.integral_of_le hab] using hraw
    apply hraw'.trans
    apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmass.le hmassBound 11)
    exact intervalIntegral.integral_nonneg hab fun u _ =>
      mul_nonneg (zetaMomentKernel_pos t u).le (pow_nonneg (hf0 u) 12)
  have hsum : (∑ t ∈ W, ∫ u in T / 2..3 * T, zetaMomentKernel t u * f u ^ 12) ≤
      zetaMomentLogLoss T * ∫ u in T / 2..3 * T, f u ^ 12 := by
    rw [← intervalIntegral.integral_finsetSum (fun t ht =>
      (hweighted t).intervalIntegrable (T / 2) (3 * T)),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      ((continuous_finsetSum W fun t ht => hweighted t).intervalIntegrable (T / 2) (3 * T))
      (((hf.pow 12).const_mul _).intervalIntegrable (T / 2) (3 * T))
    intro u hu
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_zetaMomentKernel_on_source_window W hT hSep hW hu)
      (pow_nonneg (hf0 u) 12)
  calc
    _ ≤ ∑ t ∈ W, zetaMomentLogLoss T ^ 11 *
        ∫ u in T / 2..3 * T, zetaMomentKernel t u * f u ^ 12 :=
      Finset.sum_le_sum hJensen
    _ = zetaMomentLogLoss T ^ 11 *
        ∑ t ∈ W, ∫ u in T / 2..3 * T, zetaMomentKernel t u * f u ^ 12 :=
      (Finset.mul_sum ..).symm
    _ ≤ zetaMomentLogLoss T ^ 11 *
        (zetaMomentLogLoss T * ∫ u in T / 2..3 * T, f u ^ 12) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (zetaMomentLogLoss_pos T).le 11)
    _ = _ := by ring

def zetaMomentCriticalNorm (t : ℝ) : ℝ :=
  ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖

theorem continuous_zetaMomentCriticalNorm : Continuous zetaMomentCriticalNorm := by
  unfold zetaMomentCriticalNorm
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
  apply ContinuousAt.comp (g := riemannZeta)
    (f := fun u : ℝ => (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I))
  · exact (differentiableAt_riemannZeta hne).continuousAt
  · fun_prop

def zetaMomentConvolution (T t : ℝ) : ℝ :=
  ∫ u in T / 2..3 * T, zetaMomentKernel t u * zetaMomentCriticalNorm u

def zetaTwelfthMoment (T : ℝ) : ℝ :=
  ∫ u in T / 2..3 * T, zetaMomentCriticalNorm u ^ 12

/-- Weighted Hölder and one-separation applied to the actual critical-line
zeta function, with every source interval and logarithmic loss retained. -/
theorem sum_zetaMomentConvolution_twelfth
    {T : ℝ} (W : Finset ℝ) (hT : 0 < T)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc T (2 * T)) :
    (∑ t ∈ W, zetaMomentConvolution T t ^ 12) ≤
      zetaMomentLogLoss T ^ 12 * zetaTwelfthMoment T :=
  sum_convolution_twelfth_le_moment W hT hSep hW zetaMomentCriticalNorm
    continuous_zetaMomentCriticalNorm (fun _ => norm_nonneg _)

/-- The finite moment-to-cardinality step for large convolution values.
The convolution lower bound is a genuine upstream analytic input, not a
cardinality or energy conclusion. -/
theorem zetaMomentConvolution_largeValues
    {T V : ℝ} (W : Finset ℝ) (hT : 0 < T) (hV : 0 ≤ V)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc T (2 * T))
    (hLarge : ∀ t ∈ W, V ≤ zetaMomentConvolution T t) :
    (W.card : ℝ) * V ^ 12 ≤ zetaMomentLogLoss T ^ 12 * zetaTwelfthMoment T := by
  apply le_trans _ (sum_zetaMomentConvolution_twelfth W hT hSep hW)
  calc
    _ = ∑ _t ∈ W, V ^ 12 := by simp
    _ ≤ _ := Finset.sum_le_sum fun t ht => pow_le_pow_left₀ hV (hLarge t ht) 12

/-- Actual zeta-pattern consumer of the finite moment estimate. The only
extra premise is the pointwise Perron/convolution entry inequality, stated
with its physical normalization. It is not proved or postulated here. -/
theorem ZetaLargeValuePattern.twelfth_cardinality_of_convolution
    (P : ZetaLargeValuePattern) {C : ℝ} (hC : 0 < C)
    (hEntry : ∀ t ∈ P.ordinates,
      P.V ≤ C * Real.sqrt P.N * zetaMomentConvolution P.T t) :
    (P.ordinates.card : ℝ) * P.V ^ 12 ≤
      C ^ 12 * P.N ^ 6 * zetaMomentLogLoss P.T ^ 12 * zetaTwelfthMoment P.T := by
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hfactor : 0 < C * Real.sqrt P.N := mul_pos hC (Real.sqrt_pos.2 hN)
  have hRange (t : ℝ) (ht : t ∈ P.ordinates) : t ∈ Set.Icc P.T (2 * P.T) := by
    simpa only [P.intervalLeft_eq, P.intervalRight_eq] using P.ordinates_in_interval t ht
  have h := zetaMomentConvolution_largeValues P.ordinates P.T_pos
    (div_nonneg P.V_pos.le hfactor.le) P.ordinates_oneSeparated hRange
    (fun t ht => (div_le_iff₀ hfactor).2 (by nlinarith [hEntry t ht]))
  have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg hfactor.le 12)
  have hcancel : (C * Real.sqrt P.N) ^ 12 *
      ((P.ordinates.card : ℝ) * (P.V / (C * Real.sqrt P.N)) ^ 12) =
      (P.ordinates.card : ℝ) * P.V ^ 12 := by
    field_simp [hfactor.ne']
  have hnorm : (C * Real.sqrt P.N) ^ 12 = C ^ 12 * P.N ^ 6 := by
    rw [mul_pow]
    have hs : Real.sqrt P.N ^ 12 = P.N ^ 6 := by
      calc
        _ = (Real.sqrt P.N ^ 2) ^ 6 := by ring
        _ = _ := by rw [Real.sq_sqrt hN.le]
    rw [hs]
  rw [hcancel, hnorm] at hmul
  simpa only [mul_assoc] using hmul

end TaoTrudgianYang2025
