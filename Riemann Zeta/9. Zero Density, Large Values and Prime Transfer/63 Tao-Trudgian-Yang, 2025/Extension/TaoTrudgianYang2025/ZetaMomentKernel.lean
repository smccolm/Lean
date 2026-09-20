import TaoTrudgianYang2025.ClassicalLargeValueRegions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# The logarithmic convolution kernel in the zeta moment transfer

These are analytic estimates for the literal kernel `1/(1+|u-t|)` used
in the source proof of `add-bound (ii)`. The Perron entry is proved
separately in `ZetaPerronEntry`; Heath--Brown's twelfth moment remains open.
-/

noncomputable section

open Finset MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def zetaMomentKernel (t u : ℝ) : ℝ := 1 / (1 + |u - t|)

theorem zetaMomentKernel_pos (t u : ℝ) : 0 < zetaMomentKernel t u := by
  unfold zetaMomentKernel
  positivity

theorem continuous_zetaMomentKernel (t : ℝ) : Continuous (zetaMomentKernel t) := by
  unfold zetaMomentKernel
  apply continuous_const.div (by fun_prop)
  intro u
  have := abs_nonneg (u - t)
  linarith

/-- An arbitrary center, not necessarily in the ordinate family, has only
logarithmic total kernel mass. The possible central point is kept explicitly. -/
theorem sum_zetaMomentKernel_le_harmonic
    (W : Finset ℝ) (u : ℝ) (N : ℕ)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hRange : ∀ t ∈ W, |t - u| ≤ N) :
    (∑ t ∈ W, zetaMomentKernel t u) ≤ 1 + 2 * (harmonic (N + 1) : ℝ) := by
  let S := W.erase u
  let shell : ℝ → ℕ := fun t => ⌊|t - u|⌋₊
  have hmaps : ∀ t ∈ S, shell t ∈ Finset.range (N + 1) := by
    intro t ht
    have hr := hRange t (Finset.mem_of_mem_erase ht)
    have hfloor : ((shell t : ℕ) : ℝ) ≤ (N : ℝ) :=
      (Nat.floor_le (abs_nonneg _)).trans hr
    have : shell t ≤ N := by exact_mod_cast hfloor
    simpa only [Finset.mem_range] using Nat.lt_succ_of_le this
  have hoff : (∑ t ∈ S, zetaMomentKernel t u) ≤ 2 * (harmonic (N + 1) : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => zetaMomentKernel t u)]
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), 2 * (1 / ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hcard : ({t ∈ S | shell t = k}).card ≤ 2 := by
          apply le_trans (Finset.card_le_card ?_)
            (RiemannZeta.GuthMaynard.separated_annulus_card_le_two W u k hSep)
          intro t ht
          obtain ⟨htS, htk⟩ := Finset.mem_filter.mp ht
          have htW := Finset.mem_erase.mp htS
          apply Finset.mem_filter.mpr
          refine ⟨htW.2, htW.1, ?_, ?_⟩
          · rw [← htk]
            exact Nat.floor_le (abs_nonneg _)
          · rw [← htk]
            exact Nat.lt_floor_add_one _
        calc
          _ ≤ ∑ _t ∈ {t ∈ S | shell t = k}, 1 / ((k : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro t ht
            have htk := (Finset.mem_filter.mp ht).2
            have hl : (k : ℝ) ≤ |t - u| := by
              rw [← htk]
              exact Nat.floor_le (abs_nonneg _)
            unfold zetaMomentKernel
            rw [abs_sub_comm u t]
            apply one_div_le_one_div_of_le (by positivity)
            linarith
          _ = (({t ∈ S | shell t = k}).card : ℝ) * (1 / ((k : ℝ) + 1)) := by simp
          _ ≤ 2 * (1 / ((k : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcard
      _ = 2 * (harmonic (N + 1) : ℝ) := by
        rw [harmonic]
        push_cast
        simp only [inv_eq_one_div]
        rw [Finset.mul_sum]
  by_cases hu : u ∈ W
  · rw [← Finset.sum_erase_add _ _ hu]
    have heq : zetaMomentKernel u u = 1 := by simp [zetaMomentKernel]
    rw [heq]
    dsimp [S] at hoff
    linarith
  · have hS : S = W := by simpa only [S] using (Finset.erase_eq_of_notMem hu)
    rw [hS] at hoff
    linarith

theorem sum_zetaMomentKernel_le_log
    (W : Finset ℝ) (u : ℝ) (N : ℕ)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hRange : ∀ t ∈ W, |t - u| ≤ N) :
    (∑ t ∈ W, zetaMomentKernel t u) ≤ 3 + 2 * Real.log (N + 1) := by
  have h := sum_zetaMomentKernel_le_harmonic W u N hSep hRange
  have hh := harmonic_le_one_add_log (N + 1)
  push_cast at hh
  linarith

/-- Young's inequality in the exact polynomial form used for weighted
twelfth-power Hölder. -/
theorem twelfth_tangent_bound {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    12 * a ^ 11 * x ≤ x ^ 12 + 11 * a ^ 12 := by
  have hpq : (12 : ℝ).HolderConjugate (12 / 11) := by
    norm_num [Real.holderConjugate_iff]
  have h := Real.young_inequality_of_nonneg hx (pow_nonneg ha 11) hpq
  have hp : (a ^ 11) ^ (12 / 11 : ℝ) = a ^ 12 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  rw [hp] at h
  norm_num at h
  calc
    12 * a ^ 11 * x = 12 * (x * a ^ 11) := by ring
    _ ≤ 12 * (x ^ 12 / 12 + a ^ 12 / (12 / 11)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = x ^ 12 + 11 * a ^ 12 := by ring

/-- The exact kernel mass when the center lies in the interval. -/
theorem integral_zetaMomentKernel {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    (∫ u in a..b, zetaMomentKernel t u) =
      Real.log (1 + t - a) + Real.log (1 + b - t) := by
  have hcont := continuous_zetaMomentKernel t
  have hleft : (∫ u in a..t, zetaMomentKernel t u) = Real.log (1 + t - a) := by
    have hderiv (u : ℝ) (hu : u ∈ Set.uIcc a t) :
        HasDerivAt (fun x : ℝ => -Real.log (1 + t - x)) (zetaMomentKernel t u) u := by
      rw [Set.uIcc_of_le hat] at hu
      have hp : 0 < 1 + t - u := by linarith [hu.2]
      have hd := (((hasDerivAt_const u (1 + t)).sub (hasDerivAt_id u)).log hp.ne').neg
      convert hd using 1
      unfold zetaMomentKernel
      rw [abs_of_nonpos (by linarith [hu.2] : u - t ≤ 0)]
      dsimp
      ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a t)
    simpa only [add_sub_cancel_right, Real.log_one, neg_zero, zero_sub, neg_neg] using h
  have hright : (∫ u in t..b, zetaMomentKernel t u) = Real.log (1 + b - t) := by
    have hderiv (u : ℝ) (hu : u ∈ Set.uIcc t b) :
        HasDerivAt (fun x : ℝ => Real.log (1 + x - t)) (zetaMomentKernel t u) u := by
      rw [Set.uIcc_of_le htb] at hu
      have hp : 0 < 1 + u - t := by linarith [hu.1]
      have hd := (((hasDerivAt_const u 1).add (hasDerivAt_id u)).sub_const t).log hp.ne'
      convert hd using 1
      unfold zetaMomentKernel
      rw [abs_of_nonneg (by linarith [hu.1] : 0 ≤ u - t)]
      dsimp
      ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable t b)
    simpa only [add_sub_cancel_right, Real.log_one, sub_zero] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable a t) (hcont.intervalIntegrable t b), hleft, hright]

/-- Weighted twelfth-power Hölder with the exact eleventh power of the
kernel mass. Its proof integrates Young's inequality and normalizes the
actual weighted mean; no moment estimate is a premise. -/
theorem integral_weighted_twelfth
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x)
    (hwInt : Integrable w μ) (hwfInt : Integrable (fun x => w x * f x) μ)
    (hwfPowInt : Integrable (fun x => w x * f x ^ 12) μ)
    (hMass : 0 < ∫ x, w x ∂μ) :
    (∫ x, w x * f x ∂μ) ^ 12 ≤
      (∫ x, w x ∂μ) ^ 11 * ∫ x, w x * f x ^ 12 ∂μ := by
  let A : ℝ := (∫ x, w x * f x ∂μ) / (∫ x, w x ∂μ)
  have hA : 0 ≤ A := div_nonneg (integral_nonneg fun x => mul_nonneg (hw x) (hf x)) hMass.le
  have hmean : A * (∫ x, w x ∂μ) = ∫ x, w x * f x ∂μ := div_mul_cancel₀ _ hMass.ne'
  have hpoint (x : α) :
      (12 * A ^ 11) * (w x * f x) ≤ w x * f x ^ 12 + (11 * A ^ 12) * w x := by
    have h := mul_le_mul_of_nonneg_left (twelfth_tangent_bound hA (hf x)) (hw x)
    nlinarith
  have hInt := integral_mono (hwfInt.const_mul (12 * A ^ 11))
    (hwfPowInt.add (hwInt.const_mul (11 * A ^ 12))) hpoint
  dsimp only [Pi.add_apply] at hInt
  rw [integral_add hwfPowInt (hwInt.const_mul _), integral_const_mul, integral_const_mul] at hInt
  have hsmall : A ^ 12 * (∫ x, w x ∂μ) ≤ ∫ x, w x * f x ^ 12 ∂μ := by
    rw [← hmean] at hInt
    nlinarith
  calc
    _ = (∫ x, w x ∂μ) ^ 11 * (A ^ 12 * (∫ x, w x ∂μ)) := by rw [← hmean]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (pow_nonneg hMass.le 11)

end TaoTrudgianYang2025
