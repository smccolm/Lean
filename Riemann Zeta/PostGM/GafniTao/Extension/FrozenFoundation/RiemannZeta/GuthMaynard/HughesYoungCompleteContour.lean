import RiemannZeta.GuthMaynard.HughesYoungEquation84SourceLine
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

set_option maxHeartbeats 4000000

namespace RiemannZeta.GuthMaynard

/-!
# Complete Hughes--Young contour integrals

This file passes from the finite-height rectangle identities to integrals on
the whole vertical line.  It is the exact analytic bridge needed before the
positive shift and modulus sums are assembled on `Re w = 1`.
-/

theorem continuous_hughesYoungEquation84PositiveContourSeries_vertical
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 3 / 2) :
    Continuous (fun u : ℝ =>
      hughesYoungEquation84PositiveContourSeries T t h k a b r
        ((c : ℂ) + (u : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have houter : ContinuousAt
      (hughesYoungEquation84PositiveContourSeries T t h k a b r)
      ((c : ℂ) + (u : ℂ) * I) :=
    (differentiableAt_hughesYoungEquation84PositiveContourSeries
    T t h k a b r ha hb hr (w := (c : ℂ) + (u : ℂ) * I)
      (by simpa using hc0) (by simpa using hc1)).continuousAt
  have hinner : ContinuousAt (fun v : ℝ => (c : ℂ) + (v : ℂ) * I) u := by
    fun_prop
  simpa only [Function.comp_apply] using
    houter.comp (x := u) (f := fun v : ℝ => (c : ℂ) + (v : ℂ) * I) hinner

theorem continuous_hughesYoungEquation84NegativeContourSeries_vertical
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 3 / 2) :
    Continuous (fun u : ℝ =>
      hughesYoungEquation84NegativeContourSeries T t h k a b r
        ((c : ℂ) + (u : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have houter : ContinuousAt
      (hughesYoungEquation84NegativeContourSeries T t h k a b r)
      ((c : ℂ) + (u : ℂ) * I) :=
    (differentiableAt_hughesYoungEquation84NegativeContourSeries
    T t h k a b r ha hb hr (w := (c : ℂ) + (u : ℂ) * I)
      (by simpa using hc0) (by simpa using hc1)).continuousAt
  have hinner : ContinuousAt (fun v : ℝ => (c : ℂ) + (v : ℂ) * I) u := by
    fun_prop
  simpa only [Function.comp_apply] using
    houter.comp (x := u) (f := fun v : ℝ => (c : ℂ) + (v : ℂ) * I) hinner

theorem integrable_hughesYoungEquation84PositiveContourSeries_vertical
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 3 / 2) :
    Integrable (fun u : ℝ =>
      hughesYoungEquation84PositiveContourSeries T t h k a b r
        ((c : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_norm_hughesYoungEquation84PositiveContourSeries_horizontal_le
      T t h k a b r ha hb hr hc0 hc1 (le_refl c)
  let L : ℝ := max 1 (|t| + 1)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply integrable_of_continuous_of_norm_le_gaussian_tail
    (fun u : ℝ =>
      hughesYoungEquation84PositiveContourSeries T t h k a b r
        ((c : ℂ) + (u : ℂ) * I))
    (continuous_hughesYoungEquation84PositiveContourSeries_vertical
      T t h k a b r ha hb hr hc0 hc1)
    (C := C) (A := 100 * c ^ 2) (B := 60)
    (D := 2 + |t| + c) (j := 17)
    hL (by norm_num : (0 : ℝ) < 60)
  intro u hu
  have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
  have hut : |t| + 1 ≤ |u| := (le_max_right 1 (|t| + 1)).trans hu
  have hcMem : c ∈ Set.Icc c c := by simp
  simpa only [L, add_assoc] using hbound u hu1 hut c hcMem

theorem integrable_hughesYoungEquation84NegativeContourSeries_vertical
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 3 / 2) :
    Integrable (fun u : ℝ =>
      hughesYoungEquation84NegativeContourSeries T t h k a b r
        ((c : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_norm_hughesYoungEquation84NegativeContourSeries_horizontal_le
      T t h k a b r ha hb hr hc0 hc1 (le_refl c)
  let L : ℝ := max 1 (|t| + 1)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply integrable_of_continuous_of_norm_le_gaussian_tail
    (fun u : ℝ =>
      hughesYoungEquation84NegativeContourSeries T t h k a b r
        ((c : ℂ) + (u : ℂ) * I))
    (continuous_hughesYoungEquation84NegativeContourSeries_vertical
      T t h k a b r ha hb hr hc0 hc1)
    (C := C) (A := 100 * c ^ 2) (B := 60)
    (D := 2 + |t| + c) (j := 17)
    hL (by norm_num : (0 : ℝ) < 60)
  intro u hu
  have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
  have hut : |t| + 1 ≤ |u| := (le_max_right 1 (|t| + 1)).trans hu
  have hcMem : c ∈ Set.Icc c c := by simp
  simpa only [L, add_assoc] using hbound u hu1 hut c hcMem

/-- The complete positive equation-(84) modulus series has the same whole-line
integral on any two vertical lines in the regularized strip. -/
theorem integral_hughesYoungEquation84PositiveContourSeries_vertical_eq
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    (∫ u : ℝ, hughesYoungEquation84PositiveContourSeries T t h k a b r
        ((c₁ : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, hughesYoungEquation84PositiveContourSeries T t h k a b r
        ((c₀ : ℂ) + (u : ℂ) * I) := by
  have hc₀1 : c₀ < 3 / 2 := hc.trans_lt hc₁
  have hc₁0 : 0 < c₁ := hc₀.trans_le hc
  have htop := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungEquation84PositiveContourSeries_vertical
      T t h k a b r ha hb hr hc₁0 hc₁)
    tendsto_neg_atTop_atBot tendsto_id
  have hbottom := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungEquation84PositiveContourSeries_vertical
      T t h k a b r ha hb hr hc₀ hc₀1)
    tendsto_neg_atTop_atBot tendsto_id
  have hsub := htop.sub hbottom
  have hzero :=
    tendsto_hughesYoungEquation84PositiveContourSeries_vertical_sub_zero
      T t h k a b r ha hb hr hc₀ hc₁ hc
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hzero)

/-- Negative-shift counterpart of the whole-line contour translation. -/
theorem integral_hughesYoungEquation84NegativeContourSeries_vertical_eq
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    (∫ u : ℝ, hughesYoungEquation84NegativeContourSeries T t h k a b r
        ((c₁ : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, hughesYoungEquation84NegativeContourSeries T t h k a b r
        ((c₀ : ℂ) + (u : ℂ) * I) := by
  have hc₀1 : c₀ < 3 / 2 := hc.trans_lt hc₁
  have hc₁0 : 0 < c₁ := hc₀.trans_le hc
  have htop := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungEquation84NegativeContourSeries_vertical
      T t h k a b r ha hb hr hc₁0 hc₁)
    tendsto_neg_atTop_atBot tendsto_id
  have hbottom := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungEquation84NegativeContourSeries_vertical
      T t h k a b r ha hb hr hc₀ hc₀1)
    tendsto_neg_atTop_atBot tendsto_id
  have hsub := htop.sub hbottom
  have hzero :=
    tendsto_hughesYoungEquation84NegativeContourSeries_vertical_sub_zero
      T t h k a b r ha hb hr hc₀ hc₁ hc
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hzero)

end RiemannZeta.GuthMaynard
