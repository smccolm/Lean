import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import RiemannZeta.GuthMaynard.HughesYoungCleaning

open Complex Filter Finset Topology
open Classical

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative polygamma input for Hughes--Young equation (65)

The height derivatives in Hughes--Young's cleaning step require decay of
derivatives of logarithmic Gamma ratios.  This file starts from the pinned
digamma series and proves the vertical-line summability estimate that supplies
one inverse power of the height for every derivative.  It is kept separate
from the DFI weight profile because it is an analytic dependency of the
far-shift argument, not part of DFI's theorem.
-/

/-- The absolutely convergent series underlying the `j`-th derivative of
`digamma`; the normalization by signs and factorials is applied only when the
derivative identity is used. -/
noncomputable def hughesYoungPolygammaSeries (j : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((n : ℂ) + z)⁻¹ ^ (j + 1)

private theorem norm_nat_add_complex_lower
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    min z.re 1 * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + z‖ := by
  have hc0 : 0 < min z.re 1 := lt_min hz zero_lt_one
  have hcre : min z.re 1 ≤ z.re := min_le_left _ _
  have hc1 : min z.re 1 ≤ 1 := min_le_right _ _
  have hre : (n : ℝ) + z.re ≤ ‖(n : ℂ) + z‖ := by
    simpa [add_comm] using Complex.re_le_norm ((n : ℂ) + z)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    min z.re 1 * ((n : ℝ) + 1) =
        min z.re 1 * (n : ℝ) + min z.re 1 := by ring
    _ ≤ (n : ℝ) + z.re := by nlinarith
    _ ≤ ‖(n : ℂ) + z‖ := hre

theorem summable_norm_hughesYoungPolygammaTerm
    {z : ℂ} (hz : 0 < z.re) {j : ℕ} (hj : 1 ≤ j) :
    Summable (fun n : ℕ => ‖((n : ℂ) + z)⁻¹ ^ (j + 1)‖) := by
  let c : ℝ := min z.re 1
  have hc : 0 < c := lt_min hz zero_lt_one
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) :=
    Complex.summable_one_div_natCast_add_one_sq
  have hmajor : Summable (fun n : ℕ =>
      c⁻¹ ^ (j + 1) * (1 / ((n : ℝ) + 1) ^ 2)) :=
    hbase.mul_left _
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmajor
  intro n
  have hlower : c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + z‖ :=
    norm_nat_add_complex_lower hz n
  have hn1 : 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 n
  have hcn : 0 < c * ((n : ℝ) + 1) := mul_pos hc (by positivity)
  have hnorm : 0 < ‖(n : ℂ) + z‖ := hcn.trans_le hlower
  rw [norm_pow, norm_inv]
  have hpow : (c * ((n : ℝ) + 1)) ^ (j + 1) ≤
      ‖(n : ℂ) + z‖ ^ (j + 1) :=
    pow_le_pow_left₀ hcn.le hlower _
  calc
    ‖(n : ℂ) + z‖⁻¹ ^ (j + 1) =
        (‖(n : ℂ) + z‖ ^ (j + 1))⁻¹ := by rw [inv_pow]
    _ ≤ ((c * ((n : ℝ) + 1)) ^ (j + 1))⁻¹ := by
      exact inv_anti₀ (pow_pos hcn _) hpow
    _ = c⁻¹ ^ (j + 1) * (((n : ℝ) + 1)⁻¹ ^ (j + 1)) := by
      rw [mul_pow, mul_inv, inv_pow, inv_pow]
    _ ≤ c⁻¹ ^ (j + 1) * (((n : ℝ) + 1)⁻¹ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hpow' : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ (j + 1) := by
        exact pow_le_pow_right₀ hn1 (by omega)
      simpa [inv_pow] using inv_anti₀ (by positivity) hpow'
    _ = c⁻¹ ^ (j + 1) * (1 / ((n : ℝ) + 1) ^ 2) := by
      simp only [one_div, inv_pow]

private theorem norm_polygammaTerm_le_im
    {z : ℂ} {j n : ℕ} (him : 0 < |z.im|) :
    ‖((n : ℂ) + z)⁻¹ ^ (j + 1)‖ ≤ |z.im|⁻¹ ^ (j + 1) := by
  have himle : |z.im| ≤ ‖(n : ℂ) + z‖ := by
    simpa using Complex.abs_im_le_norm ((n : ℂ) + z)
  rw [norm_pow, norm_inv]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
    (inv_anti₀ him himle) _

private theorem norm_polygammaTerm_le_real
    {z : ℂ} (hz : 0 < z.re) {j n : ℕ} :
    ‖((n : ℂ) + z)⁻¹ ^ (j + 1)‖ ≤
      (min z.re 1)⁻¹ ^ (j + 1) * (((n : ℝ) + 1)⁻¹ ^ (j + 1)) := by
  let c : ℝ := min z.re 1
  have hc : 0 < c := lt_min hz zero_lt_one
  have hlower : c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + z‖ :=
    norm_nat_add_complex_lower hz n
  have hcn : 0 < c * ((n : ℝ) + 1) := mul_pos hc (by positivity)
  rw [norm_pow, norm_inv]
  calc
    ‖(n : ℂ) + z‖⁻¹ ^ (j + 1) =
        (‖(n : ℂ) + z‖ ^ (j + 1))⁻¹ := by rw [inv_pow]
    _ ≤ ((c * ((n : ℝ) + 1)) ^ (j + 1))⁻¹ := by
      exact inv_anti₀ (pow_pos hcn _)
        (pow_le_pow_left₀ hcn.le hlower _)
    _ = c⁻¹ ^ (j + 1) * (((n : ℝ) + 1)⁻¹ ^ (j + 1)) := by
      rw [mul_pow, mul_inv, inv_pow, inv_pow]

/-- Quantitative vertical decay of the absolutely convergent polygamma
series.  This is the scale-sensitive input needed in Hughes--Young (65): the
`j`-th logarithmic derivative gains `j` inverse powers of the ordinate. -/
theorem norm_hughesYoungPolygammaSeries_le
    {z : ℂ} (hz : 0 < z.re) {j : ℕ} (hj : 1 ≤ j)
    (him : 1 ≤ |z.im|) :
    ‖hughesYoungPolygammaSeries j z‖ ≤
      (3 + (min z.re 1)⁻¹ ^ (j + 1)) * |z.im|⁻¹ ^ j := by
  let y : ℝ := |z.im|
  let N : ℕ := ⌈y⌉₊ + 1
  let c : ℝ := min z.re 1
  have hy : 1 ≤ y := him
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hN1 : 1 ≤ N := Nat.le_add_left 1 _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hyN : y ≤ (N : ℝ) := by
    change y ≤ ((⌈y⌉₊ + 1 : ℕ) : ℝ)
    push_cast
    linarith [Nat.le_ceil y]
  have hNle : (N : ℝ) ≤ 3 * y := by
    change ((⌈y⌉₊ + 1 : ℕ) : ℝ) ≤ 3 * y
    push_cast
    have hceil := Nat.ceil_lt_add_one (le_trans (by norm_num) hy)
    linarith
  have hsum := summable_norm_hughesYoungPolygammaTerm hz hj
  have hsplit :
      (∑ n ∈ Finset.range N, ((n : ℂ) + z)⁻¹ ^ (j + 1)) +
          ∑' i : ℕ, (((i + N : ℕ) : ℂ) + z)⁻¹ ^ (j + 1) =
        hughesYoungPolygammaSeries j z := by
    exact hsum.of_norm.sum_add_tsum_nat_add N
  have hhead :
      ‖∑ n ∈ Finset.range N, ((n : ℂ) + z)⁻¹ ^ (j + 1)‖ ≤
        3 * y⁻¹ ^ j := by
    calc
      ‖∑ n ∈ Finset.range N, ((n : ℂ) + z)⁻¹ ^ (j + 1)‖ ≤
          ∑ n ∈ Finset.range N, ‖((n : ℂ) + z)⁻¹ ^ (j + 1)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, y⁻¹ ^ (j + 1) := by
        apply Finset.sum_le_sum
        intro n hn
        exact norm_polygammaTerm_le_im (z := z) (j := j) (n := n) hy0
      _ = (N : ℝ) * y⁻¹ ^ (j + 1) := by simp
      _ ≤ (3 * y) * y⁻¹ ^ (j + 1) := by
        exact mul_le_mul_of_nonneg_right hNle (by positivity)
      _ = 3 * y⁻¹ ^ j := by
        rw [pow_succ]
        calc
          (3 * y) * (y⁻¹ ^ j * y⁻¹) = 3 * y⁻¹ ^ j * (y * y⁻¹) := by ring
          _ = 3 * y⁻¹ ^ j := by rw [mul_inv_cancel₀ hy0.ne', mul_one]
  have htailNorm : Summable (fun i : ℕ =>
      ‖(((i + N : ℕ) : ℂ) + z)⁻¹ ^ (j + 1)‖) :=
    (summable_nat_add_iff N).mpr hsum
  have htailPoint (i : ℕ) :
      ‖(((i + N : ℕ) : ℂ) + z)⁻¹ ^ (j + 1)‖ ≤
        c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ (j - 1) *
          (1 / (((i + N : ℕ) : ℝ) + 1) ^ 2) := by
    have hreal := norm_polygammaTerm_le_real (z := z) hz
      (j := j) (n := i + N)
    rw [show min z.re 1 = c by rfl] at hreal
    refine hreal.trans ?_
    have hbase : (N : ℝ) ≤ ((i + N : ℕ) : ℝ) + 1 := by
      have hnat : N ≤ i + N + 1 := by omega
      exact_mod_cast hnat
    have hinv : ((((i + N : ℕ) : ℝ) + 1)⁻¹) ≤ (N : ℝ)⁻¹ := by
      exact inv_anti₀ hNpos hbase
    have hdecomp : j + 1 = (j - 1) + 2 := by omega
    have htermDecomp :
        ((((i + N : ℕ) : ℝ) + 1)⁻¹) ^ (j + 1) =
          ((((i + N : ℕ) : ℝ) + 1)⁻¹) ^ (j - 1) *
            ((((i + N : ℕ) : ℝ) + 1)⁻¹) ^ 2 := by
      rw [hdecomp, pow_add]
    have hpowInv : ((((i + N : ℕ) : ℝ) + 1)⁻¹) ^ (j - 1) ≤
        (N : ℝ)⁻¹ ^ (j - 1) :=
      pow_le_pow_left₀ (by positivity) hinv _
    calc
      c⁻¹ ^ (j + 1) * ((((i + N : ℕ) : ℝ) + 1)⁻¹ ^ (j + 1)) =
          c⁻¹ ^ (j + 1) *
            (((((i + N : ℕ) : ℝ) + 1)⁻¹ ^ (j - 1)) *
              ((((i + N : ℕ) : ℝ) + 1)⁻¹ ^ 2)) := by
        rw [htermDecomp]
      _ ≤ c⁻¹ ^ (j + 1) *
            ((N : ℝ)⁻¹ ^ (j - 1) *
              ((((i + N : ℕ) : ℝ) + 1)⁻¹ ^ 2)) := by
        gcongr
      _ = c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ (j - 1) *
          (1 / (((i + N : ℕ) : ℝ) + 1) ^ 2) := by
        have hsquare : ((((i + N : ℕ) : ℝ) + 1)⁻¹) ^ 2 =
            1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 := by
          rw [one_div, inv_pow]
        rw [hsquare]
        ring
  have htailMajor : Summable (fun i : ℕ =>
      c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ (j - 1) *
        (1 / (((i + N : ℕ) : ℝ) + 1) ^ 2)) := by
    have hsquares : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) :=
      Complex.summable_one_div_natCast_add_one_sq
    have hshift := (summable_nat_add_iff N).mpr hsquares
    exact hshift.mul_left _
  have htail :
      ‖∑' i : ℕ, (((i + N : ℕ) : ℂ) + z)⁻¹ ^ (j + 1)‖ ≤
        c⁻¹ ^ (j + 1) * y⁻¹ ^ j := by
    calc
      ‖∑' i : ℕ, (((i + N : ℕ) : ℂ) + z)⁻¹ ^ (j + 1)‖ ≤
          ∑' i : ℕ, ‖(((i + N : ℕ) : ℂ) + z)⁻¹ ^ (j + 1)‖ :=
        norm_tsum_le_tsum_norm htailNorm
      _ ≤ ∑' i : ℕ, c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ (j - 1) *
          (1 / (((i + N : ℕ) : ℝ) + 1) ^ 2) :=
        htailNorm.tsum_le_tsum htailPoint htailMajor
      _ = (c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ (j - 1)) *
          ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 := by
        rw [tsum_mul_left]
      _ ≤ (c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ (j - 1)) * (N : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left
          (Complex.tsum_one_div_natCast_add_add_one_sq_le hN1)
        positivity
      _ = c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ j := by
        calc
          (c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ (j - 1)) * (N : ℝ)⁻¹ =
              c⁻¹ ^ (j + 1) * ((N : ℝ)⁻¹ ^ (j - 1) * (N : ℝ)⁻¹) := by ring
          _ = c⁻¹ ^ (j + 1) * (N : ℝ)⁻¹ ^ j := by
            rw [← pow_succ, Nat.sub_add_cancel hj]
      _ ≤ c⁻¹ ^ (j + 1) * y⁻¹ ^ j := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hy0 hyN) _
  rw [← hsplit]
  calc
    ‖(∑ n ∈ Finset.range N, ((n : ℂ) + z)⁻¹ ^ (j + 1)) +
        ∑' i : ℕ, (((i + N : ℕ) : ℂ) + z)⁻¹ ^ (j + 1)‖ ≤
      ‖∑ n ∈ Finset.range N, ((n : ℂ) + z)⁻¹ ^ (j + 1)‖ +
        ‖∑' i : ℕ, (((i + N : ℕ) : ℂ) + z)⁻¹ ^ (j + 1)‖ := norm_add_le _ _
    _ ≤ 3 * y⁻¹ ^ j + c⁻¹ ^ (j + 1) * y⁻¹ ^ j := add_le_add hhead htail
    _ = (3 + c⁻¹ ^ (j + 1)) * y⁻¹ ^ j := by ring

private theorem hasDerivAt_hughesYoungPolygammaTerm
    (j n : ℕ) {z : ℂ} (hz : (n : ℂ) + z ≠ 0) :
    HasDerivAt (fun w : ℂ => ((n : ℂ) + w)⁻¹ ^ (j + 1))
      (-(j + 1 : ℂ) * ((n : ℂ) + z)⁻¹ ^ (j + 2)) z := by
  have hlin : HasDerivAt (fun w : ℂ => (n : ℂ) + w) 1 z :=
    by simpa using (hasDerivAt_const z (n : ℂ)).add (hasDerivAt_id z)
  have hinv := hlin.inv hz
  have hpow := hinv.pow (j + 1)
  convert hpow using 1
  simp only [Nat.add_sub_cancel]
  have hpowAdd : ((n : ℂ) + z)⁻¹ ^ (j + 2) =
      ((n : ℂ) + z)⁻¹ ^ j * ((n : ℂ) + z)⁻¹ ^ 2 := by
    rw [pow_add]
  have hdiv : (-1 : ℂ) / ((n : ℂ) + z) ^ 2 =
      -(((n : ℂ) + z)⁻¹ ^ 2) := by
    rw [neg_div, one_div, inv_pow]
  change -((j : ℂ) + 1) * ((n : ℂ) + z)⁻¹ ^ (j + 2) =
    ((j + 1 : ℕ) : ℂ) * ((n : ℂ) + z)⁻¹ ^ j *
      ((-1 : ℂ) / ((n : ℂ) + z) ^ 2)
  rw [hpowAdd]
  rw [hdiv]
  push_cast
  ring

/-- The derivative of the polygamma series is obtained term by term on the
open right half-plane.  Unlike a formal differentiation rule, this theorem
contains the locally uniform summability argument needed to justify the
exchange of derivative and infinite sum. -/
theorem hasDerivAt_hughesYoungPolygammaSeries
    (j : ℕ) (hj : 1 ≤ j) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (hughesYoungPolygammaSeries j)
      (-(j + 1 : ℂ) * hughesYoungPolygammaSeries (j + 1) z) z := by
  let a : ℝ := z.re / 2
  let c : ℝ := min a 1
  let t : Set ℂ := {w | a < w.re}
  have ha : 0 < a := by dsimp [a]; linarith
  have hc : 0 < c := lt_min ha zero_lt_one
  have htOpen : IsOpen t := isOpen_lt continuous_const continuous_re
  have htPre : IsPreconnected t := by
    apply Convex.isPreconnected
    intro x hx y hy u v hu hv huv
    change a < (u • x + v • y).re
    simp only [add_re, smul_re]
    change a < u * x.re + v * y.re
    change a < x.re at hx
    change a < y.re at hy
    by_cases hu0 : u = 0
    · subst u
      simp only [zero_add] at huv
      subst v
      simpa using hy
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hux : u * a < u * x.re := mul_lt_mul_of_pos_left hx hupos
      have hvy : v * a ≤ v * y.re := mul_le_mul_of_nonneg_left (le_of_lt hy) hv
      nlinarith
  have hzt : z ∈ t := by change a < z.re; dsimp [a]; linarith
  let u : ℕ → ℝ := fun n =>
    (j + 1 : ℝ) * c⁻¹ ^ (j + 2) * (1 / ((n : ℝ) + 1) ^ 2)
  have hu : Summable u := by
    exact Complex.summable_one_div_natCast_add_one_sq.mul_left _
  have hterm (n : ℕ) (w : ℂ) (hw : w ∈ t) :
      HasDerivAt (fun q : ℂ => ((n : ℂ) + q)⁻¹ ^ (j + 1))
        (-(j + 1 : ℂ) * ((n : ℂ) + w)⁻¹ ^ (j + 2)) w := by
    apply hasDerivAt_hughesYoungPolygammaTerm
    have hpos : 0 < ((n : ℂ) + w).re := by
      simp only [add_re, natCast_re]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      change a < w.re at hw
      linarith
    exact fun hzero => by simp [hzero] at hpos
  have hderivBound (n : ℕ) (w : ℂ) (hw : w ∈ t) :
      ‖-(j + 1 : ℂ) * ((n : ℂ) + w)⁻¹ ^ (j + 2)‖ ≤ u n := by
    have hwre : a < w.re := hw
    have hcw : c ≤ w.re := (min_le_left a 1).trans (le_of_lt hwre)
    have hlower : c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + w‖ := by
      have hre : (n : ℝ) + w.re ≤ ‖(n : ℂ) + w‖ := by
        simpa [add_comm] using Complex.re_le_norm ((n : ℂ) + w)
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hc1 : c ≤ 1 := min_le_right _ _
      nlinarith
    have hcn : 0 < c * ((n : ℝ) + 1) := mul_pos hc (by positivity)
    have hpow : (c * ((n : ℝ) + 1)) ^ (j + 2) ≤
        ‖(n : ℂ) + w‖ ^ (j + 2) :=
      pow_le_pow_left₀ hcn.le hlower _
    have hinvPow : ‖(n : ℂ) + w‖⁻¹ ^ (j + 2) ≤
        c⁻¹ ^ (j + 2) * (((n : ℝ) + 1)⁻¹ ^ (j + 2)) := by
      calc
        ‖(n : ℂ) + w‖⁻¹ ^ (j + 2) =
            (‖(n : ℂ) + w‖ ^ (j + 2))⁻¹ := by rw [inv_pow]
        _ ≤ ((c * ((n : ℝ) + 1)) ^ (j + 2))⁻¹ :=
          inv_anti₀ (pow_pos hcn _) hpow
        _ = c⁻¹ ^ (j + 2) * (((n : ℝ) + 1)⁻¹ ^ (j + 2)) := by
          rw [mul_pow, mul_inv, inv_pow, inv_pow]
    have hpowerDrop : (((n : ℝ) + 1)⁻¹ ^ (j + 2)) ≤
        (((n : ℝ) + 1)⁻¹ ^ 2) := by
      have hp : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ (j + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simpa [inv_pow] using inv_anti₀ (by positivity) hp
    rw [norm_mul, norm_neg]
    have hcast : (j + 1 : ℂ) = ((j + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_natCast, norm_pow, norm_inv]
    push_cast
    change (j + 1 : ℝ) * ‖(n : ℂ) + w‖⁻¹ ^ (j + 2) ≤ _
    calc
      (j + 1 : ℝ) * ‖(n : ℂ) + w‖⁻¹ ^ (j + 2) ≤
          (j + 1 : ℝ) *
            (c⁻¹ ^ (j + 2) * (((n : ℝ) + 1)⁻¹ ^ (j + 2))) := by
        gcongr
      _ ≤ (j + 1 : ℝ) *
            (c⁻¹ ^ (j + 2) * (((n : ℝ) + 1)⁻¹ ^ 2)) := by
        gcongr
      _ = u n := by
        have hsquare : (((n : ℝ) + 1)⁻¹) ^ 2 =
            1 / ((n : ℝ) + 1) ^ 2 := by
          rw [one_div, inv_pow]
        dsimp [u]
        rw [hsquare]
        ring
  have hpoint : Summable (fun n : ℕ => ((n : ℂ) + z)⁻¹ ^ (j + 1)) :=
    (summable_norm_hughesYoungPolygammaTerm hz hj).of_norm
  have h := hasDerivAt_tsum_of_isPreconnected hu htOpen htPre hterm hderivBound
    hzt hpoint hzt
  simpa only [hughesYoungPolygammaSeries, tsum_mul_left] using h

/-- The first derivative of `digamma` is the absolutely convergent quadratic
polygamma series.  The proof starts from the pinned digamma series, verifies
uniform derivative summability on a right half-plane, and only then
differentiates term by term. -/
theorem hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.digamma (hughesYoungPolygammaSeries 1 z) z := by
  let a : ℝ := z.re / 2
  let c : ℝ := min a 1
  let t : Set ℂ := {w | a < w.re}
  have ha : 0 < a := by dsimp [a]; linarith
  have hc : 0 < c := lt_min ha zero_lt_one
  have htOpen : IsOpen t := isOpen_lt continuous_const continuous_re
  have htPre : IsPreconnected t := by
    apply Convex.isPreconnected
    intro x hx y hy u v hu hv huv
    change a < (u • x + v • y).re
    simp only [add_re, smul_re]
    change a < u * x.re + v * y.re
    change a < x.re at hx
    change a < y.re at hy
    by_cases hu0 : u = 0
    · subst u
      simp only [zero_add] at huv
      subst v
      simpa using hy
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hux : u * a < u * x.re := mul_lt_mul_of_pos_left hx hupos
      have hvy : v * a ≤ v * y.re := mul_le_mul_of_nonneg_left (le_of_lt hy) hv
      nlinarith
  have hzt : z ∈ t := by change a < z.re; dsimp [a]; linarith
  let g : ℕ → ℂ → ℂ := fun n w =>
    ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + w)⁻¹
  let u : ℕ → ℝ := fun n => c⁻¹ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2)
  have hu : Summable u :=
    Complex.summable_one_div_natCast_add_one_sq.mul_left _
  have hterm (n : ℕ) (w : ℂ) (hw : w ∈ t) :
      HasDerivAt (g n) (((n : ℂ) + w)⁻¹ ^ 2) w := by
    have hpos : 0 < ((n : ℂ) + w).re := by
      simp only [add_re, natCast_re]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      change a < w.re at hw
      linarith
    have hne : (n : ℂ) + w ≠ 0 := fun hzero => by simp [hzero] at hpos
    have hlin : HasDerivAt (fun q : ℂ => (n : ℂ) + q) 1 w := by
      simpa using (hasDerivAt_const w (n : ℂ)).add (hasDerivAt_id w)
    have hinv := hlin.inv hne
    have hconst : HasDerivAt (fun _q : ℂ => ((n : ℂ) + 1)⁻¹) 0 w :=
      hasDerivAt_const _ _
    dsimp [g]
    convert hconst.sub hinv using 1
    rw [neg_div, one_div, inv_pow]
    ring
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ t) :
      ‖((n : ℂ) + w)⁻¹ ^ 2‖ ≤ u n := by
    have hwre : a < w.re := hw
    have hcw : c ≤ w.re := (min_le_left a 1).trans (le_of_lt hwre)
    have hlower : c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + w‖ := by
      have hre : (n : ℝ) + w.re ≤ ‖(n : ℂ) + w‖ := by
        simpa [add_comm] using Complex.re_le_norm ((n : ℂ) + w)
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hc1 : c ≤ 1 := min_le_right _ _
      nlinarith
    have hcn : 0 < c * ((n : ℝ) + 1) := mul_pos hc (by positivity)
    rw [norm_pow, norm_inv]
    calc
      ‖(n : ℂ) + w‖⁻¹ ^ 2 = (‖(n : ℂ) + w‖ ^ 2)⁻¹ := by rw [inv_pow]
      _ ≤ ((c * ((n : ℝ) + 1)) ^ 2)⁻¹ := by
        exact inv_anti₀ (pow_pos hcn _) (pow_le_pow_left₀ hcn.le hlower _)
      _ = u n := by
        dsimp [u]
        calc
          ((c * ((n : ℝ) + 1)) ^ 2)⁻¹ =
              c⁻¹ ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2) := by
            rw [mul_pow, mul_inv, inv_pow, inv_pow]
          _ = c⁻¹ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
            congr 1
            rw [one_div, inv_pow]
  have hpoles (w : ℂ) (hw : w ∈ t) : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hzero
    have hwpos : 0 < w.re := lt_trans ha hw
    have hre := congrArg Complex.re hzero
    simp only [neg_re, natCast_re] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hpoint : Summable (fun n : ℕ => g n z) := by
    have hs := (Complex.hasSum_digamma (hpoles z hzt)).summable
    exact hs.congr (fun n => by simp [g, one_div, add_comm])
  have hseries := hasDerivAt_tsum_of_isPreconnected hu htOpen htPre hterm hbound
    hzt hpoint hzt
  have hseries' : HasDerivAt (fun w => ∑' n : ℕ, g n w)
      (hughesYoungPolygammaSeries 1 z) z := by
    simpa only [hughesYoungPolygammaSeries] using hseries
  have hrhs : HasDerivAt
      (fun w => -(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, g n w)
      (hughesYoungPolygammaSeries 1 z) z := by
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const z (-(Real.eulerMascheroniConstant : ℂ))).add hseries'
  have heq (w : ℂ) (hw : w ∈ t) :
      Complex.digamma w =
        -(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, g n w := by
    rw [Complex.digamma_eq_tsum (hpoles w hw)]
    congr 1
    apply tsum_congr
    intro n
    simp [g, one_div, add_comm]
  apply hrhs.congr_of_eventuallyEq
  filter_upwards [htOpen.mem_nhds hzt] with w hw
  exact heq w hw

/-- Every positive-order derivative of `digamma` is the corresponding
polygamma series with its exact sign and factorial.  The induction uses the
termwise derivative theorem above on a genuine neighborhood at every step,
so no formal interchange of an infinite sum is hidden in the statement. -/
theorem iteratedDeriv_succ_digamma_eq_hughesYoungPolygammaSeries
    (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv (n + 1) Complex.digamma z =
      (-1 : ℂ) ^ (n + 2) * (n + 1).factorial *
        hughesYoungPolygammaSeries (n + 1) z := by
  induction n generalizing z with
  | zero =>
      rw [iteratedDeriv_one]
      have h := hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one hz
      rw [h.deriv]
      norm_num
  | succ n ih =>
      let A : ℂ := (-1 : ℂ) ^ (n + 2) * (n + 1).factorial
      let F : ℂ → ℂ := fun w => A * hughesYoungPolygammaSeries (n + 1) w
      have hs := hasDerivAt_hughesYoungPolygammaSeries (n + 1) (by omega) hz
      have hconst : HasDerivAt (fun _w : ℂ => A) 0 z := hasDerivAt_const _ _
      have hF : HasDerivAt F
          (A * (-(((n + 1 : ℕ) : ℂ) + 1) *
            hughesYoungPolygammaSeries (n + 1 + 1) z)) z := by
        simpa only [F, zero_mul, zero_add] using hconst.mul hs
      have hopen : IsOpen {w : ℂ | 0 < w.re} :=
        isOpen_lt continuous_const continuous_re
      have hzopen : z ∈ {w : ℂ | 0 < w.re} := hz
      have hevent : (iteratedDeriv (n + 1) Complex.digamma) =ᶠ[nhds z] F := by
        filter_upwards [hopen.mem_nhds hzopen] with w hw
        exact ih hw
      have hactual : HasDerivAt (iteratedDeriv (n + 1) Complex.digamma)
          (A * (-(((n + 1 : ℕ) : ℂ) + 1) *
            hughesYoungPolygammaSeries (n + 1 + 1) z)) z :=
        hF.congr_of_eventuallyEq hevent
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, iteratedDeriv_succ,
        hactual.deriv]
      dsimp [A]
      have hsign : (-1 : ℂ) ^ (n + 3) = (-1 : ℂ) ^ (n + 2) * (-1) := by
        rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
      have hfac : (n + 2).factorial = (n + 2) * (n + 1).factorial := by
        exact Nat.factorial_succ (n + 1)
      rw [hsign, hfac]
      push_cast
      ring

theorem iteratedDeriv_digamma_eq_hughesYoungPolygammaSeries
    {j : ℕ} (hj : 1 ≤ j) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv j Complex.digamma z =
      (-1 : ℂ) ^ (j + 1) * j.factorial * hughesYoungPolygammaSeries j z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  simpa [add_assoc, add_comm, add_left_comm] using
    iteratedDeriv_succ_digamma_eq_hughesYoungPolygammaSeries k hz

/-- Quantitative vertical decay for the positive-order derivatives of
`digamma`, with all dependence on the derivative order and the fixed real
part explicit. -/
theorem norm_iteratedDeriv_digamma_le
    {j : ℕ} (hj : 1 ≤ j) {z : ℂ} (hz : 0 < z.re)
    (him : 1 ≤ |z.im|) :
    ‖iteratedDeriv j Complex.digamma z‖ ≤
      j.factorial * (3 + (min z.re 1)⁻¹ ^ (j + 1)) * |z.im|⁻¹ ^ j := by
  rw [iteratedDeriv_digamma_eq_hughesYoungPolygammaSeries hj hz,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
    Complex.norm_natCast]
  have hseries := norm_hughesYoungPolygammaSeries_le hz hj him
  calc
    1 ^ (j + 1) * (j.factorial : ℝ) *
        ‖hughesYoungPolygammaSeries j z‖ ≤
      1 ^ (j + 1) * (j.factorial : ℝ) *
        ((3 + (min z.re 1)⁻¹ ^ (j + 1)) * |z.im|⁻¹ ^ j) := by
      gcongr
    _ = j.factorial * (3 + (min z.re 1)⁻¹ ^ (j + 1)) * |z.im|⁻¹ ^ j := by
      norm_num
      ring

theorem hasDerivAt_iteratedDeriv_digamma
    {j : ℕ} (hj : 1 ≤ j) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (iteratedDeriv j Complex.digamma)
      (iteratedDeriv (j + 1) Complex.digamma z) z := by
  let A : ℂ := (-1 : ℂ) ^ (j + 1) * j.factorial
  let F : ℂ → ℂ := fun w => A * hughesYoungPolygammaSeries j w
  have hs := hasDerivAt_hughesYoungPolygammaSeries j hj hz
  have hconst : HasDerivAt (fun _w : ℂ => A) 0 z := hasDerivAt_const _ _
  have hF : HasDerivAt F
      (A * (-(j + 1 : ℂ) * hughesYoungPolygammaSeries (j + 1) z)) z := by
    simpa only [F, zero_mul, zero_add] using hconst.mul hs
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const continuous_re
  have hzopen : z ∈ {w : ℂ | 0 < w.re} := hz
  have hevent : (iteratedDeriv j Complex.digamma) =ᶠ[nhds z] F := by
    filter_upwards [hopen.mem_nhds hzopen] with w hw
    exact iteratedDeriv_digamma_eq_hughesYoungPolygammaSeries hj hw
  have hactual : HasDerivAt (iteratedDeriv j Complex.digamma)
      (A * (-(j + 1 : ℂ) * hughesYoungPolygammaSeries (j + 1) z)) z :=
    hF.congr_of_eventuallyEq hevent
  have hnext : iteratedDeriv (j + 1) Complex.digamma z =
      A * (-(j + 1 : ℂ) * hughesYoungPolygammaSeries (j + 1) z) := by
    rw [iteratedDeriv_succ, hactual.deriv]
  exact hactual.congr_deriv hnext.symm

end RiemannZeta.GuthMaynard
