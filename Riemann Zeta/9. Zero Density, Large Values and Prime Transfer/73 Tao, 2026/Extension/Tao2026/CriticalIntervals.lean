import Tao2026.VinogradovPhase
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Critical intervals for reciprocal phases

The normalized `r`-th derivative of the reciprocal phase is the absolute
value of `N/t + M_r/t^j`.  The source removes one short interval for each
derivative order where these two terms nearly cancel.  This module develops
the exact algebra controlling that small-value set; measure and cardinality
bounds are kept for the subsequent analytic layer.
-/

open Set

namespace Tao2026

noncomputable section

/-- After multiplication by `t`, the possible cancellation in the normalized
derivative is governed by `N + C/t^k`, where `k=j-1`. -/
def reciprocalCriticalExpression
    (N C : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  N + C / t ^ k

/-- Exact difference formula for the critical expression. -/
theorem reciprocalCriticalExpression_sub
    (N C : ℝ) (k : ℕ) {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    reciprocalCriticalExpression N C k t -
        reciprocalCriticalExpression N C k s =
      C * (s ^ k - t ^ k) / (t ^ k * s ^ k) := by
  unfold reciprocalCriticalExpression
  field_simp [hs, ht]
  ring

/-- Two points in the same absolute sublevel set have critical-expression
values differing by at most twice its threshold. -/
theorem abs_reciprocalCriticalExpression_sub_le_two_mul
    (N C : ℝ) (k : ℕ) {s t δ : ℝ}
    (ht : |reciprocalCriticalExpression N C k t| ≤ δ)
    (hs : |reciprocalCriticalExpression N C k s| ≤ δ) :
    |reciprocalCriticalExpression N C k t -
        reciprocalCriticalExpression N C k s| ≤ 2 * δ := by
  calc
    |reciprocalCriticalExpression N C k t -
        reciprocalCriticalExpression N C k s| ≤
      |reciprocalCriticalExpression N C k t| +
        |reciprocalCriticalExpression N C k s| := abs_sub _ _
    _ ≤ δ + δ := add_le_add ht hs
    _ = 2 * δ := by ring

/-- Algebraic separation inequality for two points in a critical sublevel
set.  This is the numerator/denominator form used to bound the diameter of
the exceptional interval. -/
theorem abs_coefficient_mul_abs_pow_sub_le
    (N C : ℝ) (k : ℕ) {s t δ : ℝ}
    (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (ht : |reciprocalCriticalExpression N C k t| ≤ δ)
    (hs : |reciprocalCriticalExpression N C k s| ≤ δ) :
    |C| * |s ^ k - t ^ k| ≤ 2 * δ * |t ^ k * s ^ k| := by
  have hsmall :=
    abs_reciprocalCriticalExpression_sub_le_two_mul N C k ht hs
  rw [reciprocalCriticalExpression_sub N C k hs0 ht0,
    abs_div, abs_mul] at hsmall
  have hden : |t ^ k * s ^ k| ≠ 0 := by
    positivity
  calc
    |C| * |s ^ k - t ^ k| =
        (|C| * |s ^ k - t ^ k| / |t ^ k * s ^ k|) *
          |t ^ k * s ^ k| := by field_simp
    _ ≤ (2 * δ) * |t ^ k * s ^ k| :=
      mul_le_mul_of_nonneg_right hsmall (abs_nonneg _)

/-- On the positive half-line, a power difference controls the underlying
difference at the scale of the left endpoint.  The coefficient `k` from the
mean-value theorem is deliberately discarded; the source argument only needs
an absolute constant. -/
theorem pow_mul_sub_le_pow_sub
    {X s t : ℝ} {k : ℕ}
    (hX : 0 ≤ X) (hs : X ≤ s) (hst : s ≤ t) (hk : 1 ≤ k) :
    X ^ (k - 1) * (t - s) ≤ t ^ k - s ^ k := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hs0 : 0 ≤ s := hX.trans hs
  have hdiff : 0 ≤ t - s := sub_nonneg.mpr hst
  have hXpow : X ^ q ≤ t ^ q := by
    exact pow_le_pow_left₀ hX (hs.trans hst) q
  have hstpow : s ^ q ≤ t ^ q := by
    exact pow_le_pow_left₀ hs0 hst q
  calc
    X ^ (Nat.succ q - 1) * (t - s) = X ^ q * (t - s) := by simp
    _ ≤ t ^ q * (t - s) := mul_le_mul_of_nonneg_right hXpow hdiff
    _ ≤ t ^ Nat.succ q - s ^ Nat.succ q := by
      rw [pow_succ, pow_succ]
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hstpow)]

/-- Symmetric absolute-value form of `pow_mul_sub_le_pow_sub`. -/
theorem pow_mul_abs_sub_le_abs_pow_sub
    {X s t : ℝ} {k : ℕ}
    (hX : 0 ≤ X) (hs : X ≤ s) (ht : X ≤ t) (hk : 1 ≤ k) :
    X ^ (k - 1) * |t - s| ≤ |t ^ k - s ^ k| := by
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst),
      abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (hX.trans hs) hst k))]
    exact pow_mul_sub_le_pow_sub hX hs hst hk
  · rw [abs_of_nonpos (sub_nonpos.mpr hts),
      abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ (hX.trans ht) hts k)),
      neg_sub, neg_sub]
    exact pow_mul_sub_le_pow_sub hX ht hts hk

/-- Elementary reduction of the source's near-dyadic power condition to the
single scalar estimate `(1+η)^k ≤ 2`. -/
theorem nearDyadic_pow_le_two_mul
    {X t η : ℝ} {k : ℕ}
    (hX : 0 ≤ X) (ht : X ≤ t) (htop : t ≤ X * (1 + η))
    (hfactor : (1 + η) ^ k ≤ 2) :
    t ^ k ≤ 2 * X ^ k := by
  have ht0 : 0 ≤ t := hX.trans ht
  calc
    t ^ k ≤ (X * (1 + η)) ^ k := pow_le_pow_left₀ ht0 htop k
    _ = X ^ k * (1 + η) ^ k := mul_pow X (1 + η) k
    _ ≤ X ^ k * 2 :=
      mul_le_mul_of_nonneg_left hfactor (pow_nonneg hX k)
    _ = 2 * X ^ k := by ring

/-- A finite set of natural-number lattice points in a real interval has at
most the interval length plus one elements. -/
theorem card_nat_points_Icc_le
    (s : Finset ℕ) {a b : ℝ}
    (hab : a ≤ b) (hs : ∀ n ∈ s, (n : ℝ) ∈ Set.Icc a b) :
    (s.card : ℝ) ≤ b - a + 1 := by
  by_cases hnonempty : s.Nonempty
  · let i := s.min' hnonempty
    let j := s.max' hnonempty
    have hi : i ∈ s := s.min'_mem hnonempty
    have hj : j ∈ s := s.max'_mem hnonempty
    have hij : i ≤ j := s.min'_le j hj
    have hsubset : s ⊆ Finset.Icc i j := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
    have hcard : s.card ≤ (Finset.Icc i j).card := Finset.card_le_card hsubset
    rw [Nat.card_Icc] at hcard
    have hcardReal : (s.card : ℝ) ≤ ((j + 1 - i : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have hcardWidth : ((j + 1 - i : ℕ) : ℝ) = (j : ℝ) - i + 1 := by
      norm_cast
      omega
    have hiBounds := hs i hi
    have hjBounds := hs j hj
    calc
      (s.card : ℝ) ≤ ((j + 1 - i : ℕ) : ℝ) := hcardReal
      _ = (j : ℝ) - i + 1 := hcardWidth
      _ ≤ b - a + 1 := by linarith [hiBounds.1, hjBounds.2]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

/-- Pair separation with an explicit common envelope for the two denominator
powers.  This sharper form is what is used on the source's very short
near-dyadic interval, where `t^k ≤ 2 X^k`. -/
theorem criticalSublevel_pair_separation_of_pow_le
    (N C : ℝ) {k : ℕ} {X B s t δ : ℝ}
    (hX : 0 < X) (hB : 0 ≤ B)
    (hsX : X ≤ s) (htX : X ≤ t)
    (hsPow : s ^ k ≤ B) (htPow : t ^ k ≤ B) (hk : 1 ≤ k)
    (hs : |reciprocalCriticalExpression N C k s| ≤ δ)
    (ht : |reciprocalCriticalExpression N C k t| ≤ δ) :
    |C| * X ^ (k - 1) * |t - s| ≤ 2 * δ * B ^ 2 := by
  have hs0 : 0 < s := hX.trans_le hsX
  have ht0 : 0 < t := hX.trans_le htX
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hs
  have hpower : X ^ (k - 1) * |t - s| ≤ |s ^ k - t ^ k| := by
    simpa [abs_sub_comm] using
      pow_mul_abs_sub_le_abs_pow_sub hX.le hsX htX hk
  have hlower :
      |C| * X ^ (k - 1) * |t - s| ≤ |C| * |s ^ k - t ^ k| := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hpower (abs_nonneg C)
  have hcritical :
      |C| * |s ^ k - t ^ k| ≤ 2 * δ * |t ^ k * s ^ k| :=
    abs_coefficient_mul_abs_pow_sub_le N C k hs0.ne' ht0.ne' ht hs
  have hproduct : |t ^ k * s ^ k| ≤ B ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg ht0.le k) (pow_nonneg hs0.le k)),
      pow_two]
    exact mul_le_mul htPow hsPow (pow_nonneg hs0.le k) hB
  calc
    |C| * X ^ (k - 1) * |t - s| ≤ |C| * |s ^ k - t ^ k| := hlower
    _ ≤ 2 * δ * |t ^ k * s ^ k| := hcritical
    _ ≤ 2 * δ * B ^ 2 :=
      mul_le_mul_of_nonneg_left hproduct (mul_nonneg (by positivity) hδ)

/-- Quotient form of the sharp envelope-based separation estimate. -/
theorem criticalSublevel_pair_dist_le_of_pow_le
    (N C : ℝ) {k : ℕ} {X B s t δ : ℝ}
    (hX : 0 < X) (hC : C ≠ 0) (hB : 0 ≤ B)
    (hsX : X ≤ s) (htX : X ≤ t)
    (hsPow : s ^ k ≤ B) (htPow : t ^ k ≤ B) (hk : 1 ≤ k)
    (hs : |reciprocalCriticalExpression N C k s| ≤ δ)
    (ht : |reciprocalCriticalExpression N C k t| ≤ δ) :
    |t - s| ≤ 2 * δ * B ^ 2 / (|C| * X ^ (k - 1)) := by
  have hden : 0 < |C| * X ^ (k - 1) :=
    mul_pos (abs_pos.mpr hC) (pow_pos hX _)
  rw [le_div_iff₀ hden]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    criticalSublevel_pair_separation_of_pow_le N C hX hB
      hsX htX hsPow htPow hk hs ht

/-- Source-scale specialization: if both denominator powers are at most
`2 X^k` and the critical threshold is `|C| X^{-k} q`, then the bad points
are separated by at most `8Xq`, independently of the derivative order. -/
theorem criticalSublevel_pair_dist_le_eight_mul
    (N C : ℝ) {k : ℕ} {X s t q : ℝ}
    (hX : 0 < X) (hC : C ≠ 0)
    (hsX : X ≤ s) (htX : X ≤ t)
    (hsPow : s ^ k ≤ 2 * X ^ k) (htPow : t ^ k ≤ 2 * X ^ k)
    (hk : 1 ≤ k)
    (hs : |reciprocalCriticalExpression N C k s| ≤ |C| / X ^ k * q)
    (ht : |reciprocalCriticalExpression N C k t| ≤ |C| / X ^ k * q) :
    |t - s| ≤ 8 * X * q := by
  have hB : 0 ≤ 2 * X ^ k := mul_nonneg (by norm_num) (pow_nonneg hX.le k)
  have hbound := criticalSublevel_pair_dist_le_of_pow_le N C hX hC hB
    hsX htX hsPow htPow hk hs ht
  have hkpow : X ^ k = X ^ (k - 1) * X := by
    calc
      X ^ k = X ^ ((k - 1) + 1) := by congr 1; omega
      _ = X ^ (k - 1) * X := by rw [pow_succ]
  calc
    |t - s| ≤
        2 * (|C| / X ^ k * q) * (2 * X ^ k) ^ 2 /
          (|C| * X ^ (k - 1)) := hbound
    _ = 8 * X * q := by
      rw [hkpow]
      field_simp [abs_ne_zero.mpr hC, hX.ne']
      ring

/-- Two points of one critical sublevel set inside `[X,Y]` are close in the
division-free form needed by the exceptional-interval argument.  In
particular, when `C ≠ 0` this becomes a diameter bound after division by
`|C| X^(k-1)`. -/
theorem criticalSublevel_pair_separation
    (N C : ℝ) {k : ℕ} {X Y s t δ : ℝ}
    (hX : 0 < X) (hsX : X ≤ s) (hsY : s ≤ Y)
    (htX : X ≤ t) (htY : t ≤ Y) (hk : 1 ≤ k)
    (hs : |reciprocalCriticalExpression N C k s| ≤ δ)
    (ht : |reciprocalCriticalExpression N C k t| ≤ δ) :
    |C| * X ^ (k - 1) * |t - s| ≤ 2 * δ * Y ^ (2 * k) := by
  have hs0 : 0 < s := hX.trans_le hsX
  have ht0 : 0 < t := hX.trans_le htX
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hs
  have hpower : X ^ (k - 1) * |t - s| ≤ |s ^ k - t ^ k| := by
    simpa [abs_sub_comm] using
      pow_mul_abs_sub_le_abs_pow_sub hX.le hsX htX hk
  have hlower :
      |C| * X ^ (k - 1) * |t - s| ≤ |C| * |s ^ k - t ^ k| := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hpower (abs_nonneg C)
  have hcritical :
      |C| * |s ^ k - t ^ k| ≤ 2 * δ * |t ^ k * s ^ k| :=
    abs_coefficient_mul_abs_pow_sub_le N C k hs0.ne' ht0.ne' ht hs
  have hY0 : 0 ≤ Y := hs0.le.trans hsY
  have htPow : t ^ k ≤ Y ^ k := pow_le_pow_left₀ ht0.le htY k
  have hsPow : s ^ k ≤ Y ^ k := pow_le_pow_left₀ hs0.le hsY k
  have hproduct : |t ^ k * s ^ k| ≤ Y ^ (2 * k) := by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg ht0.le k) (pow_nonneg hs0.le k))]
    calc
      t ^ k * s ^ k ≤ Y ^ k * Y ^ k :=
        mul_le_mul htPow hsPow (pow_nonneg hs0.le k) (pow_nonneg hY0 k)
      _ = Y ^ (2 * k) := by rw [← pow_add]; congr 1; omega
  calc
    |C| * X ^ (k - 1) * |t - s| ≤ |C| * |s ^ k - t ^ k| := hlower
    _ ≤ 2 * δ * |t ^ k * s ^ k| := hcritical
    _ ≤ 2 * δ * Y ^ (2 * k) :=
      mul_le_mul_of_nonneg_left hproduct (mul_nonneg (by positivity) hδ)

/-- Quotient form of the preceding pair-separation estimate. -/
theorem criticalSublevel_pair_dist_le
    (N C : ℝ) {k : ℕ} {X Y s t δ : ℝ}
    (hX : 0 < X) (hC : C ≠ 0)
    (hsX : X ≤ s) (hsY : s ≤ Y)
    (htX : X ≤ t) (htY : t ≤ Y) (hk : 1 ≤ k)
    (hs : |reciprocalCriticalExpression N C k s| ≤ δ)
    (ht : |reciprocalCriticalExpression N C k t| ≤ δ) :
    |t - s| ≤ 2 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1)) := by
  have hden : 0 < |C| * X ^ (k - 1) :=
    mul_pos (abs_pos.mpr hC) (pow_pos hX _)
  rw [le_div_iff₀ hden]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    criticalSublevel_pair_separation N C hX hsX hsY htX htY hk hs ht

/-- The critical sublevel set for one derivative order, restricted to the
ambient interval `[X,Y]`. -/
def reciprocalCriticalSet
    (N C : ℝ) (k : ℕ) (X Y δ : ℝ) : Set ℝ :=
  Set.Icc X Y ∩ {t | |reciprocalCriticalExpression N C k t| ≤ δ}

/-- The source-scale critical set is covered by one interval of length at
most `16 X q`.  The harmless factor two comes from centering the cover at an
arbitrary bad point rather than choosing an extremal endpoint. -/
theorem exists_short_Icc_cover_reciprocalCriticalSet
    (N C : ℝ) {k : ℕ} {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hC : C ≠ 0) (hk : 1 ≤ k)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ k ≤ 2 * X ^ k) :
    ∃ a b : ℝ,
      a ≤ b ∧
      reciprocalCriticalSet N C k X Y (|C| / X ^ k * q) ⊆ Set.Icc a b ∧
      b - a ≤ 16 * X * q := by
  by_cases hnonempty :
      (reciprocalCriticalSet N C k X Y (|C| / X ^ k * q)).Nonempty
  · obtain ⟨s, hs⟩ := hnonempty
    refine ⟨s - 8 * X * q, s + 8 * X * q, by
      have hradius : 0 ≤ 8 * X * q := by positivity
      linarith, ?_,
      by ring_nf; exact le_rfl⟩
    rintro t ht
    rcases hs with ⟨hsIcc, hsCritical⟩
    rcases ht with ⟨htIcc, htCritical⟩
    have hdist := criticalSublevel_pair_dist_le_eight_mul N C hX hC
      hsIcc.1 htIcc.1 (hpow s hsIcc) (hpow t htIcc) hk hsCritical htCritical
    have hbounds := abs_le.mp hdist
    constructor <;> linarith
  · refine ⟨0, 0, le_rfl, ?_, ?_⟩
    · simp [Set.not_nonempty_iff_eq_empty.mp hnonempty]
    · simpa only [sub_self] using
        mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 16 by norm_num) hX.le) hq

/-- Critical set attached to the normalized `r`-th derivative of the source
phase, with `M_r` and the exponent `j-1` exactly as in (expint1). -/
def reciprocalDerivativeCriticalSet
    (N M : ℝ) (j r : ℕ) (X Y q : ℝ) : Set ℝ :=
  reciprocalCriticalSet N (reciprocalPhaseHigherCoefficient M j r) (j - 1)
    X Y
    (|reciprocalPhaseHigherCoefficient M j r| / X ^ (j - 1) * q)

/-- Each derivative order in (expint1) contributes one exceptional interval
of length `O(Xq)`, with the absolute constant `16` made explicit. -/
theorem exists_short_Icc_cover_reciprocalDerivativeCriticalSet
    (N M : ℝ) {j r : ℕ} {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ∃ a b : ℝ,
      a ≤ b ∧
      reciprocalDerivativeCriticalSet N M j r X Y q ⊆ Set.Icc a b ∧
      b - a ≤ 16 * X * q := by
  unfold reciprocalDerivativeCriticalSet
  exact exists_short_Icc_cover_reciprocalCriticalSet N
    (reciprocalPhaseHigherCoefficient M j r) hX hq
    (reciprocalPhaseHigherCoefficient_ne_zero (by omega) hM) (by omega) hpow

/-- Measure form of the source-scale exceptional interval for one derivative
order. -/
theorem volume_reciprocalDerivativeCriticalSet_le
    (N M : ℝ) {j r : ℕ} {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    MeasureTheory.volume (reciprocalDerivativeCriticalSet N M j r X Y q) ≤
      ENNReal.ofReal (16 * X * q) := by
  obtain ⟨a, b, _hab, hsubset, hlength⟩ :=
    exists_short_Icc_cover_reciprocalDerivativeCriticalSet N M
      hX hq hM hj hpow
  calc
    MeasureTheory.volume (reciprocalDerivativeCriticalSet N M j r X Y q) ≤
        MeasureTheory.volume (Set.Icc a b) := MeasureTheory.measure_mono hsubset
    _ = ENNReal.ofReal (b - a) := Real.volume_Icc
    _ ≤ ENNReal.ofReal (16 * X * q) := ENNReal.ofReal_le_ofReal hlength

/-- Discrete counterpart of the exceptional-interval estimate: at most
`16Xq+1` natural-number summation points lie in one derivative-order critical
set. -/
theorem card_nat_points_reciprocalDerivativeCriticalSet_le
    (s : Finset ℕ) (N M : ℝ) {j r : ℕ} {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hs : ∀ n ∈ s,
      (n : ℝ) ∈ reciprocalDerivativeCriticalSet N M j r X Y q) :
    (s.card : ℝ) ≤ 16 * X * q + 1 := by
  obtain ⟨a, b, hab, hsubset, hlength⟩ :=
    exists_short_Icc_cover_reciprocalDerivativeCriticalSet N M
      hX hq hM hj hpow
  calc
    (s.card : ℝ) ≤ b - a + 1 :=
      card_nat_points_Icc_le s hab fun n hn => hsubset (hs n hn)
    _ ≤ 16 * X * q + 1 := by linarith

/-- Union of the critical sets for a finite collection of derivative orders. -/
def reciprocalDerivativeCriticalUnion
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) (X Y q : ℝ) : Set ℝ :=
  ⋃ r ∈ (orders : Set ℕ), reciprocalDerivativeCriticalSet N M j r X Y q

/-- Outside the finite union of critical sets, every selected derivative
order has the defining strict lower bound for its critical expression. -/
theorem abs_reciprocalCriticalExpression_gt_of_not_mem_criticalUnion
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) {X Y q t : ℝ} {r : ℕ}
    (htIcc : t ∈ Set.Icc X Y)
    (htRegular : t ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : r ∈ orders) :
    |reciprocalCriticalExpression N
        (reciprocalPhaseHigherCoefficient M j r) (j - 1) t| >
      |reciprocalPhaseHigherCoefficient M j r| / X ^ (j - 1) * q := by
  apply lt_of_not_ge
  intro hsmall
  apply htRegular
  rw [reciprocalDerivativeCriticalUnion]
  refine Set.mem_iUnion_of_mem r (Set.mem_iUnion_of_mem hr ?_)
  exact ⟨htIcc, hsmall⟩

/-- The union of the exceptional sets for `R` derivative orders has measure
at most `R` times the one-order bound.  This is the precise finite-union step
behind the source's `O(log X)` deleted intervals. -/
theorem volume_reciprocalDerivativeCriticalUnion_le
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    MeasureTheory.volume
        (reciprocalDerivativeCriticalUnion N M j orders X Y q) ≤
      (orders.card : ENNReal) * ENNReal.ofReal (16 * X * q) := by
  unfold reciprocalDerivativeCriticalUnion
  calc
    MeasureTheory.volume
        (⋃ r ∈ (orders : Set ℕ), reciprocalDerivativeCriticalSet N M j r X Y q) ≤
      ∑ r ∈ orders,
        MeasureTheory.volume (reciprocalDerivativeCriticalSet N M j r X Y q) :=
      MeasureTheory.measure_biUnion_finset_le orders _
    _ ≤ ∑ _r ∈ orders, ENNReal.ofReal (16 * X * q) := by
      exact Finset.sum_le_sum fun r _hr =>
        volume_reciprocalDerivativeCriticalSet_le N M hX hq hM hj hpow
    _ = (orders.card : ENNReal) * ENNReal.ofReal (16 * X * q) := by
      simp

/-- Discrete deletion bound for a finite family of derivative orders.  The
right side is the number of orders times the one-interval lattice-point
bound, exactly matching the source's harmless `O(log X)` loss. -/
theorem card_nat_points_reciprocalDerivativeCriticalUnion_le
    (s : Finset ℕ) (N M : ℝ) (j : ℕ) (orders : Finset ℕ) {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hs : ∀ n ∈ s,
      (n : ℝ) ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q) :
    (s.card : ℝ) ≤ (orders.card : ℝ) * (16 * X * q + 1) := by
  classical
  let pieces : ℕ → Finset ℕ := fun r =>
    s.filter fun n =>
      (n : ℝ) ∈ reciprocalDerivativeCriticalSet N M j r X Y q
  have hsubset : s ⊆ orders.biUnion pieces := by
    intro n hn
    have hnUnion := hs n hn
    rw [reciprocalDerivativeCriticalUnion] at hnUnion
    simp only [Set.mem_iUnion] at hnUnion
    obtain ⟨r, hrOrders, hrCritical⟩ := hnUnion
    rw [Finset.mem_biUnion]
    refine ⟨r, hrOrders, ?_⟩
    exact Finset.mem_filter.mpr ⟨hn, hrCritical⟩
  have hcardNat : s.card ≤ ∑ r ∈ orders, (pieces r).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hcardReal : (s.card : ℝ) ≤ ∑ r ∈ orders, ((pieces r).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (s.card : ℝ) ≤ ∑ r ∈ orders, ((pieces r).card : ℝ) := hcardReal
    _ ≤ ∑ _r ∈ orders, (16 * X * q + 1) := by
      exact Finset.sum_le_sum fun r _hr =>
        card_nat_points_reciprocalDerivativeCriticalSet_le
          (pieces r) N M hX hq hM hj hpow fun n hn =>
            (Finset.mem_filter.mp hn).2
    _ = (orders.card : ℝ) * (16 * X * q + 1) := by simp; ring

/-- The smallest closed interval of natural numbers containing a finite set.
It is empty exactly when the original set is empty. -/
noncomputable def natHull (s : Finset ℕ) : Finset ℕ := by
  classical
  exact if hs : s.Nonempty then Finset.Icc (s.min' hs) (s.max' hs) else ∅

/-- The (at most two) endpoints of `natHull s`. -/
noncomputable def natHullCuts (s : Finset ℕ) : Finset ℕ := by
  classical
  exact if hs : s.Nonempty then {s.min' hs, s.max' hs} else ∅

theorem subset_natHull (s : Finset ℕ) : s ⊆ natHull s := by
  classical
  intro n hn
  have hs : s.Nonempty := ⟨n, hn⟩
  simp only [natHull, dif_pos hs, Finset.mem_Icc]
  exact ⟨s.min'_le n hn, s.le_max' n hn⟩

theorem natHullCuts_subset_natHull (s : Finset ℕ) :
    natHullCuts s ⊆ natHull s := by
  classical
  by_cases hs : s.Nonempty
  · simp only [natHullCuts, natHull, dif_pos hs]
    intro n hn
    rw [Finset.mem_insert, Finset.mem_singleton] at hn
    rw [Finset.mem_Icc]
    rcases hn with rfl | rfl
    · exact ⟨le_rfl, s.min'_le _ (s.max'_mem hs)⟩
    · exact ⟨s.min'_le _ (s.max'_mem hs), le_rfl⟩
  · simp [natHullCuts, natHull, hs]

theorem card_natHullCuts_le_two (s : Finset ℕ) :
    (natHullCuts s).card ≤ 2 := by
  classical
  by_cases hs : s.Nonempty
  · rw [natHullCuts, dif_pos hs]
    exact Finset.card_insert_le _ _
  · simp [natHullCuts, hs]

/-- A natural interval avoiding the endpoints of an interval hull cannot
cross its boundary: it is either entirely in the hull or disjoint from it. -/
theorem natHull_all_or_disjoint_of_disjoint_cuts
    (s : Finset ℕ) {a b : ℕ}
    (hcuts : Disjoint (Finset.Ico a b) (natHullCuts s)) :
    (∀ n ∈ Finset.Ico a b, n ∈ natHull s) ∨
      Disjoint (Finset.Ico a b) (natHull s) := by
  classical
  by_cases hs : s.Nonempty
  · let lo := s.min' hs
    let hi := s.max' hs
    have hloCut : lo ∈ natHullCuts s := by
      simp [natHullCuts, hs, lo]
    have hhiCut : hi ∈ natHullCuts s := by
      simp [natHullCuts, hs, hi]
    rw [Finset.disjoint_left] at hcuts
    by_cases hmeet : ∃ n, n ∈ Finset.Ico a b ∧ n ∈ natHull s
    · left
      obtain ⟨n, hnIco, hnHull⟩ := hmeet
      have hnBounds : lo ≤ n ∧ n ≤ hi := by
        simpa [natHull, hs, lo, hi] using hnHull
      intro m hmIco
      have hmBounds : lo ≤ m ∧ m ≤ hi := by
        constructor
        · by_contra hm
          have hmlo : m < lo := Nat.lt_of_not_ge hm
          have hloIco : lo ∈ Finset.Ico a b := Finset.mem_Ico.mpr
            ⟨(Finset.mem_Ico.mp hmIco).1.trans hmlo.le,
              hnBounds.1.trans_lt (Finset.mem_Ico.mp hnIco).2⟩
          exact hcuts hloIco hloCut
        · by_contra hm
          have hhim : hi < m := Nat.lt_of_not_ge hm
          have hhiIco : hi ∈ Finset.Ico a b := Finset.mem_Ico.mpr
            ⟨(Finset.mem_Ico.mp hnIco).1.trans hnBounds.2,
              hhim.trans (Finset.mem_Ico.mp hmIco).2⟩
          exact hcuts hhiIco hhiCut
      simpa [natHull, hs, lo, hi] using hmBounds
    · right
      rw [Finset.disjoint_left]
      intro n hnIco hnHull
      exact hmeet ⟨n, hnIco, hnHull⟩
  · right
    simp [natHull, hs]

/-- Integer starts whose forward real window of length `R` meets at least one
selected critical set.  Deleting these starts supplies the expanded margins
needed by finite differencing. -/
def reciprocalDerivativeExpandedCriticalNatPoints
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ)
    (X Y q : ℝ) (R : ℕ) : Finset ℕ := by
  classical
  exact ambient.filter fun n => ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
    t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q

@[simp]
theorem mem_reciprocalDerivativeExpandedCriticalNatPoints
    {ambient orders : Finset ℕ} {N M : ℝ} {j : ℕ}
    {X Y q : ℝ} {R n : ℕ} :
    n ∈ reciprocalDerivativeExpandedCriticalNatPoints
        ambient orders N M j X Y q R ↔
      n ∈ ambient ∧ ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
        t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q := by
  classical
  simp [reciprocalDerivativeExpandedCriticalNatPoints]

/-- One derivative order creates at most `16Xq + R + 1` integer starts whose
forward `R`-window can meet its critical interval. -/
theorem card_nat_points_expanded_reciprocalDerivativeCriticalSet_le
    (s : Finset ℕ) (N M : ℝ) {j r R : ℕ} {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hs : ∀ n ∈ s, ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
      t ∈ reciprocalDerivativeCriticalSet N M j r X Y q) :
    (s.card : ℝ) ≤ 16 * X * q + R + 1 := by
  obtain ⟨u, v, huv, hsubset, hlength⟩ :=
    exists_short_Icc_cover_reciprocalDerivativeCriticalSet N M
      hX hq hM hj hpow (r := r)
  have hR : (0 : ℝ) ≤ R := by positivity
  have huvExpanded : u - (R : ℝ) ≤ v := by linarith
  calc
    (s.card : ℝ) ≤ v - (u - (R : ℝ)) + 1 :=
      card_nat_points_Icc_le s huvExpanded fun n hn => by
        obtain ⟨t, htWindow, htCritical⟩ := hs n hn
        have htCover := hsubset htCritical
        norm_num only [Nat.cast_add] at htWindow
        rcases htWindow with ⟨hnt, htR⟩
        rcases htCover with ⟨hut, htv⟩
        constructor <;> linarith
    _ ≤ 16 * X * q + R + 1 := by linarith

/-- Expanded critical starts belonging to one fixed derivative order. -/
noncomputable def reciprocalDerivativeExpandedCriticalNatPointsForOrder
    (ambient : Finset ℕ) (N M : ℝ) (j r : ℕ)
    (X Y q : ℝ) (R : ℕ) : Finset ℕ := by
  classical
  exact ambient.filter fun n => ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
    t ∈ reciprocalDerivativeCriticalSet N M j r X Y q

@[simp]
theorem mem_reciprocalDerivativeExpandedCriticalNatPointsForOrder
    {ambient : Finset ℕ} {N M : ℝ} {j r : ℕ}
    {X Y q : ℝ} {R n : ℕ} :
    n ∈ reciprocalDerivativeExpandedCriticalNatPointsForOrder
        ambient N M j r X Y q R ↔
      n ∈ ambient ∧ ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
        t ∈ reciprocalDerivativeCriticalSet N M j r X Y q := by
  classical
  simp [reciprocalDerivativeExpandedCriticalNatPointsForOrder]

/-- Taking the integer interval hull of one order's expanded bad starts does
not increase the source-scale cardinality bound. -/
theorem card_natHull_reciprocalDerivativeExpandedCriticalNatPointsForOrder_le
    (ambient : Finset ℕ) (N M : ℝ) {j r R : ℕ} {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ((natHull (reciprocalDerivativeExpandedCriticalNatPointsForOrder
        ambient N M j r X Y q R)).card : ℝ) ≤
      16 * X * q + R + 1 := by
  classical
  let s := reciprocalDerivativeExpandedCriticalNatPointsForOrder
    ambient N M j r X Y q R
  by_cases hs : s.Nonempty
  · obtain ⟨u, v, huv, hcover, hlength⟩ :=
      exists_short_Icc_cover_reciprocalDerivativeCriticalSet N M
        hX hq hM hj hpow (r := r)
    have hloMem : s.min' hs ∈ s := s.min'_mem hs
    have hhiMem : s.max' hs ∈ s := s.max'_mem hs
    obtain ⟨tlo, htloWindow, htloCritical⟩ :=
      (mem_reciprocalDerivativeExpandedCriticalNatPointsForOrder.mp hloMem).2
    obtain ⟨thi, hthiWindow, hthiCritical⟩ :=
      (mem_reciprocalDerivativeExpandedCriticalNatPointsForOrder.mp hhiMem).2
    have htloCover := hcover htloCritical
    have hthiCover := hcover hthiCritical
    have hR : (0 : ℝ) ≤ R := by positivity
    have huvExpanded : u - (R : ℝ) ≤ v := by linarith
    calc
      ((natHull s).card : ℝ) ≤ v - (u - (R : ℝ)) + 1 :=
        card_nat_points_Icc_le (natHull s) huvExpanded fun n hn => by
          have hnBounds : s.min' hs ≤ n ∧ n ≤ s.max' hs := by
            simpa [natHull, hs] using hn
          norm_num only [Nat.cast_add] at htloWindow hthiWindow
          constructor
          · have hnlo : ((s.min' hs : ℕ) : ℝ) ≤ n := by
              exact_mod_cast hnBounds.1
            linarith [htloWindow.2, htloCover.1]
          · have hnhi : (n : ℝ) ≤ s.max' hs := by
              exact_mod_cast hnBounds.2
            linarith [hthiWindow.1, hthiCover.2]
      _ ≤ 16 * X * q + R + 1 := by linarith
  · simp [natHull, s, hs]
    positivity

/-- Union of the integer interval hulls of the expanded bad starts for each
selected derivative order. -/
noncomputable def reciprocalDerivativeExpandedCriticalHullNatPoints
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ)
    (X Y q : ℝ) (R : ℕ) : Finset ℕ := by
  classical
  exact orders.biUnion fun r => natHull
    (reciprocalDerivativeExpandedCriticalNatPointsForOrder
      ambient N M j r X Y q R)

/-- The endpoint cut set for the per-order expanded critical hulls. -/
noncomputable def reciprocalDerivativeExpandedCriticalHullCuts
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ)
    (X Y q : ℝ) (R : ℕ) : Finset ℕ := by
  classical
  exact orders.biUnion fun r => natHullCuts
    (reciprocalDerivativeExpandedCriticalNatPointsForOrder
      ambient N M j r X Y q R)

theorem reciprocalDerivativeExpandedCriticalNatPoints_subset_hulls
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ)
    (X Y q : ℝ) (R : ℕ) :
    reciprocalDerivativeExpandedCriticalNatPoints
        ambient orders N M j X Y q R ⊆
      reciprocalDerivativeExpandedCriticalHullNatPoints
        ambient orders N M j X Y q R := by
  classical
  intro n hn
  obtain ⟨hnAmbient, t, htWindow, htUnion⟩ :=
    mem_reciprocalDerivativeExpandedCriticalNatPoints.mp hn
  rw [reciprocalDerivativeCriticalUnion] at htUnion
  simp only [Set.mem_iUnion] at htUnion
  obtain ⟨r, hrOrders, hrCritical⟩ := htUnion
  rw [reciprocalDerivativeExpandedCriticalHullNatPoints, Finset.mem_biUnion]
  refine ⟨r, hrOrders, subset_natHull _ ?_⟩
  exact mem_reciprocalDerivativeExpandedCriticalNatPointsForOrder.mpr
    ⟨hnAmbient, t, htWindow, hrCritical⟩

theorem reciprocalDerivativeExpandedCriticalHullCuts_subset_hulls
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ)
    (X Y q : ℝ) (R : ℕ) :
    reciprocalDerivativeExpandedCriticalHullCuts
        ambient orders N M j X Y q R ⊆
      reciprocalDerivativeExpandedCriticalHullNatPoints
        ambient orders N M j X Y q R := by
  classical
  intro n hn
  rw [reciprocalDerivativeExpandedCriticalHullCuts,
    Finset.mem_biUnion] at hn
  obtain ⟨r, hrOrders, hnCut⟩ := hn
  rw [reciprocalDerivativeExpandedCriticalHullNatPoints,
    Finset.mem_biUnion]
  exact ⟨r, hrOrders, natHullCuts_subset_natHull _ hnCut⟩

/-- There are at most two component cuts per selected derivative order. -/
theorem card_reciprocalDerivativeExpandedCriticalHullCuts_le
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ)
    (X Y q : ℝ) (R : ℕ) :
    (reciprocalDerivativeExpandedCriticalHullCuts
      ambient orders N M j X Y q R).card ≤ 2 * orders.card := by
  classical
  calc
    (reciprocalDerivativeExpandedCriticalHullCuts
        ambient orders N M j X Y q R).card ≤
        ∑ r ∈ orders, (natHullCuts
          (reciprocalDerivativeExpandedCriticalNatPointsForOrder
            ambient N M j r X Y q R)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ orders, 2 := by
      exact Finset.sum_le_sum fun r _hr => card_natHullCuts_le_two _
    _ = 2 * orders.card := by simp [mul_comm]

/-- Filling the holes in each order's expanded bad-start set preserves the
same total source-scale deletion bound. -/
theorem card_reciprocalDerivativeExpandedCriticalHullNatPoints_le
    (ambient orders : Finset ℕ) (N M : ℝ) (j R : ℕ) {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ((reciprocalDerivativeExpandedCriticalHullNatPoints
        ambient orders N M j X Y q R).card : ℝ) ≤
      (orders.card : ℝ) * (16 * X * q + R + 1) := by
  classical
  have hcardNat :
      (reciprocalDerivativeExpandedCriticalHullNatPoints
          ambient orders N M j X Y q R).card ≤
        ∑ r ∈ orders, (natHull
          (reciprocalDerivativeExpandedCriticalNatPointsForOrder
            ambient N M j r X Y q R)).card := by
    exact Finset.card_biUnion_le
  have hcardReal :
      ((reciprocalDerivativeExpandedCriticalHullNatPoints
          ambient orders N M j X Y q R).card : ℝ) ≤
        ∑ r ∈ orders, ((natHull
          (reciprocalDerivativeExpandedCriticalNatPointsForOrder
            ambient N M j r X Y q R)).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((reciprocalDerivativeExpandedCriticalHullNatPoints
        ambient orders N M j X Y q R).card : ℝ) ≤
        ∑ r ∈ orders, ((natHull
          (reciprocalDerivativeExpandedCriticalNatPointsForOrder
            ambient N M j r X Y q R)).card : ℝ) := hcardReal
    _ ≤ ∑ _r ∈ orders, (16 * X * q + R + 1) := by
      exact Finset.sum_le_sum fun r _hr =>
        card_natHull_reciprocalDerivativeExpandedCriticalNatPointsForOrder_le
          ambient N M hX hq hM hj hpow
    _ = (orders.card : ℝ) * (16 * X * q + R + 1) := by simp; ring

/-- An integer interval avoiding every hull endpoint is either wholly
deleted by one selected order or disjoint from all expanded critical hulls.
-/
theorem all_mem_reciprocalDerivativeExpandedCriticalHulls_or_disjoint_of_disjoint_cuts
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ)
    (X Y q : ℝ) (R : ℕ) {a b : ℕ}
    (hcuts : Disjoint (Finset.Ico a b)
      (reciprocalDerivativeExpandedCriticalHullCuts
        ambient orders N M j X Y q R)) :
    (∀ n ∈ Finset.Ico a b,
        n ∈ reciprocalDerivativeExpandedCriticalHullNatPoints
          ambient orders N M j X Y q R) ∨
      Disjoint (Finset.Ico a b)
        (reciprocalDerivativeExpandedCriticalHullNatPoints
          ambient orders N M j X Y q R) := by
  classical
  by_cases hmeet : ∃ r ∈ orders, ∃ n,
      n ∈ Finset.Ico a b ∧
      n ∈ natHull (reciprocalDerivativeExpandedCriticalNatPointsForOrder
        ambient N M j r X Y q R)
  · obtain ⟨r, hrOrders, n, hnIco, hnHull⟩ := hmeet
    have hcutsOrder : Disjoint (Finset.Ico a b)
        (natHullCuts (reciprocalDerivativeExpandedCriticalNatPointsForOrder
          ambient N M j r X Y q R)) := by
      rw [Finset.disjoint_left] at hcuts ⊢
      intro m hmIco hmCut
      apply hcuts hmIco
      rw [reciprocalDerivativeExpandedCriticalHullCuts,
        Finset.mem_biUnion]
      exact ⟨r, hrOrders, hmCut⟩
    rcases natHull_all_or_disjoint_of_disjoint_cuts _ hcutsOrder with
      hall | hdisj
    · left
      intro m hmIco
      rw [reciprocalDerivativeExpandedCriticalHullNatPoints,
        Finset.mem_biUnion]
      exact ⟨r, hrOrders, hall m hmIco⟩
    · exfalso
      rw [Finset.disjoint_left] at hdisj
      exact hdisj hnIco hnHull
  · right
    rw [Finset.disjoint_left]
    intro n hnIco hnHulls
    rw [reciprocalDerivativeExpandedCriticalHullNatPoints,
      Finset.mem_biUnion] at hnHulls
    obtain ⟨r, hrOrders, hnHull⟩ := hnHulls
    exact hmeet ⟨r, hrOrders, n, hnIco, hnHull⟩

/-- Expanded-margin deletion bound for a finite family of derivative orders.
-/
theorem card_reciprocalDerivativeExpandedCriticalNatPoints_le
    (ambient orders : Finset ℕ) (N M : ℝ) (j R : ℕ) {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ((reciprocalDerivativeExpandedCriticalNatPoints
        ambient orders N M j X Y q R).card : ℝ) ≤
      (orders.card : ℝ) * (16 * X * q + R + 1) := by
  classical
  let s := reciprocalDerivativeExpandedCriticalNatPoints
    ambient orders N M j X Y q R
  let pieces : ℕ → Finset ℕ := fun r =>
    s.filter fun n => ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
      t ∈ reciprocalDerivativeCriticalSet N M j r X Y q
  have hsubsetPieces : s ⊆ orders.biUnion pieces := by
    intro n hn
    have hnExpanded :=
      mem_reciprocalDerivativeExpandedCriticalNatPoints.mp hn
    obtain ⟨t, htWindow, htUnion⟩ := hnExpanded.2
    rw [reciprocalDerivativeCriticalUnion] at htUnion
    simp only [Set.mem_iUnion] at htUnion
    obtain ⟨r, hrOrders, hrCritical⟩ := htUnion
    rw [Finset.mem_biUnion]
    exact ⟨r, hrOrders, Finset.mem_filter.mpr
      ⟨hn, t, htWindow, hrCritical⟩⟩
  have hcardNat : s.card ≤ ∑ r ∈ orders, (pieces r).card :=
    (Finset.card_le_card hsubsetPieces).trans Finset.card_biUnion_le
  have hcardReal : (s.card : ℝ) ≤
      ∑ r ∈ orders, ((pieces r).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (s.card : ℝ) ≤ ∑ r ∈ orders, ((pieces r).card : ℝ) := hcardReal
    _ ≤ ∑ _r ∈ orders, (16 * X * q + R + 1) := by
      exact Finset.sum_le_sum fun r _hr =>
        card_nat_points_expanded_reciprocalDerivativeCriticalSet_le
          (pieces r) N M hX hq hM hj hpow fun n hn =>
            (Finset.mem_filter.mp hn).2
    _ = (orders.card : ℝ) * (16 * X * q + R + 1) := by simp; ring

/-- Complement of the expanded critical starts inside an ambient finite set.
-/
def reciprocalDerivativeExpandedRegularNatPoints
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ)
    (X Y q : ℝ) (R : ℕ) : Finset ℕ := by
  classical
  exact ambient.filter fun n => ¬ ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
    t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q

/-- Exact partition into starts whose forward `R`-window meets the critical
union and starts whose whole window is regular. -/
theorem reciprocalPhaseSum_eq_expandedCritical_add_regular
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ) (X Y q : ℝ) (R : ℕ) :
    (∑ n ∈ ambient,
      standardAdditiveCharacter (reciprocalPhase N M j n)) =
      (∑ n ∈ reciprocalDerivativeExpandedCriticalNatPoints
          ambient orders N M j X Y q R,
        standardAdditiveCharacter (reciprocalPhase N M j n)) +
      ∑ n ∈ reciprocalDerivativeExpandedRegularNatPoints
          ambient orders N M j X Y q R,
        standardAdditiveCharacter (reciprocalPhase N M j n) := by
  classical
  simpa [reciprocalDerivativeExpandedCriticalNatPoints,
    reciprocalDerivativeExpandedRegularNatPoints] using
    (Finset.sum_filter_add_sum_filter_not ambient
      (fun n => ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
        t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q)
      (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))).symm

/-- Unit-modulus bound for the phase contribution of all expanded critical
starts. -/
theorem norm_reciprocalPhaseSum_expandedCriticalNatPoints_le
    (ambient orders : Finset ℕ) (N M : ℝ) (j R : ℕ) {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ‖∑ n ∈ reciprocalDerivativeExpandedCriticalNatPoints
        ambient orders N M j X Y q R,
      standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      (orders.card : ℝ) * (16 * X * q + R + 1) := by
  calc
    ‖∑ n ∈ reciprocalDerivativeExpandedCriticalNatPoints
        ambient orders N M j X Y q R,
      standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      ∑ n ∈ reciprocalDerivativeExpandedCriticalNatPoints
        ambient orders N M j X Y q R,
        ‖standardAdditiveCharacter (reciprocalPhase N M j n)‖ :=
      norm_sum_le _ _
    _ = ((reciprocalDerivativeExpandedCriticalNatPoints
        ambient orders N M j X Y q R).card : ℝ) := by simp
    _ ≤ (orders.card : ℝ) * (16 * X * q + R + 1) :=
      card_reciprocalDerivativeExpandedCriticalNatPoints_le
        ambient orders N M j R hX hq hM hj hpow

/-- Natural summation points from an ambient finite interval which lie in at
least one selected derivative-order critical set. -/
noncomputable def reciprocalDerivativeCriticalNatPoints
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ) (X Y q : ℝ) : Finset ℕ := by
  classical
  exact ambient.filter fun n =>
    (n : ℝ) ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q

@[simp]
theorem mem_reciprocalDerivativeCriticalNatPoints
    {ambient orders : Finset ℕ} {N M : ℝ} {j : ℕ} {X Y q : ℝ} {n : ℕ} :
    n ∈ reciprocalDerivativeCriticalNatPoints ambient orders N M j X Y q ↔
      n ∈ ambient ∧
      (n : ℝ) ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q := by
  classical
  simp [reciprocalDerivativeCriticalNatPoints]

/-- The total reciprocal-phase contribution of all deleted integer points is
bounded by their exact finite-union lattice count. -/
theorem norm_reciprocalPhaseSum_criticalNatPoints_le
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ) {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ‖∑ n ∈ reciprocalDerivativeCriticalNatPoints ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      (orders.card : ℝ) * (16 * X * q + 1) := by
  calc
    ‖∑ n ∈ reciprocalDerivativeCriticalNatPoints ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      ∑ n ∈ reciprocalDerivativeCriticalNatPoints ambient orders N M j X Y q,
        ‖standardAdditiveCharacter (reciprocalPhase N M j n)‖ := by
      exact norm_sum_le _ _
    _ =
      ((reciprocalDerivativeCriticalNatPoints ambient orders N M j X Y q).card : ℝ) :=
      by simp
    _ ≤ (orders.card : ℝ) * (16 * X * q + 1) :=
      card_nat_points_reciprocalDerivativeCriticalUnion_le
        (reciprocalDerivativeCriticalNatPoints ambient orders N M j X Y q)
        N M j orders hX hq hM hj hpow fun n hn =>
          (mem_reciprocalDerivativeCriticalNatPoints.mp hn).2

/-- Complementary summation points on which none of the selected derivative
orders is critical. -/
noncomputable def reciprocalDerivativeRegularNatPoints
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ) (X Y q : ℝ) : Finset ℕ := by
  classical
  exact ambient.filter fun n =>
    (n : ℝ) ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q

/-- A finite interval with some bad points deleted is a disjoint union of at
most `bad.card + 1` consecutive good intervals.  This norm formulation avoids
choosing or sorting the components: the proof recursively splits at a bad
point and accounts for the two subintervals and their bad-point cards exactly.
-/
theorem norm_sum_filter_Ico_le_badCard_add_one_mul_of_subinterval
    {E : Type*} [NormedAddCommGroup E]
    (z : ℕ → E) (P : ℕ → Prop) [DecidablePred P]
    (a₀ b₀ : ℕ) {B : ℝ}
    (hinterval : ∀ a b : ℕ, a₀ ≤ a → b ≤ b₀ →
      (∀ n ∈ Finset.Ico a b, P n) →
      ‖∑ n ∈ Finset.Ico a b, z n‖ ≤ B) :
    ∀ a b : ℕ, a₀ ≤ a → b ≤ b₀ →
      ‖∑ n ∈ (Finset.Ico a b).filter P, z n‖ ≤
        (((Finset.Ico a b).filter (fun n => ¬ P n)).card + 1) * B := by
  intro a b ha hb
  generalize hd : b - a = d
  induction d using Nat.strong_induction_on generalizing a b with
  | h d ih =>
      let bad := (Finset.Ico a b).filter (fun n => ¬ P n)
      by_cases hbad : bad.Nonempty
      · obtain ⟨c, hc⟩ := hbad
        have hcIco : c ∈ Finset.Ico a b := (Finset.mem_filter.mp hc).1
        have hcNot : ¬ P c := (Finset.mem_filter.mp hc).2
        have hac : a ≤ c := (Finset.mem_Ico.mp hcIco).1
        have hcb : c < b := (Finset.mem_Ico.mp hcIco).2
        have hleftLen : c - a < d := by omega
        have hrightLen : b - (c + 1) < d := by omega
        have hleft := ih (c - a) hleftLen a c ha (hcb.le.trans hb)
        have hright := ih (b - (c + 1)) hrightLen (c + 1) b
          (ha.trans (hac.trans (Nat.le_succ c))) hb
        let left := (Finset.Ico a c).filter P
        let right := (Finset.Ico (c + 1) b).filter P
        let badLeft := (Finset.Ico a c).filter (fun n => ¬ P n)
        let badRight := (Finset.Ico (c + 1) b).filter (fun n => ¬ P n)
        have hreg : (Finset.Ico a b).filter P = left ∪ right := by
          ext n
          simp only [left, right, Finset.mem_filter, Finset.mem_Ico,
            Finset.mem_union]
          constructor
          · rintro ⟨⟨han, hnb⟩, hnP⟩
            by_cases hnc : n < c
            · exact Or.inl ⟨⟨han, hnc⟩, hnP⟩
            · right
              have hne : n ≠ c := by
                intro hncEq
                exact hcNot (hncEq ▸ hnP)
              have hcn : c + 1 ≤ n := by omega
              exact ⟨⟨hcn, hnb⟩, hnP⟩
          · rintro (⟨⟨han, hnc⟩, hnP⟩ | ⟨⟨hcn, hnb⟩, hnP⟩)
            · exact ⟨⟨han, hnc.trans hcb⟩, hnP⟩
            · exact ⟨⟨hac.trans (by omega), hnb⟩, hnP⟩
        have hdisj : Disjoint left right := by
          rw [Finset.disjoint_left]
          intro n hnleft hnright
          have hnl : n < c :=
            (Finset.mem_Ico.mp (Finset.mem_filter.mp hnleft).1).2
          have hnr : c + 1 ≤ n :=
            (Finset.mem_Ico.mp (Finset.mem_filter.mp hnright).1).1
          omega
        have hbadSplit : bad = (badLeft ∪ {c}) ∪ badRight := by
          ext n
          simp only [bad, badLeft, badRight, Finset.mem_filter,
            Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨han, hnb⟩, hnNot⟩
            rcases lt_trichotomy n c with hnc | rfl | hcn
            · exact Or.inl (Or.inl ⟨⟨han, hnc⟩, hnNot⟩)
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨⟨by omega, hnb⟩, hnNot⟩
          · rintro ((⟨⟨han, hnc⟩, hnNot⟩ | rfl) |
              ⟨⟨hcn, hnb⟩, hnNot⟩)
            · exact ⟨⟨han, hnc.trans hcb⟩, hnNot⟩
            · exact ⟨Finset.mem_Ico.mp hcIco, hcNot⟩
            · exact ⟨⟨hac.trans (by omega), hnb⟩, hnNot⟩
        have hcNotBadLeft : c ∉ badLeft := by
          simp [badLeft]
        have hdisjBadRight : Disjoint (badLeft ∪ {c}) badRight := by
          rw [Finset.disjoint_left]
          intro n hnleft hnright
          have hnr : c + 1 ≤ n :=
            (Finset.mem_Ico.mp (Finset.mem_filter.mp hnright).1).1
          rcases Finset.mem_union.mp hnleft with hnl | hncSingleton
          · have hnc : n < c :=
              (Finset.mem_Ico.mp (Finset.mem_filter.mp hnl).1).2
            omega
          · have hnc : n = c := Finset.mem_singleton.mp hncSingleton
            omega
        have hcard : bad.card = badLeft.card + 1 + badRight.card := by
          rw [hbadSplit, Finset.card_union_of_disjoint hdisjBadRight,
            Finset.card_union_of_disjoint]
          · simp
          · simp [Finset.disjoint_singleton_right, hcNotBadLeft]
        calc
          ‖∑ x ∈ (Finset.Ico a b).filter P, z x‖ =
              ‖(∑ x ∈ left, z x) + ∑ x ∈ right, z x‖ := by
                rw [hreg, Finset.sum_union hdisj]
          _ ≤ ‖∑ x ∈ left, z x‖ + ‖∑ x ∈ right, z x‖ := norm_add_le _ _
          _ ≤ (badLeft.card + 1) * B + (badRight.card + 1) * B := by
            exact add_le_add (by simpa [left, badLeft] using hleft)
              (by simpa [right, badRight] using hright)
          _ = (bad.card + 1) * B := by rw [hcard]; push_cast; ring
      · have hall : ∀ n ∈ Finset.Ico a b, P n := by
          intro n hn
          by_contra hnP
          exact hbad ⟨n, Finset.mem_filter.mpr ⟨hn, hnP⟩⟩
        have hfilter : (Finset.Ico a b).filter P = Finset.Ico a b := by
          apply Finset.filter_eq_self.mpr
          exact hall
        have hbadCard : bad.card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.not_nonempty_iff_eq_empty.mp
          exact hbad
        rw [hfilter,
          show ((Finset.Ico a b).filter (fun n => ¬ P n)).card = 0 from hbadCard]
        simpa using hinterval a b ha hb hall

/-- Global-hypothesis form of
`norm_sum_filter_Ico_le_badCard_add_one_mul_of_subinterval`. -/
theorem norm_sum_filter_Ico_le_badCard_add_one_mul
    {E : Type*} [NormedAddCommGroup E]
    (z : ℕ → E) (P : ℕ → Prop) [DecidablePred P]
    {B : ℝ}
    (hinterval : ∀ a b : ℕ, (∀ n ∈ Finset.Ico a b, P n) →
      ‖∑ n ∈ Finset.Ico a b, z n‖ ≤ B) :
    ∀ a b : ℕ,
      ‖∑ n ∈ (Finset.Ico a b).filter P, z n‖ ≤
        (((Finset.Ico a b).filter (fun n => ¬ P n)).card + 1) * B := by
  intro a b
  exact norm_sum_filter_Ico_le_badCard_add_one_mul_of_subinterval
    z P a b (fun c d _ _ hregular => hinterval c d hregular)
      a b le_rfl le_rfl

/-- Split only at a prescribed finite cut set.  If every cut is bad and each
cut-free piece has norm at most `B`, the filtered sum costs exactly one copy of
`B` per local cut plus one. -/
theorem norm_sum_filter_Ico_le_cutCard_add_one_mul_of_subinterval
    {E : Type*} [NormedAddCommGroup E]
    (z : ℕ → E) (P : ℕ → Prop) [DecidablePred P]
    (cuts : Finset ℕ) (a₀ b₀ : ℕ) {B : ℝ}
    (hcutBad : ∀ n ∈ cuts, ¬ P n)
    (hpiece : ∀ a b : ℕ, a₀ ≤ a → b ≤ b₀ →
      Disjoint (Finset.Ico a b) cuts →
      ‖∑ n ∈ (Finset.Ico a b).filter P, z n‖ ≤ B) :
    ∀ a b : ℕ, a₀ ≤ a → b ≤ b₀ →
      ‖∑ n ∈ (Finset.Ico a b).filter P, z n‖ ≤
        (((Finset.Ico a b).filter (fun n => n ∈ cuts)).card + 1) * B := by
  intro a b ha hb
  generalize hd : b - a = d
  induction d using Nat.strong_induction_on generalizing a b with
  | h d ih =>
      let localCuts := (Finset.Ico a b).filter (fun n => n ∈ cuts)
      by_cases hcuts : localCuts.Nonempty
      · obtain ⟨c, hc⟩ := hcuts
        have hcIco : c ∈ Finset.Ico a b := (Finset.mem_filter.mp hc).1
        have hcCut : c ∈ cuts := (Finset.mem_filter.mp hc).2
        have hcNot : ¬ P c := hcutBad c hcCut
        have hac : a ≤ c := (Finset.mem_Ico.mp hcIco).1
        have hcb : c < b := (Finset.mem_Ico.mp hcIco).2
        have hleftLen : c - a < d := by omega
        have hrightLen : b - (c + 1) < d := by omega
        have hleft := ih (c - a) hleftLen a c ha (hcb.le.trans hb)
        have hright := ih (b - (c + 1)) hrightLen (c + 1) b
          (ha.trans (hac.trans (Nat.le_succ c))) hb
        let left := (Finset.Ico a c).filter P
        let right := (Finset.Ico (c + 1) b).filter P
        let cutsLeft := (Finset.Ico a c).filter (fun n => n ∈ cuts)
        let cutsRight := (Finset.Ico (c + 1) b).filter (fun n => n ∈ cuts)
        have hreg : (Finset.Ico a b).filter P = left ∪ right := by
          ext n
          simp only [left, right, Finset.mem_filter, Finset.mem_Ico,
            Finset.mem_union]
          constructor
          · rintro ⟨⟨han, hnb⟩, hnP⟩
            by_cases hnc : n < c
            · exact Or.inl ⟨⟨han, hnc⟩, hnP⟩
            · right
              have hne : n ≠ c := by
                intro hncEq
                exact hcNot (hncEq ▸ hnP)
              exact ⟨⟨by omega, hnb⟩, hnP⟩
          · rintro (⟨⟨han, hnc⟩, hnP⟩ | ⟨⟨hcn, hnb⟩, hnP⟩)
            · exact ⟨⟨han, hnc.trans hcb⟩, hnP⟩
            · exact ⟨⟨hac.trans (by omega), hnb⟩, hnP⟩
        have hdisj : Disjoint left right := by
          rw [Finset.disjoint_left]
          intro n hnleft hnright
          have hnl : n < c :=
            (Finset.mem_Ico.mp (Finset.mem_filter.mp hnleft).1).2
          have hnr : c + 1 ≤ n :=
            (Finset.mem_Ico.mp (Finset.mem_filter.mp hnright).1).1
          omega
        have hcutsSplit : localCuts = (cutsLeft ∪ {c}) ∪ cutsRight := by
          ext n
          simp only [localCuts, cutsLeft, cutsRight, Finset.mem_filter,
            Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨han, hnb⟩, hnCut⟩
            rcases lt_trichotomy n c with hnc | rfl | hcn
            · exact Or.inl (Or.inl ⟨⟨han, hnc⟩, hnCut⟩)
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨⟨by omega, hnb⟩, hnCut⟩
          · rintro ((⟨⟨han, hnc⟩, hnCut⟩ | rfl) |
              ⟨⟨hcn, hnb⟩, hnCut⟩)
            · exact ⟨⟨han, hnc.trans hcb⟩, hnCut⟩
            · exact ⟨Finset.mem_Ico.mp hcIco, hcCut⟩
            · exact ⟨⟨hac.trans (by omega), hnb⟩, hnCut⟩
        have hcNotCutsLeft : c ∉ cutsLeft := by simp [cutsLeft]
        have hdisjCutsRight : Disjoint (cutsLeft ∪ {c}) cutsRight := by
          rw [Finset.disjoint_left]
          intro n hnleft hnright
          have hnr : c + 1 ≤ n :=
            (Finset.mem_Ico.mp (Finset.mem_filter.mp hnright).1).1
          rcases Finset.mem_union.mp hnleft with hnl | hncSingleton
          · have hnc : n < c :=
              (Finset.mem_Ico.mp (Finset.mem_filter.mp hnl).1).2
            omega
          · have hnc : n = c := Finset.mem_singleton.mp hncSingleton
            omega
        have hcard : localCuts.card = cutsLeft.card + 1 + cutsRight.card := by
          rw [hcutsSplit, Finset.card_union_of_disjoint hdisjCutsRight,
            Finset.card_union_of_disjoint]
          · simp
          · simp [Finset.disjoint_singleton_right, hcNotCutsLeft]
        calc
          ‖∑ x ∈ (Finset.Ico a b).filter P, z x‖ =
              ‖(∑ x ∈ left, z x) + ∑ x ∈ right, z x‖ := by
                rw [hreg, Finset.sum_union hdisj]
          _ ≤ ‖∑ x ∈ left, z x‖ + ‖∑ x ∈ right, z x‖ := norm_add_le _ _
          _ ≤ (cutsLeft.card + 1) * B + (cutsRight.card + 1) * B := by
            exact add_le_add (by simpa [left, cutsLeft] using hleft)
              (by simpa [right, cutsRight] using hright)
          _ = (localCuts.card + 1) * B := by rw [hcard]; push_cast; ring
      · have hdisjCuts : Disjoint (Finset.Ico a b) cuts := by
          rw [Finset.disjoint_left]
          intro n hnIco hnCut
          exact hcuts ⟨n, Finset.mem_filter.mpr ⟨hnIco, hnCut⟩⟩
        have hcard : localCuts.card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.not_nonempty_iff_eq_empty.mp
          exact hcuts
        rw [show ((Finset.Ico a b).filter (fun n => n ∈ cuts)).card = 0 from hcard]
        simpa using hpiece a b ha hb hdisjCuts

/-- Global-cardinality corollary of the cut-set component decomposition. -/
theorem norm_sum_filter_Ico_le_cutsCard_add_one_mul
    {E : Type*} [NormedAddCommGroup E]
    (z : ℕ → E) (P : ℕ → Prop) [DecidablePred P]
    (cuts : Finset ℕ) (a b : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hcutBad : ∀ n ∈ cuts, ¬ P n)
    (hpiece : ∀ c d : ℕ, a ≤ c → d ≤ b →
      Disjoint (Finset.Ico c d) cuts →
      ‖∑ n ∈ (Finset.Ico c d).filter P, z n‖ ≤ B) :
    ‖∑ n ∈ (Finset.Ico a b).filter P, z n‖ ≤
      (cuts.card + 1) * B := by
  have hlocal := norm_sum_filter_Ico_le_cutCard_add_one_mul_of_subinterval
    z P cuts a b hcutBad hpiece a b le_rfl le_rfl
  have hcardNat : ((Finset.Ico a b).filter (fun n => n ∈ cuts)).card ≤
      cuts.card := Finset.card_le_card fun n hn => (Finset.mem_filter.mp hn).2
  have hcard :
      ((((Finset.Ico a b).filter (fun n => n ∈ cuts)).card : ℝ) + 1) ≤
        (cuts.card : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hcardNat 1
  exact hlocal.trans (mul_le_mul_of_nonneg_right hcard hB)

/-- The regular complement of the expanded critical hulls has at most two
component cuts per derivative order.  In particular its multiplier is
independent of the exceptional length `Xq`. -/
theorem norm_reciprocalPhaseSum_expandedHullRegular_le_components
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) (a b R : ℕ) (X Y q : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ c d : ℕ, a ≤ c → d ≤ b →
      (∀ n ∈ Finset.Ico c d,
        ¬ ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
          t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q) →
      ‖reciprocalPhaseSum N M j c d‖ ≤ B) :
    ‖∑ n ∈ (Finset.Ico a b).filter fun n =>
        n ∉ reciprocalDerivativeExpandedCriticalHullNatPoints
          (Finset.Ico a b) orders N M j X Y q R,
      standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      (((2 * orders.card + 1 : ℕ) : ℝ) * B) := by
  classical
  let hulls := reciprocalDerivativeExpandedCriticalHullNatPoints
    (Finset.Ico a b) orders N M j X Y q R
  let cuts := reciprocalDerivativeExpandedCriticalHullCuts
    (Finset.Ico a b) orders N M j X Y q R
  have hcomponents := norm_sum_filter_Ico_le_cutsCard_add_one_mul
    (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
    (fun n => n ∉ hulls) cuts a b hB
    (fun n hnCut hnRegular => hnRegular
      (reciprocalDerivativeExpandedCriticalHullCuts_subset_hulls
        (Finset.Ico a b) orders N M j X Y q R hnCut))
    (fun c d hc hd hdisjointCuts => by
      rcases
          all_mem_reciprocalDerivativeExpandedCriticalHulls_or_disjoint_of_disjoint_cuts
            (Finset.Ico a b) orders N M j X Y q R hdisjointCuts with
        hall | hdisjointHulls
      · have hempty : (Finset.Ico c d).filter (fun n => n ∉ hulls) = ∅ := by
          ext n
          constructor
          · intro hn
            have hnIco := (Finset.mem_filter.mp hn).1
            exact False.elim ((Finset.mem_filter.mp hn).2 (hall n hnIco))
          · simp
        rw [hempty]
        simpa using hB
      · have hwindow : ∀ n ∈ Finset.Ico c d,
            ¬ ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
              t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q := by
          intro n hnIco hnCritical
          have hnAmbient : n ∈ Finset.Ico a b := by
            rw [Finset.mem_Ico] at hnIco ⊢
            omega
          have hnExpanded : n ∈ reciprocalDerivativeExpandedCriticalNatPoints
              (Finset.Ico a b) orders N M j X Y q R :=
            mem_reciprocalDerivativeExpandedCriticalNatPoints.mpr
              ⟨hnAmbient, hnCritical⟩
          have hnHull : n ∈ hulls :=
            reciprocalDerivativeExpandedCriticalNatPoints_subset_hulls
              (Finset.Ico a b) orders N M j X Y q R hnExpanded
          rw [Finset.disjoint_left] at hdisjointHulls
          exact hdisjointHulls hnIco hnHull
        have hfilter : (Finset.Ico c d).filter (fun n => n ∉ hulls) =
            Finset.Ico c d := by
          apply Finset.filter_eq_self.mpr
          intro n hnIco hnHull
          rw [Finset.disjoint_left] at hdisjointHulls
          exact hdisjointHulls hnIco hnHull
        rw [hfilter]
        simpa [reciprocalPhaseSum] using hlocal c d hc hd hwindow)
  have hcardNat : cuts.card + 1 ≤ 2 * orders.card + 1 :=
    Nat.add_le_add_right
      (card_reciprocalDerivativeExpandedCriticalHullCuts_le
        (Finset.Ico a b) orders N M j X Y q R) 1
  have hcardReal : (cuts.card : ℝ) + 1 ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  exact hcomponents.trans (mul_le_mul_of_nonneg_right hcardReal hB)

/-- The regular reciprocal-phase remainder is bounded by one uniform
consecutive-interval estimate for each component created by the deleted
critical lattice points. -/
theorem norm_reciprocalPhaseSum_regularNatPoints_le_components
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) (a b : ℕ) (X Y q : ℝ)
    {B : ℝ}
    (hlocal : ∀ c d : ℕ, a ≤ c → d ≤ b →
      (∀ n ∈ Finset.Ico c d,
        (n : ℝ) ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q) →
      ‖reciprocalPhaseSum N M j c d‖ ≤ B) :
    ‖∑ n ∈ reciprocalDerivativeRegularNatPoints
        (Finset.Ico a b) orders N M j X Y q,
      standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      (((reciprocalDerivativeCriticalNatPoints
        (Finset.Ico a b) orders N M j X Y q).card : ℝ) + 1) * B := by
  classical
  simpa [reciprocalDerivativeRegularNatPoints,
    reciprocalDerivativeCriticalNatPoints, reciprocalPhaseSum] using
    (norm_sum_filter_Ico_le_badCard_add_one_mul_of_subinterval
      (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
      (fun n => (n : ℝ) ∉
        reciprocalDerivativeCriticalUnion N M j orders X Y q)
      a b (fun c d hc hd hregular => hlocal c d hc hd hregular)
      a b le_rfl le_rfl)

/-- Source cardinality control for the regular-component decomposition. -/
theorem norm_reciprocalPhaseSum_regularNatPoints_le_componentEnvelope
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) (a b : ℕ) {X Y q : ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hlocal : ∀ c d : ℕ, a ≤ c → d ≤ b →
      (∀ n ∈ Finset.Ico c d,
        (n : ℝ) ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q) →
      ‖reciprocalPhaseSum N M j c d‖ ≤ B) :
    ‖∑ n ∈ reciprocalDerivativeRegularNatPoints
        (Finset.Ico a b) orders N M j X Y q,
      standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      ((orders.card : ℝ) * (16 * X * q + 1) + 1) * B := by
  have hcomponents :=
    norm_reciprocalPhaseSum_regularNatPoints_le_components
      N M j orders a b X Y q hlocal
  have hcard := card_nat_points_reciprocalDerivativeCriticalUnion_le
    (reciprocalDerivativeCriticalNatPoints
      (Finset.Ico a b) orders N M j X Y q)
    N M j orders hX hq hM hj hpow (fun n hn =>
      (mem_reciprocalDerivativeCriticalNatPoints.mp hn).2)
  exact hcomponents.trans (mul_le_mul_of_nonneg_right (by linarith) hB)

/-- Exact partition of the phase sum into deleted critical points and the
regular remainder. -/
theorem reciprocalPhaseSum_eq_critical_add_regular
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ) (X Y q : ℝ) :
    (∑ n ∈ ambient,
        standardAdditiveCharacter (reciprocalPhase N M j n)) =
      (∑ n ∈ reciprocalDerivativeCriticalNatPoints
          ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)) +
      ∑ n ∈ reciprocalDerivativeRegularNatPoints
          ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n) := by
  classical
  simpa [reciprocalDerivativeCriticalNatPoints,
    reciprocalDerivativeRegularNatPoints] using
      (Finset.sum_filter_add_sum_filter_not ambient
        (fun n => (n : ℝ) ∈
          reciprocalDerivativeCriticalUnion N M j orders X Y q)
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))).symm

/-- After deleting all critical points, the original phase sum is bounded by
the regular sum plus the explicit finite deletion error. -/
theorem norm_reciprocalPhaseSum_le_regular_add_criticalError
    (ambient orders : Finset ℕ) (N M : ℝ) (j : ℕ) {X Y q : ℝ}
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ‖∑ n ∈ ambient,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      ‖∑ n ∈ reciprocalDerivativeRegularNatPoints
          ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ +
      (orders.card : ℝ) * (16 * X * q + 1) := by
  rw [reciprocalPhaseSum_eq_critical_add_regular]
  calc
    ‖(∑ n ∈ reciprocalDerivativeCriticalNatPoints
          ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)) +
        ∑ n ∈ reciprocalDerivativeRegularNatPoints
          ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      ‖∑ n ∈ reciprocalDerivativeCriticalNatPoints
          ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ +
      ‖∑ n ∈ reciprocalDerivativeRegularNatPoints
          ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ := norm_add_le _ _
    _ ≤ ‖∑ n ∈ reciprocalDerivativeRegularNatPoints
          ambient orders N M j X Y q,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ +
        (orders.card : ℝ) * (16 * X * q + 1) := by
      have hcritical := norm_reciprocalPhaseSum_criticalNatPoints_le
        ambient orders N M j hX hq hM hj hpow
      linarith

/-- Global critical/regular assembly: a uniform bound on every regular
consecutive interval is multiplied by the source lattice-point component
envelope, and the deleted critical points contribute their explicit cardinality
error. -/
theorem norm_reciprocalPhaseSum_le_componentEnvelope_add_criticalError
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) (a b : ℕ) {X Y q : ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hlocal : ∀ c d : ℕ, a ≤ c → d ≤ b →
      (∀ n ∈ Finset.Ico c d,
        (n : ℝ) ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q) →
      ‖reciprocalPhaseSum N M j c d‖ ≤ B) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((orders.card : ℝ) * (16 * X * q + 1) + 1) * B +
        (orders.card : ℝ) * (16 * X * q + 1) := by
  have hsplit := norm_reciprocalPhaseSum_le_regular_add_criticalError
    (Finset.Ico a b) orders N M j hX hq hM hj hpow
  have hregular :=
    norm_reciprocalPhaseSum_regularNatPoints_le_componentEnvelope
      N M j orders a b hB hX hq hM hj hpow hlocal
  simpa [reciprocalPhaseSum] using hsplit.trans (add_le_add hregular le_rfl)

/-- Component decomposition for the starts whose full forward `R`-windows are
regular. -/
theorem norm_reciprocalPhaseSum_expandedRegular_le_components
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) (a b R : ℕ) (X Y q : ℝ)
    {B : ℝ}
    (hlocal : ∀ c d : ℕ, a ≤ c → d ≤ b →
      (∀ n ∈ Finset.Ico c d,
        ¬ ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
          t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q) →
      ‖reciprocalPhaseSum N M j c d‖ ≤ B) :
    ‖∑ n ∈ reciprocalDerivativeExpandedRegularNatPoints
        (Finset.Ico a b) orders N M j X Y q R,
      standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      (((reciprocalDerivativeExpandedCriticalNatPoints
        (Finset.Ico a b) orders N M j X Y q R).card : ℝ) + 1) * B := by
  classical
  let Q : ℕ → Prop := fun n =>
    ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
      t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q
  change ‖∑ n ∈ (Finset.Ico a b).filter (fun n => ¬ Q n),
      standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
    ((((Finset.Ico a b).filter Q).card : ℝ) + 1) * B
  simpa only [not_not] using
    (norm_sum_filter_Ico_le_badCard_add_one_mul_of_subinterval
      (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
      (fun n => ¬ Q n)
      a b (fun c d hc hd hregular => hlocal c d hc hd hregular)
      a b le_rfl le_rfl)

/-- Global expanded-hull envelope with only two regular-component cuts per
derivative order.  The exceptional length occurs solely in the additive
unit-modulus deletion cost. -/
theorem norm_reciprocalPhaseSum_le_expandedHullComponentEnvelope
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) (a b R : ℕ) {X Y q : ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hlocal : ∀ c d : ℕ, a ≤ c → d ≤ b →
      (∀ n ∈ Finset.Ico c d,
        ¬ ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
          t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q) →
      ‖reciprocalPhaseSum N M j c d‖ ≤ B) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      (((2 * orders.card + 1 : ℕ) : ℝ) * B) +
        (orders.card : ℝ) * (16 * X * q + R + 1) := by
  classical
  let hulls := reciprocalDerivativeExpandedCriticalHullNatPoints
    (Finset.Ico a b) orders N M j X Y q R
  have hpartition :
      (∑ n ∈ Finset.Ico a b,
          standardAdditiveCharacter (reciprocalPhase N M j n)) =
        (∑ n ∈ (Finset.Ico a b).filter (fun n => n ∈ hulls),
          standardAdditiveCharacter (reciprocalPhase N M j n)) +
        ∑ n ∈ (Finset.Ico a b).filter (fun n => n ∉ hulls),
          standardAdditiveCharacter (reciprocalPhase N M j n) := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not (Finset.Ico a b)
        (fun n => n ∈ hulls)
        (fun n => standardAdditiveCharacter
          (reciprocalPhase N M j n))).symm
  have hbad :
      ‖∑ n ∈ (Finset.Ico a b).filter (fun n => n ∈ hulls),
          standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
        (orders.card : ℝ) * (16 * X * q + R + 1) := by
    calc
      ‖∑ n ∈ (Finset.Ico a b).filter (fun n => n ∈ hulls),
          standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
          ∑ n ∈ (Finset.Ico a b).filter (fun n => n ∈ hulls),
            ‖standardAdditiveCharacter (reciprocalPhase N M j n)‖ :=
        norm_sum_le _ _
      _ = (((Finset.Ico a b).filter (fun n => n ∈ hulls)).card : ℝ) := by
        simp
      _ ≤ (hulls.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (fun n hn =>
          (Finset.mem_filter.mp hn).2)
      _ ≤ (orders.card : ℝ) * (16 * X * q + R + 1) :=
        card_reciprocalDerivativeExpandedCriticalHullNatPoints_le
          (Finset.Ico a b) orders N M j R hX hq hM hj hpow
  have hregular :=
    norm_reciprocalPhaseSum_expandedHullRegular_le_components
      N M j orders a b R X Y q hB hlocal
  rw [reciprocalPhaseSum, hpartition]
  exact (norm_add_le _ _).trans (add_le_add hbad hregular) |>.trans_eq (by ring)

/-- Global expanded-margin component envelope.  The first summand is the
number of regular components times their uniform bound; the second is the
unit-modulus cost of every expanded critical start. -/
theorem norm_reciprocalPhaseSum_le_expandedComponentEnvelope
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) (a b R : ℕ) {X Y q : ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hX : 0 < X) (hq : 0 ≤ q) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hlocal : ∀ c d : ℕ, a ≤ c → d ≤ b →
      (∀ n ∈ Finset.Ico c d,
        ¬ ∃ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ),
          t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q) →
      ‖reciprocalPhaseSum N M j c d‖ ≤ B) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((orders.card : ℝ) * (16 * X * q + R + 1) + 1) * B +
        (orders.card : ℝ) * (16 * X * q + R + 1) := by
  rw [reciprocalPhaseSum]
  rw [reciprocalPhaseSum_eq_expandedCritical_add_regular
    (Finset.Ico a b) orders N M j X Y q R]
  calc
    ‖(∑ n ∈ reciprocalDerivativeExpandedCriticalNatPoints
          (Finset.Ico a b) orders N M j X Y q R,
        standardAdditiveCharacter (reciprocalPhase N M j n)) +
        ∑ n ∈ reciprocalDerivativeExpandedRegularNatPoints
          (Finset.Ico a b) orders N M j X Y q R,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      ‖∑ n ∈ reciprocalDerivativeExpandedCriticalNatPoints
          (Finset.Ico a b) orders N M j X Y q R,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ +
      ‖∑ n ∈ reciprocalDerivativeExpandedRegularNatPoints
          (Finset.Ico a b) orders N M j X Y q R,
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ := norm_add_le _ _
    _ ≤ (orders.card : ℝ) * (16 * X * q + R + 1) +
        (((reciprocalDerivativeExpandedCriticalNatPoints
          (Finset.Ico a b) orders N M j X Y q R).card : ℝ) + 1) * B :=
      add_le_add
        (norm_reciprocalPhaseSum_expandedCriticalNatPoints_le
          (Finset.Ico a b) orders N M j R hX hq hM hj hpow)
        (norm_reciprocalPhaseSum_expandedRegular_le_components
          N M j orders a b R X Y q hlocal)
    _ ≤ (orders.card : ℝ) * (16 * X * q + R + 1) +
        ((orders.card : ℝ) * (16 * X * q + R + 1) + 1) * B := by
      gcongr
      exact card_reciprocalDerivativeExpandedCriticalNatPoints_le
        (Finset.Ico a b) orders N M j R hX hq hM hj hpow
    _ = ((orders.card : ℝ) * (16 * X * q + R + 1) + 1) * B +
        (orders.card : ℝ) * (16 * X * q + R + 1) := by ring

/-- Consecutive integer starts with regular forward `R`-windows cover the
entire real interval through the last start's window. -/
theorem forall_Icc_of_forall_Ico_forwardWindow
    (P : ℝ → Prop) {a b R : ℕ} (hab : a < b) (hR : 1 ≤ R)
    (hwindow : ∀ n ∈ Finset.Ico a b,
      ∀ t ∈ Set.Icc (n : ℝ) ((n + R : ℕ) : ℝ), P t) :
    ∀ t ∈ Set.Icc (a : ℝ) ((b - 1 + R : ℕ) : ℝ), P t := by
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by positivity : (0 : ℝ) ≤ a) ht.1
  by_cases hfloor : ⌊t⌋₊ < b
  · have hafloor : a ≤ ⌊t⌋₊ := Nat.le_floor ht.1
    apply hwindow ⌊t⌋₊ (Finset.mem_Ico.mpr ⟨hafloor, hfloor⟩) t
    constructor
    · exact Nat.floor_le ht0
    · have hlt := Nat.lt_floor_add_one t
      norm_num only [Nat.cast_add] at hlt ⊢
      have hcastR : (1 : ℝ) ≤ R := by exact_mod_cast hR
      linarith
  · have hbFloor : b ≤ ⌊t⌋₊ := Nat.le_of_not_gt hfloor
    have hbpos : 0 < b := by omega
    have habPred : a ≤ b - 1 := by omega
    apply hwindow (b - 1) (Finset.mem_Ico.mpr ⟨habPred, by omega⟩) t
    constructor
    · have hcastFloor : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
      have hcastB : (b : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hbFloor
      have hpred : ((b - 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
        exact_mod_cast Nat.sub_le b 1
      linarith
    · exact ht.2

/-- Avoidance of every forward window of length `4H+1` gives the real
expanded-interval regularity required by four Weyl-differencing rounds. -/
theorem regular_on_fourStepExpandedIcc_of_forwardWindows
    (N M : ℝ) (j : ℕ) (orders : Finset ℕ) {X Y q : ℝ}
    {c d H : ℕ} (hcd : c < d)
    (hwindow : ∀ n ∈ Finset.Ico c d,
      ¬ ∃ t ∈ Set.Icc (n : ℝ) ((n + (4 * H + 1) : ℕ) : ℝ),
        t ∈ reciprocalDerivativeCriticalUnion N M j orders X Y q) :
    ∀ t ∈ Set.Icc (c : ℝ)
        ((c : ℝ) + (d - c : ℕ) + (4 * H : ℕ)),
      t ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q := by
  have hregular := forall_Icc_of_forall_Ico_forwardWindow
    (fun t => t ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    hcd (by omega : 1 ≤ 4 * H + 1) fun n hn t ht => by
      exact fun htCritical => hwindow n hn ⟨t, ht, htCritical⟩
  intro t ht
  apply hregular t
  refine ⟨ht.1, ?_⟩
  calc
    t ≤ (c : ℝ) + (d - c : ℕ) + (4 * H : ℕ) := ht.2
    _ = ((d - 1 + (4 * H + 1) : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      rw [Nat.cast_sub hcd.le, Nat.cast_sub (by omega : 1 ≤ d)]
      ring

/-- Once a critical set is nonempty, one explicit closed interval covers it.
Its radius is the pair-separation bound, so this is the formal version of the
source's “one short critical interval” reduction for a fixed derivative
order. -/
theorem reciprocalCriticalSet_subset_Icc
    (N C : ℝ) {k : ℕ} {X Y δ s : ℝ}
    (hX : 0 < X) (hC : C ≠ 0) (hk : 1 ≤ k)
    (hs : s ∈ reciprocalCriticalSet N C k X Y δ) :
    reciprocalCriticalSet N C k X Y δ ⊆
      Set.Icc
        (s - 2 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1)))
        (s + 2 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1))) := by
  rintro t ht
  rcases hs with ⟨⟨hsX, hsY⟩, hsCritical⟩
  rcases ht with ⟨⟨htX, htY⟩, htCritical⟩
  have hdist := criticalSublevel_pair_dist_le N C hX hC
    hsX hsY htX htY hk hsCritical htCritical
  have hbounds := abs_le.mp hdist
  constructor <;> linarith

/-- The covering interval in `reciprocalCriticalSet_subset_Icc` has twice
the displayed radius. -/
theorem reciprocalCriticalCover_length
    (C : ℝ) {k : ℕ} {X Y δ s : ℝ} :
    (s + 2 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1))) -
        (s - 2 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1))) =
      4 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1)) := by
  ring

/-- A fixed derivative order contributes at most one closed exceptional
interval, including the empty-critical-set case. -/
theorem exists_Icc_cover_reciprocalCriticalSet
    (N C : ℝ) {k : ℕ} {X Y δ : ℝ}
    (hX : 0 < X) (hY : 0 ≤ Y) (hδ : 0 ≤ δ)
    (hC : C ≠ 0) (hk : 1 ≤ k) :
    ∃ a b : ℝ,
      reciprocalCriticalSet N C k X Y δ ⊆ Set.Icc a b ∧
      b - a ≤ 4 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1)) := by
  by_cases hnonempty : (reciprocalCriticalSet N C k X Y δ).Nonempty
  · obtain ⟨s, hs⟩ := hnonempty
    refine ⟨
      s - 2 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1)),
      s + 2 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1)),
      reciprocalCriticalSet_subset_Icc N C hX hC hk hs, ?_⟩
    exact (reciprocalCriticalCover_length C).le
  · refine ⟨0, 0, ?_, ?_⟩
    · simp [Set.not_nonempty_iff_eq_empty.mp hnonempty]
    · have hden : 0 < |C| * X ^ (k - 1) :=
        mul_pos (abs_pos.mpr hC) (pow_pos hX _)
      simpa only [sub_self] using
        div_nonneg
          (mul_nonneg
            (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hδ)
            (pow_nonneg hY (2 * k)))
          hden.le

/-- Lebesgue-measure version of the single-interval cover. -/
theorem volume_reciprocalCriticalSet_le
    (N C : ℝ) {k : ℕ} {X Y δ : ℝ}
    (hX : 0 < X) (hY : 0 ≤ Y) (hδ : 0 ≤ δ)
    (hC : C ≠ 0) (hk : 1 ≤ k) :
    MeasureTheory.volume (reciprocalCriticalSet N C k X Y δ) ≤
      ENNReal.ofReal
        (4 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1))) := by
  obtain ⟨a, b, hsubset, hlength⟩ :=
    exists_Icc_cover_reciprocalCriticalSet N C hX hY hδ hC hk
  calc
    MeasureTheory.volume (reciprocalCriticalSet N C k X Y δ) ≤
        MeasureTheory.volume (Set.Icc a b) := MeasureTheory.measure_mono hsubset
    _ = ENNReal.ofReal (b - a) := Real.volume_Icc
    _ ≤ ENNReal.ofReal
        (4 * δ * Y ^ (2 * k) / (|C| * X ^ (k - 1))) :=
      ENNReal.ofReal_le_ofReal hlength

/-- The normalized derivative is exactly `1/t` times the critical expression
with coefficient `M_r` and exponent `j-1`. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_eq_critical
    (N M : ℝ) {j r : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : 0 < t) :
    t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| =
      |reciprocalCriticalExpression N
          (reciprocalPhaseHigherCoefficient M j r) (j - 1) t| / t := by
  rw [normalized_abs_iteratedDeriv_reciprocalPhase N M j r ht]
  unfold reciprocalCriticalExpression
  have hjpow : t ^ j = t ^ (j - 1) * t := by
    calc
      t ^ j = t ^ ((j - 1) + 1) := by congr 1; omega
      _ = t ^ (j - 1) * t := by rw [pow_succ]
  have hinside :
      N / t + reciprocalPhaseHigherCoefficient M j r / t ^ j =
        (N + reciprocalPhaseHigherCoefficient M j r / t ^ (j - 1)) / t := by
    rw [hjpow]
    field_simp [ht.ne']
  rw [hinside, abs_div, abs_of_pos ht]

/-- The regular-set condition translated back to the normalized absolute
derivative in equation (expint1). -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_gt_of_not_mem_criticalUnion
    (N M : ℝ) {j r : ℕ} (orders : Finset ℕ) {X Y q t : ℝ}
    (hX : 0 < X) (hj : 1 ≤ j)
    (htIcc : t ∈ Set.Icc X Y)
    (htRegular : t ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : r ∈ orders) :
    |reciprocalPhaseHigherCoefficient M j r| / X ^ (j - 1) * q / t <
      t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| := by
  have ht : 0 < t := hX.trans_le htIcc.1
  rw [normalized_abs_iteratedDeriv_reciprocalPhase_eq_critical N M hj ht]
  exact div_lt_div_of_pos_right
    (abs_reciprocalCriticalExpression_gt_of_not_mem_criticalUnion
      N M j orders htIcc htRegular hr) ht

/-- In the large-`M_r` branch, deleting the critical union gives the uniform
lower derivative bound `(Fq)/10` used before invoking Vinogradov or Weyl. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_gt_scale_mul_of_large
    (N M : ℝ) {j r : ℕ} (orders : Finset ℕ) {X Y q t : ℝ}
    (hX : 0 < X) (hq : 0 < q) (hj : 1 ≤ j)
    (htIcc : t ∈ Set.Icc X Y) (htop : t ≤ 2 * X)
    (htRegular : t ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : r ∈ orders)
    (hlarge : |N| * X ^ (j - 1) ≤
      4 * |reciprocalPhaseHigherCoefficient M j r|) :
    reciprocalPhaseScale N M j X * q / 10 <
      t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| := by
  let Cabs := |reciprocalPhaseHigherCoefficient M j r|
  have hF : reciprocalPhaseScale N M j X ≤ 5 * (Cabs / X ^ j) := by
    exact reciprocalPhaseScale_le_five_mul_higherCoefficient
      N M hj hX hlarge
  have ht : 0 < t := hX.trans_le htIcc.1
  have hpowPos : 0 < X ^ (j - 1) := pow_pos hX _
  have hden : X ^ (j - 1) * t ≤ 2 * X ^ j := by
    calc
      X ^ (j - 1) * t ≤ X ^ (j - 1) * (2 * X) :=
        mul_le_mul_of_nonneg_left htop hpowPos.le
      _ = 2 * X ^ j := by
        have hjpow : X ^ j = X ^ (j - 1) * X := by
          calc
            X ^ j = X ^ ((j - 1) + 1) := by congr 1; omega
            _ = X ^ (j - 1) * X := by rw [pow_succ]
        rw [hjpow]
        ring
  have hmiddle : Cabs / X ^ j * q / 2 ≤ Cabs / X ^ (j - 1) * q / t := by
    have hnum : 0 ≤ Cabs * q := mul_nonneg (abs_nonneg _) hq.le
    have hdiv : Cabs * q / (2 * X ^ j) ≤
        Cabs * q / (X ^ (j - 1) * t) :=
      div_le_div_of_nonneg_left hnum (mul_pos hpowPos ht) hden
    convert hdiv using 1 <;> field_simp [hX.ne', ht.ne']
  have hlower :=
    normalized_abs_iteratedDeriv_reciprocalPhase_gt_of_not_mem_criticalUnion
      N M orders hX hj htIcc htRegular hr
  calc
    reciprocalPhaseScale N M j X * q / 10 ≤
        (5 * (Cabs / X ^ j)) * q / 10 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hF hq.le) (by norm_num)
    _ = Cabs / X ^ j * q / 2 := by ring
    _ ≤ Cabs / X ^ (j - 1) * q / t := hmiddle
    _ < t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| := hlower

/-- Unified derivative lower bound after critical-set deletion.  The small
`M_r` case is uniform everywhere, while the complementary case uses the
deleted critical interval; together they give `(Fq)/10` for every selected
order. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_ge_scale_mul_div_ten_of_regular
    (N M : ℝ) {j r : ℕ} (orders : Finset ℕ) {X Y q t : ℝ}
    (hX : 0 < X) (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (htIcc : t ∈ Set.Icc X Y) (htop : t ≤ 2 * X)
    (htRegular : t ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : r ∈ orders) :
    reciprocalPhaseScale N M j X * q / 10 ≤
      t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| := by
  rcases le_total
      (4 * |reciprocalPhaseHigherCoefficient M j r|)
      (|N| * X ^ (j - 1)) with hsmall | hlarge
  · have hbase :=
      normalized_abs_iteratedDeriv_reciprocalPhase_ge_scale_div_ten_of_small
        N M hj hX htIcc.1 htop hsmall
    have hF0 := reciprocalPhaseScale_nonneg N M j hX
    have hqmul : reciprocalPhaseScale N M j X * q ≤
        reciprocalPhaseScale N M j X := by
      calc
        reciprocalPhaseScale N M j X * q ≤
            reciprocalPhaseScale N M j X * 1 :=
          mul_le_mul_of_nonneg_left hqOne hF0
        _ = reciprocalPhaseScale N M j X := by ring
    exact (div_le_div_of_nonneg_right hqmul (by norm_num)).trans hbase
  · exact (normalized_abs_iteratedDeriv_reciprocalPhase_gt_scale_mul_of_large
      N M orders hX hq hj htIcc htop htRegular hr hlarge).le

/-- Complete two-sided derivative window available on the regular remainder,
before the elementary conversion to the source's `α^(±r³)F` notation. -/
theorem reciprocalPhase_derivative_bounds_on_regular
    (N M : ℝ) {j r : ℕ} (orders : Finset ℕ) {X Y q t : ℝ}
    (hX : 0 < X) (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (htIcc : t ∈ Set.Icc X Y) (htop : t ≤ 2 * X)
    (htRegular : t ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : r ∈ orders) :
    reciprocalPhaseScale N M j X * q / 10 ≤
        t ^ r / (r.factorial : ℝ) *
          |iteratedDeriv r (reciprocalPhase N M j) t| ∧
      t ^ r / (r.factorial : ℝ) *
          |iteratedDeriv r (reciprocalPhase N M j) t| ≤
        (((r + j) ^ r : ℕ) : ℝ) * reciprocalPhaseScale N M j X := by
  exact ⟨
    normalized_abs_iteratedDeriv_reciprocalPhase_ge_scale_mul_div_ten_of_regular
      N M orders hX hq hqOne hj htIcc htop htRegular hr,
    normalized_abs_iteratedDeriv_reciprocalPhase_le_multiplier_scale
      N M hj hX htIcc.1⟩

/-- Conversion of the explicit regular-set window to the
`α^(-r³)F ≤ · ≤ α^(r³)F` normalization in Vinogradov's estimate. -/
theorem reciprocalPhase_vinogradov_derivative_bounds_on_regular
    (N M : ℝ) {j r : ℕ} (orders : Finset ℕ) {X Y q t α : ℝ}
    (hX : 0 < X) (hq : 0 < q) (hqOne : q ≤ 1) (hα : 0 < α)
    (hj : 1 ≤ j) (htIcc : t ∈ Set.Icc X Y) (htop : t ≤ 2 * X)
    (htRegular : t ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : r ∈ orders)
    (hlowerCoeff : 10 ≤ α ^ (r ^ 3) * q)
    (hupperCoeff : (((r + j) ^ r : ℕ) : ℝ) ≤ α ^ (r ^ 3)) :
    reciprocalPhaseScale N M j X / α ^ (r ^ 3) ≤
        t ^ r / (r.factorial : ℝ) *
          |iteratedDeriv r (reciprocalPhase N M j) t| ∧
      t ^ r / (r.factorial : ℝ) *
          |iteratedDeriv r (reciprocalPhase N M j) t| ≤
        α ^ (r ^ 3) * reciprocalPhaseScale N M j X := by
  obtain ⟨hlower, hupper⟩ := reciprocalPhase_derivative_bounds_on_regular
    N M orders hX hq hqOne hj htIcc htop htRegular hr
  have hF0 := reciprocalPhaseScale_nonneg N M j hX
  have hαpow : 0 < α ^ (r ^ 3) := pow_pos hα _
  have hscaled :
      reciprocalPhaseScale N M j X / α ^ (r ^ 3) ≤
        reciprocalPhaseScale N M j X * q / 10 := by
    rw [div_le_div_iff₀ hαpow (by norm_num : (0 : ℝ) < 10)]
    have hmul := mul_le_mul_of_nonneg_left hlowerCoeff hF0
    nlinarith
  exact ⟨hscaled.trans hlower,
    hupper.trans (mul_le_mul_of_nonneg_right hupperCoeff hF0)⟩

end

end Tao2026
