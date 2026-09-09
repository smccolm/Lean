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
