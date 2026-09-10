import Tao2026.TypeIIKernel
import Tao2026.PhaseVariation
import Tao2026.CriticalIntervals
import Tao2026.Vinogradov
import RiemannZeta.GuthMaynard.VanDerCorput
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite Weyl differencing

This module begins the unconditional exponential-sum engine needed for
Proposition 1.12.  It formalizes the averaged-shift Cauchy--Schwarz step of
van der Corput/Weyl differencing, including the exact finite boundary fibers.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate Interval

namespace Tao2026

noncomputable section

/-- Pairs `(n,h)` used to average a sum of length `N` over `H` shifts. -/
def weylShiftPairs (N H : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range N ×ˢ Finset.range H

/-- The fiber of shifted pairs satisfying `n + h = m`.  These fibers retain
the exact boundary truncation in the averaged-shift argument. -/
def weylShiftFiber (N H m : ℕ) : Finset (ℕ × ℕ) :=
  (weylShiftPairs N H).filter (fun p => p.1 + p.2 = m)

/-- The shifted window sum over the exact fiber `n + h = m`. -/
def weylWindowSum (a : ℕ → ℂ) (N H m : ℕ) : ℂ :=
  ∑ p ∈ weylShiftFiber N H m, a p.1

/-- Every shifted pair maps into the ambient interval of length `N + H`. -/
theorem add_mem_range_add_of_mem_weylShiftPairs
    {N H : ℕ} {p : ℕ × ℕ} (hp : p ∈ weylShiftPairs N H) :
    p.1 + p.2 ∈ Finset.range (N + H) := by
  rcases Finset.mem_product.mp hp with ⟨hn, hh⟩
  exact Finset.mem_range.mpr
    (Nat.add_lt_add (Finset.mem_range.mp hn) (Finset.mem_range.mp hh))

/-- Exact averaged-shift identity.  Each original summand occurs once for
each of the `H` shifts, while the left side groups the same pairs by their
shifted endpoint. -/
theorem sum_weylWindowSum (a : ℕ → ℂ) (N H : ℕ) :
    ∑ m ∈ Finset.range (N + H), weylWindowSum a N H m =
      (H : ℂ) * ∑ n ∈ Finset.range N, a n := by
  calc
    ∑ m ∈ Finset.range (N + H), weylWindowSum a N H m =
        ∑ p ∈ weylShiftPairs N H, a p.1 := by
      simpa only [weylWindowSum, weylShiftFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (fun p hp => add_mem_range_add_of_mem_weylShiftPairs hp)
          (fun p => a p.1))
    _ = (H : ℂ) * ∑ n ∈ Finset.range N, a n := by
      simp only [weylShiftPairs, Finset.sum_product, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      exact (Finset.mul_sum _ _ _).symm

/-- Averaged-shift Cauchy--Schwarz inequality, the first quantitative step
of finite van der Corput/Weyl differencing.  It is valid without auxiliary
positivity assumptions, so later stages may choose the shift length freely.
-/
theorem norm_sum_sq_mul_shift_sq_le
    (a : ℕ → ℂ) (N H : ℕ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, a n‖ ^ 2 ≤
      (N + H : ℕ) *
        ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 := by
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, a n‖ ^ 2 =
        ‖∑ m ∈ Finset.range (N + H), weylWindowSum a N H m‖ ^ 2 := by
      rw [sum_weylWindowSum]
      simp [mul_pow]
    _ ≤ ((Finset.range (N + H)).card : ℝ) *
        ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 :=
      norm_sum_sq_le_card_mul_sum_norm_sq _ _
    _ = (N + H : ℕ) *
        ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 := by
      simp

/-- Exact double-sum expansion of one boundary-truncated shift window. -/
theorem weylWindowSum_mul_conj
    (a : ℕ → ℂ) (N H m : ℕ) :
    weylWindowSum a N H m * conj (weylWindowSum a N H m) =
      ∑ p ∈ weylShiftFiber N H m,
        ∑ q ∈ weylShiftFiber N H m, a p.1 * conj (a q.1) := by
  exact sum_mul_conj_sum_eq_doubleSum _ _

/-- Squared-norm version of the exact expansion of one shift window. -/
theorem weylWindowSum_norm_sq
    (a : ℕ → ℂ) (N H m : ℕ) :
    ((‖weylWindowSum a N H m‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ weylShiftFiber N H m,
        ∑ q ∈ weylShiftFiber N H m, a p.1 * conj (a q.1) := by
  rw [← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self, mul_comm,
    weylWindowSum_mul_conj]

/-- Summing the window squares and removing the fiber index gives the exact
pair-correlation constraint `n + h = n' + h'`.  This is the combinatorial
form from which the usual lagged correlations are obtained. -/
theorem sum_weylWindowSum_norm_sq_eq_pairCorrelation
    (a : ℕ → ℂ) (N H : ℕ) :
    ∑ m ∈ Finset.range (N + H),
        ((‖weylWindowSum a N H m‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ weylShiftPairs N H,
        ∑ q ∈ (weylShiftPairs N H).filter
          (fun q => q.1 + q.2 = p.1 + p.2),
          a p.1 * conj (a q.1) := by
  calc
    ∑ m ∈ Finset.range (N + H),
        ((‖weylWindowSum a N H m‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ Finset.range (N + H),
          ∑ p ∈ weylShiftFiber N H m,
            ∑ q ∈ weylShiftFiber N H m,
              a p.1 * conj (a q.1) := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact weylWindowSum_norm_sq a N H m
    _ = ∑ m ∈ Finset.range (N + H),
          ∑ p ∈ weylShiftFiber N H m,
            ∑ q ∈ (weylShiftPairs N H).filter
              (fun q => q.1 + q.2 = p.1 + p.2),
              a p.1 * conj (a q.1) := by
      apply Finset.sum_congr rfl
      intro m _hm
      apply Finset.sum_congr rfl
      intro p hp
      have hpm : p.1 + p.2 = m :=
        (Finset.mem_filter.mp hp).2
      congr 1
      ext q
      simp only [weylShiftFiber, Finset.mem_filter]
      simp [hpm]
    _ = ∑ p ∈ weylShiftPairs N H,
          ∑ q ∈ (weylShiftPairs N H).filter
            (fun q => q.1 + q.2 = p.1 + p.2),
            a p.1 * conj (a q.1) := by
      simpa only [weylShiftFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (fun p hp => add_mem_range_add_of_mem_weylShiftPairs hp)
          (fun p =>
            ∑ q ∈ (weylShiftPairs N H).filter
              (fun q => q.1 + q.2 = p.1 + p.2),
              a p.1 * conj (a q.1)))

/-- Pairs of original indices compatible with two fixed shifts. -/
def weylFixedShiftPairs (N h h' : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter
    (fun p => p.1 + h = p.2 + h')

/-- The forward correlation at lag `d`, with its exact truncated support. -/
def weylForwardCorrelation (a : ℕ → ℂ) (N d : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N - d), a (n + d) * conj (a n)

/-- When `h ≤ h'`, the fixed-shift constraint is exactly the image of the
forward-lag interval under `n ↦ (n + (h' - h), n)`. -/
theorem weylFixedShiftPairs_eq_image_of_le
    {N h h' : ℕ} (hh' : h ≤ h') :
    weylFixedShiftPairs N h h' =
      (Finset.range (N - (h' - h))).image
        (fun n => (n + (h' - h), n)) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpRange, hpEq⟩
    rcases Finset.mem_product.mp hpRange with ⟨hpFirst, hpSecond⟩
    have hpRel : p.1 = p.2 + (h' - h) := by omega
    have hpBound : p.2 < N - (h' - h) := by
      rw [Nat.lt_sub_iff_add_lt]
      simpa [← hpRel] using Finset.mem_range.mp hpFirst
    refine Finset.mem_image.mpr ⟨p.2, Finset.mem_range.mpr hpBound, ?_⟩
    apply Prod.ext
    · simp [hpRel]
    · rfl
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
    rw [weylFixedShiftPairs, Finset.mem_filter, Finset.mem_product]
    have hnBound : n + (h' - h) < N := by
      have := Finset.mem_range.mp hn
      omega
    constructor
    · exact ⟨Finset.mem_range.mpr hnBound,
        Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_add_right n _) hnBound)⟩
    · omega

/-- A fixed ordered pair of shifts with `h ≤ h'` contributes precisely the
forward correlation at lag `h' - h`. -/
theorem sum_weylFixedShiftPairs_eq_forwardCorrelation_of_le
    (a : ℕ → ℂ) (N : ℕ) {h h' : ℕ} (hh' : h ≤ h') :
    ∑ p ∈ weylFixedShiftPairs N h h', a p.1 * conj (a p.2) =
      weylForwardCorrelation a N (h' - h) := by
  rw [weylFixedShiftPairs_eq_image_of_le hh']
  rw [Finset.sum_image]
  · rfl
  · intro n _hn n' _hn' heq
    exact congrArg Prod.snd heq

/-- In the reverse ordering of the two shifts, the same fixed-shift sum is
the complex conjugate of the corresponding forward correlation. -/
theorem sum_weylFixedShiftPairs_eq_conj_forwardCorrelation_of_ge
    (a : ℕ → ℂ) (N : ℕ) {h h' : ℕ} (hh' : h' ≤ h) :
    ∑ p ∈ weylFixedShiftPairs N h h', a p.1 * conj (a p.2) =
      conj (weylForwardCorrelation a N (h - h')) := by
  have hpair : weylFixedShiftPairs N h h' =
      (Finset.range (N - (h - h'))).image
        (fun n => (n, n + (h - h'))) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpRange, hpEq⟩
      rcases Finset.mem_product.mp hpRange with ⟨hpFirst, hpSecond⟩
      have hpRel : p.2 = p.1 + (h - h') := by omega
      have hpBound : p.1 < N - (h - h') := by
        rw [Nat.lt_sub_iff_add_lt]
        simpa [← hpRel] using Finset.mem_range.mp hpSecond
      refine Finset.mem_image.mpr ⟨p.1, Finset.mem_range.mpr hpBound, ?_⟩
      apply Prod.ext
      · rfl
      · simp [hpRel]
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
      rw [weylFixedShiftPairs, Finset.mem_filter, Finset.mem_product]
      have hnBound : n + (h - h') < N := by
        have := Finset.mem_range.mp hn
        omega
      constructor
      · exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt
            (Nat.le_add_right n _) hnBound),
          Finset.mem_range.mpr hnBound⟩
      · omega
  rw [hpair, Finset.sum_image]
  · rw [weylForwardCorrelation, map_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    simp [map_mul, mul_comm]
  · intro n _hn n' _hn' heq
    exact congrArg Prod.fst heq

/-- The norm of a fixed-shift correlation depends only on the natural
distance between the two shifts. -/
theorem norm_sum_weylFixedShiftPairs_eq_forwardCorrelation_natDist
    (a : ℕ → ℂ) (N h h' : ℕ) :
    ‖∑ p ∈ weylFixedShiftPairs N h h', a p.1 * conj (a p.2)‖ =
      ‖weylForwardCorrelation a N (Nat.dist h h')‖ := by
  rcases le_total h h' with hh' | hh'
  · rw [sum_weylFixedShiftPairs_eq_forwardCorrelation_of_le a N hh',
      Nat.dist_eq_sub_of_le hh']
  · rw [sum_weylFixedShiftPairs_eq_conj_forwardCorrelation_of_ge a N hh',
      Nat.dist_eq_sub_of_le_right hh']
    exact norm_conj _

/-- The endpoint-constrained pair sum can equivalently be organized by the
two shifts first. -/
theorem sum_weylPairCorrelation_eq_sum_fixedShiftPairs
    (a : ℕ → ℂ) (N H : ℕ) :
    ∑ p ∈ weylShiftPairs N H,
        ∑ q ∈ (weylShiftPairs N H).filter
          (fun q => q.1 + q.2 = p.1 + p.2),
          a p.1 * conj (a q.1) =
      ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ p ∈ weylFixedShiftPairs N h h',
          a p.1 * conj (a p.2) := by
  simp only [weylShiftPairs, weylFixedShiftPairs, Finset.sum_product,
    Finset.sum_filter]
  calc
    ∑ n ∈ Finset.range N, ∑ h ∈ Finset.range H,
        ∑ n' ∈ Finset.range N, ∑ h' ∈ Finset.range H,
          (if n' + h' = n + h then a n * conj (a n') else 0) =
      ∑ h ∈ Finset.range H, ∑ n ∈ Finset.range N,
        ∑ n' ∈ Finset.range N, ∑ h' ∈ Finset.range H,
          (if n' + h' = n + h then a n * conj (a n') else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
          (if n' + h' = n + h then a n * conj (a n') else 0) := by
      apply Finset.sum_congr rfl
      intro h _hh
      calc
        ∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
            ∑ h' ∈ Finset.range H,
              (if n' + h' = n + h then a n * conj (a n') else 0) =
          ∑ n ∈ Finset.range N, ∑ h' ∈ Finset.range H,
            ∑ n' ∈ Finset.range N,
              (if n' + h' = n + h then a n * conj (a n') else 0) := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [Finset.sum_comm]
        _ = ∑ h' ∈ Finset.range H, ∑ n ∈ Finset.range N,
            ∑ n' ∈ Finset.range N,
              (if n' + h' = n + h then a n * conj (a n') else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
          (if n + h = n' + h' then a n * conj (a n') else 0) := by
      apply Finset.sum_congr rfl
      intro h _hh
      apply Finset.sum_congr rfl
      intro h' _hh'
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro n' _hn'
      by_cases heq : n + h = n' + h'
      · rw [if_pos heq, if_pos heq.symm]
      · have hne : n' + h' ≠ n + h := by
          exact fun hrev => heq hrev.symm
        rw [if_neg heq, if_neg hne]

/-- Complete exact shift-correlation expansion of the window-square term in
the averaged Cauchy--Schwarz inequality. -/
theorem sum_weylWindowSum_norm_sq_eq_sum_fixedShiftPairs
    (a : ℕ → ℂ) (N H : ℕ) :
    ∑ m ∈ Finset.range (N + H),
        ((‖weylWindowSum a N H m‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ p ∈ weylFixedShiftPairs N h h',
          a p.1 * conj (a p.2) := by
  rw [sum_weylWindowSum_norm_sq_eq_pairCorrelation,
    sum_weylPairCorrelation_eq_sum_fixedShiftPairs]

/-- Before regrouping by distance, the real window-square sum is bounded by
the norms of all fixed-shift correlations. -/
theorem sum_weylWindowSum_norm_sq_le_shiftCorrelationNorms
    (a : ℕ → ℂ) (N H : ℕ) :
    ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 ≤
      ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ‖weylForwardCorrelation a N (Nat.dist h' h)‖ := by
  have hexpand := sum_weylWindowSum_norm_sq_eq_sum_fixedShiftPairs a N H
  have hre :
      ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 =
        (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ p ∈ weylFixedShiftPairs N h h',
            a p.1 * conj (a p.2)).re := by
    calc
      ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 =
          ∑ m ∈ Finset.range (N + H),
            (((‖weylWindowSum a N H m‖ ^ 2 : ℝ) : ℂ).re) := by
        apply Finset.sum_congr rfl
        intro m _hm
        rfl
      _ = (∑ m ∈ Finset.range (N + H),
            ((‖weylWindowSum a N H m‖ ^ 2 : ℝ) : ℂ)).re := by
        rw [Complex.re_sum]
      _ = _ := congrArg Complex.re hexpand
  calc
    ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 =
        (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ p ∈ weylFixedShiftPairs N h h',
            a p.1 * conj (a p.2)).re := hre
    _ = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          (∑ p ∈ weylFixedShiftPairs N h h',
            a p.1 * conj (a p.2)).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      rw [Complex.re_sum]
    _ ≤ ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ‖∑ p ∈ weylFixedShiftPairs N h h',
            a p.1 * conj (a p.2)‖ := by
      apply Finset.sum_le_sum
      intro h _hh
      apply Finset.sum_le_sum
      intro h' _hh'
      exact Complex.re_le_norm _
    _ = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ‖weylForwardCorrelation a N (Nat.dist h' h)‖ := by
      apply Finset.sum_congr rfl
      intro h _hh
      apply Finset.sum_congr rfl
      intro h' _hh'
      rw [norm_sum_weylFixedShiftPairs_eq_forwardCorrelation_natDist,
        Nat.dist_comm h h']

/-- For positive `H`, actual shift distances are strictly below `H`, giving
the sharp lag range `[0,H)` rather than the harmless `[0,H]` overcount. -/
theorem sum_weylWindowSum_norm_sq_le_forwardCorrelations_of_pos
    (a : ℕ → ℂ) (N H : ℕ) (hH : 0 < H) :
    ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 ≤
      2 * (H : ℝ) *
        ∑ d ∈ Finset.range H, ‖weylForwardCorrelation a N d‖ := by
  calc
    ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 ≤
        ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ‖weylForwardCorrelation a N (Nat.dist h' h)‖ :=
      sum_weylWindowSum_norm_sq_le_shiftCorrelationNorms a N H
    _ ≤ ∑ _h ∈ Finset.range H,
          2 * ∑ d ∈ Finset.range H,
            ‖weylForwardCorrelation a N d‖ := by
      apply Finset.sum_le_sum
      intro h hh
      have hBound := Finset.mem_range.mp hh
      have hRewrite : H - 1 + 1 = H := Nat.sub_add_cancel hH
      simpa only [hRewrite] using
        (sum_natDistKernel_le_two_mul_sum
          (Finset.range H) h (H - 1)
          (fun d => ‖weylForwardCorrelation a N d‖)
          (fun d => norm_nonneg _)
          (by
            intro h' hh'
            have hh'Bound := Finset.mem_range.mp hh'
            rcases le_total h' h with hle | hle
            · rw [Nat.dist_eq_sub_of_le hle]
              omega
            · rw [Nat.dist_eq_sub_of_le_right hle]
              omega))
    _ = 2 * (H : ℝ) *
          ∑ d ∈ Finset.range H,
            ‖weylForwardCorrelation a N d‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- A fully real upper bound for the averaged window-square term by forward
correlations.  The factor two is the sharp multiplicity bound for a fixed
natural distance from a shift center. -/
theorem sum_weylWindowSum_norm_sq_le_forwardCorrelations
    (a : ℕ → ℂ) (N H : ℕ) :
    ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 ≤
      2 * (H : ℝ) *
        ∑ d ∈ Finset.range (H + 1),
          ‖weylForwardCorrelation a N d‖ := by
  have hexpand := sum_weylWindowSum_norm_sq_eq_sum_fixedShiftPairs a N H
  have hre :
      ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 =
        (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ p ∈ weylFixedShiftPairs N h h',
            a p.1 * conj (a p.2)).re := by
    calc
      ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 =
          ∑ m ∈ Finset.range (N + H),
            (((‖weylWindowSum a N H m‖ ^ 2 : ℝ) : ℂ).re) := by
        apply Finset.sum_congr rfl
        intro m _hm
        change ‖weylWindowSum a N H m‖ ^ 2 =
          ‖weylWindowSum a N H m‖ ^ 2
        rfl
      _ = (∑ m ∈ Finset.range (N + H),
            ((‖weylWindowSum a N H m‖ ^ 2 : ℝ) : ℂ)).re := by
        rw [Complex.re_sum]
      _ = _ := congrArg Complex.re hexpand
  calc
    ∑ m ∈ Finset.range (N + H), ‖weylWindowSum a N H m‖ ^ 2 =
        (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ p ∈ weylFixedShiftPairs N h h',
            a p.1 * conj (a p.2)).re := hre
    _ = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          (∑ p ∈ weylFixedShiftPairs N h h',
            a p.1 * conj (a p.2)).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      rw [Complex.re_sum]
    _ ≤ ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ‖∑ p ∈ weylFixedShiftPairs N h h',
            a p.1 * conj (a p.2)‖ := by
      apply Finset.sum_le_sum
      intro h _hh
      apply Finset.sum_le_sum
      intro h' _hh'
      exact Complex.re_le_norm _
    _ = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ‖weylForwardCorrelation a N (Nat.dist h' h)‖ := by
      apply Finset.sum_congr rfl
      intro h _hh
      apply Finset.sum_congr rfl
      intro h' _hh'
      rw [norm_sum_weylFixedShiftPairs_eq_forwardCorrelation_natDist,
        Nat.dist_comm h h']
    _ ≤ ∑ _h ∈ Finset.range H,
          2 * ∑ d ∈ Finset.range (H + 1),
            ‖weylForwardCorrelation a N d‖ := by
      apply Finset.sum_le_sum
      intro h hh
      have hBound := Finset.mem_range.mp hh
      exact sum_natDistKernel_le_two_mul_sum
        (Finset.range H) h H (fun d => ‖weylForwardCorrelation a N d‖)
        (fun d => norm_nonneg _)
        (by
          intro h' hh'
          have hh'Bound := Finset.mem_range.mp hh'
          rcases le_total h' h with hle | hle
          · rw [Nat.dist_eq_sub_of_le hle]
            omega
          · rw [Nat.dist_eq_sub_of_le_right hle]
            omega)
    _ = 2 * (H : ℝ) *
          ∑ d ∈ Finset.range (H + 1),
            ‖weylForwardCorrelation a N d‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Finite van der Corput inequality in forward-correlation form. -/
theorem norm_sum_sq_mul_shift_sq_le_forwardCorrelations
    (a : ℕ → ℂ) (N H : ℕ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, a n‖ ^ 2 ≤
      2 * ((N + H : ℕ) : ℝ) * (H : ℝ) *
        ∑ d ∈ Finset.range (H + 1),
          ‖weylForwardCorrelation a N d‖ := by
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, a n‖ ^ 2 ≤
        ((N + H : ℕ) : ℝ) *
          ∑ m ∈ Finset.range (N + H),
            ‖weylWindowSum a N H m‖ ^ 2 :=
      norm_sum_sq_mul_shift_sq_le a N H
    _ ≤ ((N + H : ℕ) : ℝ) *
        (2 * (H : ℝ) *
          ∑ d ∈ Finset.range (H + 1),
            ‖weylForwardCorrelation a N d‖) := by
      exact mul_le_mul_of_nonneg_left
        (sum_weylWindowSum_norm_sq_le_forwardCorrelations a N H)
        (Nat.cast_nonneg (N + H))
    _ = 2 * ((N + H : ℕ) : ℝ) * (H : ℝ) *
        ∑ d ∈ Finset.range (H + 1),
          ‖weylForwardCorrelation a N d‖ := by ring

/-- Divided form of finite van der Corput, valid for a positive shift length.
This is the form intended for iteration. -/
theorem norm_sum_sq_mul_shift_le_forwardCorrelations
    (a : ℕ → ℂ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖ ^ 2 ≤
      2 * ((N + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range (H + 1),
          ‖weylForwardCorrelation a N d‖ := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hbound := norm_sum_sq_mul_shift_sq_le_forwardCorrelations a N H
  refine le_of_mul_le_mul_left ?_ hHR
  convert hbound using 1 <;> ring

/-- Sharp-lag version of finite van der Corput: for positive `H`, only
forward correlations with `d < H` occur. -/
theorem norm_sum_sq_mul_shift_le_forwardCorrelations_sharp
    (a : ℕ → ℂ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖ ^ 2 ≤
      2 * ((N + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range H, ‖weylForwardCorrelation a N d‖ := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hcombined :
      (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, a n‖ ^ 2 ≤
        ((N + H : ℕ) : ℝ) *
          (2 * (H : ℝ) *
            ∑ d ∈ Finset.range H,
              ‖weylForwardCorrelation a N d‖) :=
    (norm_sum_sq_mul_shift_sq_le a N H).trans
      (mul_le_mul_of_nonneg_left
        (sum_weylWindowSum_norm_sq_le_forwardCorrelations_of_pos a N H hH)
        (Nat.cast_nonneg (N + H)))
  refine le_of_mul_le_mul_left ?_ hHR
  convert hcombined using 1 <;> ring

/-- One forward finite difference of a real phase. -/
def forwardPhaseDifference (phase : ℕ → ℝ) (d n : ℕ) : ℝ :=
  phase (n + d) - phase n

/-- One real forward difference with a natural-number shift. -/
def realForwardDifferenceNat (f : ℝ → ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  f (x + d) - f x

/-- A real forward difference is exactly the interval integral of the
derivative. -/
theorem realForwardDifferenceNat_eq_intervalIntegral_deriv
    {f : ℝ → ℝ} (d : ℕ) (x : ℝ)
    (hdiff : ∀ y ∈ Set.uIcc x (x + d), DifferentiableAt ℝ f y)
    (hint : IntervalIntegrable (deriv f) MeasureTheory.volume x (x + d)) :
    realForwardDifferenceNat f d x =
      ∫ y in x..(x + d), deriv f y := by
  unfold realForwardDifferenceNat
  symm
  exact intervalIntegral.integral_deriv_eq_sub hdiff hint

/-- An upper derivative bound controls one finite difference by the shift
length times that bound. -/
theorem abs_realForwardDifferenceNat_le_mul_of_abs_deriv_le
    {f : ℝ → ℝ} (d : ℕ) (x C : ℝ)
    (hdiff : ∀ y ∈ Set.uIcc x (x + d), DifferentiableAt ℝ f y)
    (hint : IntervalIntegrable (deriv f) MeasureTheory.volume x (x + d))
    (hbound : ∀ y ∈ Set.uIoc x (x + d), |deriv f y| ≤ C) :
    |realForwardDifferenceNat f d x| ≤ (d : ℝ) * C := by
  rw [realForwardDifferenceNat_eq_intervalIntegral_deriv d x hdiff hint]
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ y in x..(x + d), deriv f y‖ ≤ C * |(x + d) - x| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      simpa [Real.norm_eq_abs] using hbound y hy
    _ = (d : ℝ) * C := by
      rw [show (x + (d : ℝ)) - x = d by ring]
      rw [abs_of_nonneg (by positivity)]
      ring

/-- A positive lower derivative bound gives the matching signed lower bound
for one finite difference. -/
theorem mul_le_realForwardDifferenceNat_of_le_deriv
    {f : ℝ → ℝ} (d : ℕ) (x c : ℝ)
    (hdiff : ∀ y ∈ Set.uIcc x (x + d), DifferentiableAt ℝ f y)
    (hint : IntervalIntegrable (deriv f) MeasureTheory.volume x (x + d))
    (hlower : ∀ y ∈ Set.Icc x (x + d), c ≤ deriv f y) :
    (d : ℝ) * c ≤ realForwardDifferenceNat f d x := by
  rw [realForwardDifferenceNat_eq_intervalIntegral_deriv d x hdiff hint]
  calc
    (d : ℝ) * c = ∫ _y in x..(x + d), c := by simp
    _ ≤ ∫ y in x..(x + d), deriv f y := by
      exact intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
        (hab := by exact le_add_of_nonneg_right (Nat.cast_nonneg d))
        (hf := intervalIntegrable_const) (hg := hint) hlower

/-- A negative upper derivative bound gives the matching signed upper bound
for one finite difference. -/
theorem realForwardDifferenceNat_le_neg_mul_of_deriv_le_neg
    {f : ℝ → ℝ} (d : ℕ) (x c : ℝ)
    (hdiff : ∀ y ∈ Set.uIcc x (x + d), DifferentiableAt ℝ f y)
    (hint : IntervalIntegrable (deriv f) MeasureTheory.volume x (x + d))
    (hupper : ∀ y ∈ Set.Icc x (x + d), deriv f y ≤ -c) :
    realForwardDifferenceNat f d x ≤ -((d : ℝ) * c) := by
  rw [realForwardDifferenceNat_eq_intervalIntegral_deriv d x hdiff hint]
  calc
    (∫ y in x..(x + d), deriv f y) ≤ ∫ _y in x..(x + d), -c := by
      exact intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
        (hab := by exact le_add_of_nonneg_right (Nat.cast_nonneg d))
        (hf := hint) (hg := intervalIntegrable_const) hupper
    _ = -((d : ℝ) * c) := by simp

/-- A negative upper derivative bound also gives an absolute lower bound for
one finite difference. -/
theorem mul_le_abs_realForwardDifferenceNat_of_deriv_le_neg
    {f : ℝ → ℝ} (d : ℕ) (x c : ℝ)
    (hdiff : ∀ y ∈ Set.uIcc x (x + d), DifferentiableAt ℝ f y)
    (hint : IntervalIntegrable (deriv f) MeasureTheory.volume x (x + d))
    (hupper : ∀ y ∈ Set.Icc x (x + d), deriv f y ≤ -c) :
    (d : ℝ) * c ≤ |realForwardDifferenceNat f d x| := by
  have hneg := realForwardDifferenceNat_le_neg_mul_of_deriv_le_neg
    d x c hdiff hint hupper
  calc
    (d : ℝ) * c ≤ -realForwardDifferenceNat f d x := by linarith
    _ ≤ |realForwardDifferenceNat f d x| := neg_le_abs _

/-- Sign-independent derivative separation implies an absolute finite-
difference lower bound. -/
theorem mul_le_abs_realForwardDifferenceNat_of_deriv_separated
    {f : ℝ → ℝ} (d : ℕ) (x c : ℝ)
    (hdiff : ∀ y ∈ Set.uIcc x (x + d), DifferentiableAt ℝ f y)
    (hint : IntervalIntegrable (deriv f) MeasureTheory.volume x (x + d))
    (hsep :
      (∀ y ∈ Set.Icc x (x + d), c ≤ deriv f y) ∨
      (∀ y ∈ Set.Icc x (x + d), deriv f y ≤ -c)) :
    (d : ℝ) * c ≤ |realForwardDifferenceNat f d x| := by
  rcases hsep with hlower | hupper
  · exact (mul_le_realForwardDifferenceNat_of_le_deriv
      d x c hdiff hint hlower).trans (le_abs_self _)
  · exact mul_le_abs_realForwardDifferenceNat_of_deriv_le_neg
      d x c hdiff hint hupper

/-- Iterated real forward differences with the same natural lag lists used
by the discrete exponential-sum recursion. -/
def iteratedRealForwardDifferenceNat (f : ℝ → ℝ) :
    List ℕ → ℝ → ℝ
  | [], x => f x
  | d :: ds, x =>
      iteratedRealForwardDifferenceNat (realForwardDifferenceNat f d) ds x

/-- Appending a lag applies its real forward difference after all previous
lags. -/
theorem iteratedRealForwardDifferenceNat_append_singleton
    (f : ℝ → ℝ) (ds : List ℕ) (d : ℕ) :
    iteratedRealForwardDifferenceNat f (ds ++ [d]) =
      realForwardDifferenceNat (iteratedRealForwardDifferenceNat f ds) d := by
  induction ds generalizing f with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, iteratedRealForwardDifferenceNat]
      rw [ih]

/-- Differentiation commutes with one real forward difference whenever the
original derivative exists at both endpoints. -/
theorem HasDerivAt.realForwardDifferenceNat
    {f : ℝ → ℝ} {f'x f'xd x : ℝ} (d : ℕ)
    (hxd : HasDerivAt f f'xd (x + d)) (hx : HasDerivAt f f'x x) :
    HasDerivAt (realForwardDifferenceNat f d) (f'xd - f'x) x := by
  simpa only [realForwardDifferenceNat] using
    (hxd.comp_add_const x (d : ℝ)).sub hx

/-- Differentiation commutes with every iterated real forward difference.
The global hypothesis is deliberately generic; later interval-local forms
can discharge it from the reciprocal phase away from zero. -/
theorem hasDerivAt_iteratedRealForwardDifferenceNat
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (ds : List ℕ) (x : ℝ) :
    HasDerivAt (iteratedRealForwardDifferenceNat f ds)
      (iteratedRealForwardDifferenceNat f' ds x) x := by
  induction ds generalizing f f' with
  | nil => exact hf x
  | cons d ds ih =>
      apply ih
      intro y
      exact HasDerivAt.realForwardDifferenceNat d (hf (y + d)) (hf y)

/-- Every iterated derivative commutes with one real forward difference when
the original function has the required smoothness at both endpoints. -/
theorem iteratedDeriv_realForwardDifferenceNat
    {f : ℝ → ℝ} (r d : ℕ) {x : ℝ}
    (hxd : ContDiffAt ℝ r f (x + d)) (hx : ContDiffAt ℝ r f x) :
    iteratedDeriv r (realForwardDifferenceNat f d) x =
      realForwardDifferenceNat (iteratedDeriv r f) d x := by
  have hshift : ContDiffAt ℝ r (fun y => f (y + (d : ℝ))) x :=
    hxd.comp x (contDiffAt_id.add contDiffAt_const)
  unfold realForwardDifferenceNat
  change iteratedDeriv r ((fun y => f (y + (d : ℝ))) - f) x = _
  rw [iteratedDeriv_sub hshift hx]
  rw [congrFun (iteratedDeriv_comp_add_const r f (d : ℝ)) x]

/-- Pointwise finite smoothness descends to an iterated one-dimensional
derivative, retaining the unused number of derivatives. -/
theorem ContDiffAt.iteratedDeriv_right
    {f : ℝ → ℝ} {n m i : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hmi : m + i ≤ n) :
    ContDiffAt ℝ m (iteratedDeriv i f) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin i) ℝ).symm.contDiff.contDiffAt.comp
    x (hf.iteratedFDeriv_right (by exact_mod_cast hmi))

/-- A `C^(k+1)` function has the expected derivative of its `k`-th iterated
one-dimensional derivative. -/
theorem hasDerivAt_iteratedDeriv_of_contDiffAt
    {f : ℝ → ℝ} (k : ℕ) {x : ℝ}
    (hf : ContDiffAt ℝ (k + 1) f x) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hdiff : DifferentiableAt ℝ (iteratedDeriv k f) x :=
    (ContDiffAt.iteratedDeriv_right hf (m := 1) (i := k)
      (by exact_mod_cast (show 1 + k ≤ k + 1 by omega))).differentiableAt_one
  rw [iteratedDeriv_succ]
  exact hdiff.hasDerivAt

/-- A global bound for the derivative whose order equals the number of lags
controls the corresponding iterated finite difference by the product of those
lags. -/
theorem abs_iteratedRealForwardDifferenceNat_le_prod
    {f : ℝ → ℝ} (ds : List ℕ) (x C : ℝ)
    (hf : ContDiff ℝ ds.length f)
    (hbound : ∀ y, |iteratedDeriv ds.length f y| ≤ C) :
    |iteratedRealForwardDifferenceNat f ds x| ≤ (ds.prod : ℝ) * C := by
  induction ds generalizing f C x with
  | nil =>
      simpa [iteratedRealForwardDifferenceNat] using hbound x
  | cons d ds ih =>
      have hflen : ContDiff ℝ (ds.length + 1) f := by
        simpa using hf
      have hfweak : ContDiff ℝ ds.length f :=
        hflen.of_le (by exact_mod_cast Nat.le_succ ds.length)
      have hshift : ContDiff ℝ ds.length (fun y : ℝ => f (y + (d : ℝ))) :=
        hfweak.comp (contDiff_id.add contDiff_const)
      have hdelta : ContDiff ℝ ds.length (realForwardDifferenceNat f d) := by
        simpa only [realForwardDifferenceNat] using hshift.sub hfweak
      have hdeltaBound :
          ∀ y, |iteratedDeriv ds.length (realForwardDifferenceNat f d) y| ≤
            (d : ℝ) * C := by
        intro y
        rw [iteratedDeriv_realForwardDifferenceNat ds.length d
          hfweak.contDiffAt hfweak.contDiffAt]
        apply abs_realForwardDifferenceNat_le_mul_of_abs_deriv_le
        · intro z hz
          exact (hflen.differentiable_iteratedDeriv' ds.length).differentiableAt
        · rw [← iteratedDeriv_succ]
          exact (hflen.continuous_iteratedDeriv' (ds.length + 1)).intervalIntegrable _ _
        · intro z hz
          rw [← iteratedDeriv_succ]
          exact hbound z
      simpa only [iteratedRealForwardDifferenceNat, List.prod_cons, Nat.cast_mul,
        mul_assoc, mul_left_comm] using
        ih (f := realForwardDifferenceNat f d) (C := (d : ℝ) * C)
          (x := x) hdelta hdeltaBound

/-- A positive lower bound for the derivative whose order equals the number
of lags gives the matching signed lower bound for the iterated difference. -/
theorem prod_mul_le_iteratedRealForwardDifferenceNat_of_le_iteratedDeriv
    {f : ℝ → ℝ} (ds : List ℕ) (x c : ℝ)
    (hf : ContDiff ℝ ds.length f)
    (hlower : ∀ y, c ≤ iteratedDeriv ds.length f y) :
    (ds.prod : ℝ) * c ≤ iteratedRealForwardDifferenceNat f ds x := by
  induction ds generalizing f c x with
  | nil =>
      simpa [iteratedRealForwardDifferenceNat] using hlower x
  | cons d ds ih =>
      have hflen : ContDiff ℝ (ds.length + 1) f := by
        simpa using hf
      have hfweak : ContDiff ℝ ds.length f :=
        hflen.of_le (by exact_mod_cast Nat.le_succ ds.length)
      have hshift : ContDiff ℝ ds.length (fun y : ℝ => f (y + (d : ℝ))) :=
        hfweak.comp (contDiff_id.add contDiff_const)
      have hdelta : ContDiff ℝ ds.length (realForwardDifferenceNat f d) := by
        simpa only [realForwardDifferenceNat] using hshift.sub hfweak
      have hdeltaLower :
          ∀ y, (d : ℝ) * c ≤
            iteratedDeriv ds.length (realForwardDifferenceNat f d) y := by
        intro y
        rw [iteratedDeriv_realForwardDifferenceNat ds.length d
          hfweak.contDiffAt hfweak.contDiffAt]
        apply mul_le_realForwardDifferenceNat_of_le_deriv
        · intro z hz
          exact (hflen.differentiable_iteratedDeriv' ds.length).differentiableAt
        · rw [← iteratedDeriv_succ]
          exact (hflen.continuous_iteratedDeriv' (ds.length + 1)).intervalIntegrable _ _
        · intro z hz
          rw [← iteratedDeriv_succ]
          exact hlower z
      simpa only [iteratedRealForwardDifferenceNat, List.prod_cons, Nat.cast_mul,
        mul_assoc, mul_left_comm] using
        ih (f := realForwardDifferenceNat f d) (c := (d : ℝ) * c)
          (x := x) hdelta hdeltaLower

/-- A negative upper bound for the derivative whose order equals the number
of lags gives the matching signed upper bound for the iterated difference. -/
theorem iteratedRealForwardDifferenceNat_le_neg_prod_mul_of_iteratedDeriv_le_neg
    {f : ℝ → ℝ} (ds : List ℕ) (x c : ℝ)
    (hf : ContDiff ℝ ds.length f)
    (hupper : ∀ y, iteratedDeriv ds.length f y ≤ -c) :
    iteratedRealForwardDifferenceNat f ds x ≤ -((ds.prod : ℝ) * c) := by
  induction ds generalizing f c x with
  | nil =>
      simpa [iteratedRealForwardDifferenceNat] using hupper x
  | cons d ds ih =>
      have hflen : ContDiff ℝ (ds.length + 1) f := by
        simpa using hf
      have hfweak : ContDiff ℝ ds.length f :=
        hflen.of_le (by exact_mod_cast Nat.le_succ ds.length)
      have hshift : ContDiff ℝ ds.length (fun y : ℝ => f (y + (d : ℝ))) :=
        hfweak.comp (contDiff_id.add contDiff_const)
      have hdelta : ContDiff ℝ ds.length (realForwardDifferenceNat f d) := by
        simpa only [realForwardDifferenceNat] using hshift.sub hfweak
      have hdeltaUpper :
          ∀ y, iteratedDeriv ds.length (realForwardDifferenceNat f d) y ≤
            -((d : ℝ) * c) := by
        intro y
        rw [iteratedDeriv_realForwardDifferenceNat ds.length d
          hfweak.contDiffAt hfweak.contDiffAt]
        apply realForwardDifferenceNat_le_neg_mul_of_deriv_le_neg
        · intro z hz
          exact (hflen.differentiable_iteratedDeriv' ds.length).differentiableAt
        · rw [← iteratedDeriv_succ]
          exact (hflen.continuous_iteratedDeriv' (ds.length + 1)).intervalIntegrable _ _
        · intro z hz
          rw [← iteratedDeriv_succ]
          exact hupper z
      simpa only [iteratedRealForwardDifferenceNat, List.prod_cons, Nat.cast_mul,
        mul_assoc, mul_left_comm] using
        ih (f := realForwardDifferenceNat f d) (c := (d : ℝ) * c)
          (x := x) hdelta hdeltaUpper

/-- A sign-independent derivative separation bound propagates through every
lag, gaining their exact product. -/
theorem prod_mul_le_abs_iteratedRealForwardDifferenceNat_of_iteratedDeriv_separated
    {f : ℝ → ℝ} (ds : List ℕ) (x c : ℝ)
    (hf : ContDiff ℝ ds.length f)
    (hsep :
      (∀ y, c ≤ iteratedDeriv ds.length f y) ∨
      (∀ y, iteratedDeriv ds.length f y ≤ -c)) :
    (ds.prod : ℝ) * c ≤ |iteratedRealForwardDifferenceNat f ds x| := by
  rcases hsep with hlower | hupper
  · exact (prod_mul_le_iteratedRealForwardDifferenceNat_of_le_iteratedDeriv
      ds x c hf hlower).trans (le_abs_self _)
  · have hneg :=
      iteratedRealForwardDifferenceNat_le_neg_prod_mul_of_iteratedDeriv_le_neg
        ds x c hf hupper
    calc
      (ds.prod : ℝ) * c ≤ -iteratedRealForwardDifferenceNat f ds x := by linarith
      _ ≤ |iteratedRealForwardDifferenceNat f ds x| := neg_le_abs _

/-- Positive-ray version of derivative commutation.  Natural shifts preserve
positivity, so this is the form applicable to reciprocal phases. -/
theorem hasDerivAt_iteratedRealForwardDifferenceNat_of_pos
    {f f' : ℝ → ℝ}
    (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (ds : List ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedRealForwardDifferenceNat f ds)
      (iteratedRealForwardDifferenceNat f' ds x) x := by
  induction ds generalizing f f' x with
  | nil => exact hf x hx
  | cons d ds ih =>
      apply ih
      · intro y hy
        apply HasDerivAt.realForwardDifferenceNat d
        · exact hf (y + d) (by positivity)
        · exact hf y hy
      · exact hx

/-- Positive-ray continuity is preserved by every natural-lag finite
difference. -/
theorem continuousAt_iteratedRealForwardDifferenceNat_of_pos
    {f : ℝ → ℝ} (hf : ∀ y, 0 < y → ContinuousAt f y)
    (ds : List ℕ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (iteratedRealForwardDifferenceNat f ds) x := by
  induction ds generalizing f x with
  | nil => exact hf x hx
  | cons d ds ih =>
      apply ih
      · intro y hy
        have hadd : ContinuousAt (fun z : ℝ => z + (d : ℝ)) y :=
          continuousAt_id.add continuousAt_const
        have hcomp : ContinuousAt (f ∘ fun z : ℝ => z + (d : ℝ)) y :=
          ContinuousAt.comp (hf (y + d) (by positivity)) hadd
        have hcomp' : ContinuousAt (fun z : ℝ => f (z + (d : ℝ))) y := by
          simpa [Function.comp_def] using hcomp
        exact hcomp'.sub (hf y hy)
      · exact hx

/-- On the positive ray, appending one lag expresses the full iterated
difference as the interval integral of the preceding differences of the
derivative. -/
theorem iteratedRealForwardDifferenceNat_append_eq_intervalIntegral_of_pos
    {f f' : ℝ → ℝ}
    (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hf' : ∀ y, 0 < y → ContinuousAt f' y)
    (ds : List ℕ) (d : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedRealForwardDifferenceNat f (ds ++ [d]) x =
      ∫ y in x..(x + d), iteratedRealForwardDifferenceNat f' ds y := by
  rw [iteratedRealForwardDifferenceNat_append_singleton]
  have hxxd : x ≤ x + d := le_add_of_nonneg_right (Nat.cast_nonneg d)
  have hpos : ∀ y ∈ Set.uIcc x (x + d), 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hxxd] at hy
    exact hx.trans_le hy.1
  have hd := fun y (hy : y ∈ Set.uIcc x (x + d)) =>
    hasDerivAt_iteratedRealForwardDifferenceNat_of_pos hf ds (hpos y hy)
  have hcont : ContinuousOn
      (iteratedRealForwardDifferenceNat f' ds) (Set.uIcc x (x + d)) := by
    intro y hy
    exact (continuousAt_iteratedRealForwardDifferenceNat_of_pos
      hf' ds (hpos y hy)).continuousWithinAt
  have hcontDeriv : ContinuousOn
      (deriv (iteratedRealForwardDifferenceNat f ds))
      (Set.uIcc x (x + d)) := by
    exact hcont.congr fun y hy => (hd y hy).deriv
  rw [realForwardDifferenceNat_eq_intervalIntegral_deriv d x
    (fun y hy => (hd y hy).differentiableAt) hcontDeriv.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro y hy
  exact (hd y hy).deriv

/-- A derivative chain on the positive ray gives an exact local product bound
for every lag list.  The top derivative only needs to be bounded on the
smallest interval containing all evaluation points. -/
theorem abs_iteratedRealForwardDifferenceNat_le_prod_of_pos
    (fs : ℕ → ℝ → ℝ) (ds : List ℕ) (x C : ℝ) (hx : 0 < x)
    (hderiv : ∀ k < ds.length, ∀ y, 0 < y →
      HasDerivAt (fs k) (fs (k + 1) y) y)
    (hcont : ∀ k ≤ ds.length, ∀ y, 0 < y → ContinuousAt (fs k) y)
    (hbound : ∀ y, x ≤ y → y ≤ x + ds.sum → |fs ds.length y| ≤ C) :
    |iteratedRealForwardDifferenceNat (fs 0) ds x| ≤
      (ds.prod : ℝ) * C := by
  induction ds using List.reverseRecOn generalizing fs C x with
  | nil =>
      simpa [iteratedRealForwardDifferenceNat] using hbound x le_rfl (by simp)
  | append_singleton ds d ih =>
      have hlen : (ds ++ [d]).length = ds.length + 1 := by simp
      have hFTC :=
        iteratedRealForwardDifferenceNat_append_eq_intervalIntegral_of_pos
          (f := fs 0) (f' := fs 1)
          (fun y hy => hderiv 0 (by simp [hlen]) y hy)
          (fun y hy => hcont 1 (by simp [hlen]) y hy) ds d hx
      rw [hFTC]
      rw [← Real.norm_eq_abs]
      calc
        ‖∫ y in x..(x + d), iteratedRealForwardDifferenceNat (fs 1) ds y‖ ≤
            ((ds.prod : ℝ) * C) * |(x + d) - x| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro y hy
          rw [Real.norm_eq_abs]
          apply ih (fs := fun k => fs (k + 1)) (C := C)
          · rw [Set.uIoc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg d))] at hy
            exact hx.trans hy.1
          · intro k hk z hz
            exact hderiv (k + 1) (by simpa [hlen] using Nat.succ_lt_succ hk) z hz
          · intro k hk z hz
            exact hcont (k + 1) (by simpa [hlen] using Nat.succ_le_succ hk) z hz
          · intro z hyz hzy
            rw [Set.uIoc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg d))] at hy
            have hxz : x ≤ z := (le_of_lt hy.1).trans hyz
            have hzu : z ≤ x + (ds ++ [d]).sum := by
              calc
                z ≤ y + ds.sum := hzy
                _ ≤ x + (ds ++ [d]).sum := by
                  simp only [List.sum_append, List.sum_singleton, Nat.cast_add]
                  linarith [hy.2]
            simpa [hlen] using hbound z hxz hzu
        _ = (((ds ++ [d]).prod : ℕ) : ℝ) * C := by
          rw [show (x + (d : ℝ)) - x = d by ring, abs_of_nonneg (Nat.cast_nonneg d)]
          simp only [List.prod_append, List.prod_singleton, Nat.cast_mul]
          ring

/-- A positive top derivative on the exact evaluation interval gives the
matching signed local product lower bound. -/
theorem prod_mul_le_iteratedRealForwardDifferenceNat_of_pos
    (fs : ℕ → ℝ → ℝ) (ds : List ℕ) (x c : ℝ) (hx : 0 < x)
    (hderiv : ∀ k < ds.length, ∀ y, 0 < y →
      HasDerivAt (fs k) (fs (k + 1) y) y)
    (hcont : ∀ k ≤ ds.length, ∀ y, 0 < y → ContinuousAt (fs k) y)
    (hlower : ∀ y, x ≤ y → y ≤ x + ds.sum → c ≤ fs ds.length y) :
    (ds.prod : ℝ) * c ≤ iteratedRealForwardDifferenceNat (fs 0) ds x := by
  induction ds using List.reverseRecOn generalizing fs c x with
  | nil =>
      simpa [iteratedRealForwardDifferenceNat] using hlower x le_rfl (by simp)
  | append_singleton ds d ih =>
      have hlen : (ds ++ [d]).length = ds.length + 1 := by simp
      have hFTC :=
        iteratedRealForwardDifferenceNat_append_eq_intervalIntegral_of_pos
          (f := fs 0) (f' := fs 1)
          (fun y hy => hderiv 0 (by simp [hlen]) y hy)
          (fun y hy => hcont 1 (by simp [hlen]) y hy) ds d hx
      rw [hFTC]
      have hxxd : x ≤ x + d := le_add_of_nonneg_right (Nat.cast_nonneg d)
      have hint : IntervalIntegrable
          (iteratedRealForwardDifferenceNat (fs 1) ds)
          MeasureTheory.volume x (x + d) := by
        apply ContinuousOn.intervalIntegrable
        intro y hy
        rw [Set.uIcc_of_le hxxd] at hy
        exact (continuousAt_iteratedRealForwardDifferenceNat_of_pos
          (fun z hz => hcont 1 (by simp [hlen]) z hz) ds
          (hx.trans_le hy.1)).continuousWithinAt
      calc
        (((ds ++ [d]).prod : ℕ) : ℝ) * c =
            ∫ _y in x..(x + d), (ds.prod : ℝ) * c := by
          simp only [List.prod_append, List.prod_singleton, Nat.cast_mul]
          simp
          ring
        _ ≤ ∫ y in x..(x + d),
            iteratedRealForwardDifferenceNat (fs 1) ds y := by
          apply intervalIntegral.integral_mono_on hxxd intervalIntegrable_const hint
          intro y hy
          apply ih (fs := fun k => fs (k + 1)) (c := c)
          · exact hx.trans_le hy.1
          · intro k hk z hz
            exact hderiv (k + 1) (by simpa [hlen] using Nat.succ_lt_succ hk) z hz
          · intro k hk z hz
            exact hcont (k + 1) (by simpa [hlen] using Nat.succ_le_succ hk) z hz
          · intro z hyz hzy
            have hxz : x ≤ z := hy.1.trans hyz
            have hzu : z ≤ x + (ds ++ [d]).sum := by
              calc
                z ≤ y + ds.sum := hzy
                _ ≤ x + (ds ++ [d]).sum := by
                  simp only [List.sum_append, List.sum_singleton, Nat.cast_add]
                  linarith [hy.2]
            simpa [hlen] using hlower z hxz hzu

/-- A negative top derivative on the exact evaluation interval gives the
matching signed local product upper bound. -/
theorem iteratedRealForwardDifferenceNat_le_neg_prod_mul_of_pos
    (fs : ℕ → ℝ → ℝ) (ds : List ℕ) (x c : ℝ) (hx : 0 < x)
    (hderiv : ∀ k < ds.length, ∀ y, 0 < y →
      HasDerivAt (fs k) (fs (k + 1) y) y)
    (hcont : ∀ k ≤ ds.length, ∀ y, 0 < y → ContinuousAt (fs k) y)
    (hupper : ∀ y, x ≤ y → y ≤ x + ds.sum → fs ds.length y ≤ -c) :
    iteratedRealForwardDifferenceNat (fs 0) ds x ≤
      -((ds.prod : ℝ) * c) := by
  induction ds using List.reverseRecOn generalizing fs c x with
  | nil =>
      simpa [iteratedRealForwardDifferenceNat] using hupper x le_rfl (by simp)
  | append_singleton ds d ih =>
      have hlen : (ds ++ [d]).length = ds.length + 1 := by simp
      have hFTC :=
        iteratedRealForwardDifferenceNat_append_eq_intervalIntegral_of_pos
          (f := fs 0) (f' := fs 1)
          (fun y hy => hderiv 0 (by simp [hlen]) y hy)
          (fun y hy => hcont 1 (by simp [hlen]) y hy) ds d hx
      rw [hFTC]
      have hxxd : x ≤ x + d := le_add_of_nonneg_right (Nat.cast_nonneg d)
      have hint : IntervalIntegrable
          (iteratedRealForwardDifferenceNat (fs 1) ds)
          MeasureTheory.volume x (x + d) := by
        apply ContinuousOn.intervalIntegrable
        intro y hy
        rw [Set.uIcc_of_le hxxd] at hy
        exact (continuousAt_iteratedRealForwardDifferenceNat_of_pos
          (fun z hz => hcont 1 (by simp [hlen]) z hz) ds
          (hx.trans_le hy.1)).continuousWithinAt
      calc
        (∫ y in x..(x + d),
            iteratedRealForwardDifferenceNat (fs 1) ds y) ≤
            ∫ _y in x..(x + d), -((ds.prod : ℝ) * c) := by
          apply intervalIntegral.integral_mono_on hxxd hint intervalIntegrable_const
          intro y hy
          apply ih (fs := fun k => fs (k + 1)) (c := c)
          · exact hx.trans_le hy.1
          · intro k hk z hz
            exact hderiv (k + 1) (by simpa [hlen] using Nat.succ_lt_succ hk) z hz
          · intro k hk z hz
            exact hcont (k + 1) (by simpa [hlen] using Nat.succ_le_succ hk) z hz
          · intro z hyz hzy
            have hxz : x ≤ z := hy.1.trans hyz
            have hzu : z ≤ x + (ds ++ [d]).sum := by
              calc
                z ≤ y + ds.sum := hzy
                _ ≤ x + (ds ++ [d]).sum := by
                  simp only [List.sum_append, List.sum_singleton, Nat.cast_add]
                  linarith [hy.2]
            simpa [hlen] using hupper z hxz hzu
        _ = -((((ds ++ [d]).prod : ℕ) : ℝ) * c) := by
          simp only [List.prod_append, List.prod_singleton, Nat.cast_mul]
          simp
          ring

/-- Sign-independent derivative separation on the exact positive evaluation
interval propagates through all lags with their exact product. -/
theorem prod_mul_le_abs_iteratedRealForwardDifferenceNat_of_pos_separated
    (fs : ℕ → ℝ → ℝ) (ds : List ℕ) (x c : ℝ) (hx : 0 < x)
    (hderiv : ∀ k < ds.length, ∀ y, 0 < y →
      HasDerivAt (fs k) (fs (k + 1) y) y)
    (hcont : ∀ k ≤ ds.length, ∀ y, 0 < y → ContinuousAt (fs k) y)
    (hsep :
      (∀ y, x ≤ y → y ≤ x + ds.sum → c ≤ fs ds.length y) ∨
      (∀ y, x ≤ y → y ≤ x + ds.sum → fs ds.length y ≤ -c)) :
    (ds.prod : ℝ) * c ≤
      |iteratedRealForwardDifferenceNat (fs 0) ds x| := by
  rcases hsep with hlower | hupper
  · exact (prod_mul_le_iteratedRealForwardDifferenceNat_of_pos
      fs ds x c hx hderiv hcont hlower).trans (le_abs_self _)
  · have hneg := iteratedRealForwardDifferenceNat_le_neg_prod_mul_of_pos
      fs ds x c hx hderiv hcont hupper
    calc
      (ds.prod : ℝ) * c ≤
          -iteratedRealForwardDifferenceNat (fs 0) ds x := by linarith
      _ ≤ |iteratedRealForwardDifferenceNat (fs 0) ds x| := neg_le_abs _

/-- Positive-ray local product upper bound specialized to the source
reciprocal phase. -/
theorem abs_iteratedRealForwardDifferenceNat_reciprocalPhase_le_prod_of_pos
    (N M : ℝ) (j : ℕ) (ds : List ℕ) (x C : ℝ) (hx : 0 < x)
    (hbound : ∀ y, x ≤ y → y ≤ x + ds.sum →
      |iteratedDeriv ds.length (reciprocalPhase N M j) y| ≤ C) :
    |iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds x| ≤
      (ds.prod : ℝ) * C := by
  simpa using abs_iteratedRealForwardDifferenceNat_le_prod_of_pos
    (fs := fun k => iteratedDeriv k (reciprocalPhase N M j)) ds x C hx
    (by
      intro k hk y hy
      exact hasDerivAt_iteratedDeriv_of_contDiffAt k
        (contDiffAt_reciprocalPhase_of_pos N M j (k + 1) hy))
    (by
      intro k hk y hy
      exact (ContDiffAt.iteratedDeriv_right
        (contDiffAt_reciprocalPhase_of_pos N M j k hy)
        (m := 0) (i := k) (by omega)).continuousAt)
    hbound

/-- Positive-ray local derivative separation specialized to the source
reciprocal phase. -/
theorem prod_mul_le_abs_iteratedRealForwardDifferenceNat_reciprocalPhase_of_pos_separated
    (N M : ℝ) (j : ℕ) (ds : List ℕ) (x c : ℝ) (hx : 0 < x)
    (hsep :
      (∀ y, x ≤ y → y ≤ x + ds.sum →
        c ≤ iteratedDeriv ds.length (reciprocalPhase N M j) y) ∨
      (∀ y, x ≤ y → y ≤ x + ds.sum →
        iteratedDeriv ds.length (reciprocalPhase N M j) y ≤ -c)) :
    (ds.prod : ℝ) * c ≤
      |iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds x| := by
  simpa using
    prod_mul_le_abs_iteratedRealForwardDifferenceNat_of_pos_separated
      (fs := fun k => iteratedDeriv k (reciprocalPhase N M j)) ds x c hx
      (by
        intro k hk y hy
        exact hasDerivAt_iteratedDeriv_of_contDiffAt k
          (contDiffAt_reciprocalPhase_of_pos N M j (k + 1) hy))
      (by
        intro k hk y hy
        exact (ContDiffAt.iteratedDeriv_right
          (contDiffAt_reciprocalPhase_of_pos N M j k hy)
          (m := 0) (i := k) (by omega)).continuousAt)
      hsep

/-- The normalized source derivative estimate converted to a raw derivative
bound on `[X, ∞)`. -/
theorem abs_iteratedDeriv_reciprocalPhase_le_scale_div_pow
    (N M : ℝ) {j r : ℕ} (hj : 1 ≤ j) {X t : ℝ}
    (hX : 0 < X) (hXt : X ≤ t) :
    |iteratedDeriv r (reciprocalPhase N M j) t| ≤
      (r.factorial : ℝ) *
          ((((r + j) ^ r : ℕ) : ℝ) * reciprocalPhaseScale N M j X) /
        X ^ r := by
  have ht : 0 < t := hX.trans_le hXt
  have hraw := normalized_abs_iteratedDeriv_reciprocalPhase_le_multiplier_scale
    N M (j := j) (r := r) hj hX hXt
  have hfac : (0 : ℝ) < r.factorial := by positivity
  have htPow : 0 < t ^ r := pow_pos ht r
  have hXpow : 0 < X ^ r := pow_pos hX r
  let K : ℝ := (((r + j) ^ r : ℕ) : ℝ) * reciprocalPhaseScale N M j X
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _)
    (reciprocalPhaseScale_nonneg N M j hX)
  have hfirst : |iteratedDeriv r (reciprocalPhase N M j) t| ≤
      (r.factorial : ℝ) * K / t ^ r := by
    rw [le_div_iff₀ htPow]
    rw [div_mul_eq_mul_div] at hraw
    have hmul := (div_le_iff₀ hfac).mp hraw
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hpow : X ^ r ≤ t ^ r := pow_le_pow_left₀ hX.le hXt r
  calc
    |iteratedDeriv r (reciprocalPhase N M j) t| ≤
        (r.factorial : ℝ) * K / t ^ r := hfirst
    _ ≤ (r.factorial : ℝ) * K / X ^ r := by
      exact div_le_div_of_nonneg_left (mul_nonneg hfac.le hK) hXpow hpow
    _ = (r.factorial : ℝ) *
          ((((r + j) ^ r : ℕ) : ℝ) * reciprocalPhaseScale N M j X) /
        X ^ r := by rfl

/-- Fully explicit positive-ray upper bound for a reciprocal-phase iterated
finite difference.  It combines the source derivative scale with the exact
product of the Weyl lags. -/
theorem abs_iteratedRealForwardDifferenceNat_reciprocalPhase_le_product_scale
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) (ds : List ℕ) {x : ℝ} (hx : 0 < x) :
    |iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds x| ≤
      (ds.prod : ℝ) *
        ((ds.length.factorial : ℝ) *
            ((((ds.length + j) ^ ds.length : ℕ) : ℝ) *
              reciprocalPhaseScale N M j x) /
          x ^ ds.length) := by
  apply abs_iteratedRealForwardDifferenceNat_reciprocalPhase_le_prod_of_pos
  · exact hx
  · intro y hxy hyTop
    exact abs_iteratedDeriv_reciprocalPhase_le_scale_div_pow
      N M hj hx hxy

/-- A continuous real function bounded in absolute value away from zero on a
nonempty interval has one constant sign there, with the same quantitative
separation. -/
theorem continuousOn_sign_separated_of_abs_lower
    {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hcont : ContinuousOn f (Set.Icc a b))
    (habs : ∀ y ∈ Set.Icc a b, c ≤ |f y|) :
    (∀ y ∈ Set.Icc a b, c ≤ f y) ∨
      (∀ y ∈ Set.Icc a b, f y ≤ -c) := by
  rcases le_total 0 (f a) with hfa | hfa
  · left
    intro y hy
    have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
    have hnonneg : 0 ≤ f y := by
      by_contra hyneg
      have hyle : f y ≤ 0 := le_of_not_ge hyneg
      obtain ⟨z, hz, hzero⟩ := isPreconnected_Icc.intermediate_value₂
        hy ha hcont continuousOn_const hyle hfa
      have hcz := habs z hz
      simp only [hzero, abs_zero] at hcz
      linarith
    simpa [abs_of_nonneg hnonneg] using habs y hy
  · right
    intro y hy
    have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
    have hnonpos : f y ≤ 0 := by
      by_contra hypos
      have hyle : 0 ≤ f y := le_of_not_ge hypos
      obtain ⟨z, hz, hzero⟩ := isPreconnected_Icc.intermediate_value₂
        ha hy hcont continuousOn_const hfa hyle
      have hcz := habs z hz
      simp only [hzero, abs_zero] at hcz
      linarith
    have hcy := habs y hy
    rw [abs_of_nonpos hnonpos] at hcy
    linarith

/-- A pointwise absolute lower bound for the source reciprocal derivative on
the exact evaluation interval automatically has constant sign and therefore
propagates to its iterated finite difference with the exact lag product. -/
theorem prod_mul_le_abs_iteratedRealForwardDifferenceNat_reciprocalPhase_of_abs_lower
    (N M : ℝ) (j : ℕ) (ds : List ℕ) (x c : ℝ) (hx : 0 < x) (hc : 0 < c)
    (hlower : ∀ y ∈ Set.Icc x (x + ds.sum),
      c ≤ |iteratedDeriv ds.length (reciprocalPhase N M j) y|) :
    (ds.prod : ℝ) * c ≤
      |iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds x| := by
  have hinterval : x ≤ x + ds.sum :=
    le_add_of_nonneg_right (Nat.cast_nonneg ds.sum)
  have hcont : ContinuousOn
      (iteratedDeriv ds.length (reciprocalPhase N M j))
      (Set.Icc x (x + ds.sum)) := by
    intro y hy
    have hypos : 0 < y := hx.trans_le hy.1
    exact (ContDiffAt.iteratedDeriv_right
      (contDiffAt_reciprocalPhase_of_pos N M j ds.length hypos)
      (m := 0) (i := ds.length) (by omega)).continuousAt.continuousWithinAt
  have hsep := continuousOn_sign_separated_of_abs_lower
    hinterval hc hcont hlower
  apply prod_mul_le_abs_iteratedRealForwardDifferenceNat_reciprocalPhase_of_pos_separated
  · exact hx
  · rcases hsep with hpositive | hnegative
    · left
      intro y hxy hyTop
      exact hpositive y ⟨hxy, hyTop⟩
    · right
      intro y hxy hyTop
      exact hnegative y ⟨hxy, hyTop⟩

/-- A normalized lower bound for the reciprocal phase's top derivative is
converted into the explicit finite-difference lower bound on the exact
evaluation interval. -/
theorem prod_mul_normalizedLower_div_pow_le_abs_iteratedRealForwardDifferenceNat_reciprocalPhase
    (N M : ℝ) (j : ℕ) (ds : List ℕ) (x L : ℝ) (hx : 0 < x) (hL : 0 < L)
    (hlower : ∀ y ∈ Set.Icc x (x + ds.sum),
      L ≤ y ^ ds.length / (ds.length.factorial : ℝ) *
        |iteratedDeriv ds.length (reciprocalPhase N M j) y|) :
    (ds.prod : ℝ) *
        ((ds.length.factorial : ℝ) * L / (x + ds.sum) ^ ds.length) ≤
      |iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds x| := by
  have htop : 0 < x + (ds.sum : ℝ) := by positivity
  have hfac : (0 : ℝ) < ds.length.factorial := by positivity
  have hc : 0 < (ds.length.factorial : ℝ) * L /
      (x + ds.sum) ^ ds.length := by positivity
  apply prod_mul_le_abs_iteratedRealForwardDifferenceNat_reciprocalPhase_of_abs_lower
    N M j ds x _ hx hc
  intro y hy
  have hypos : 0 < y := hx.trans_le hy.1
  have hypow : 0 < y ^ ds.length := pow_pos hypos ds.length
  have htopPow : 0 < (x + ds.sum) ^ ds.length :=
    pow_pos htop ds.length
  have hpow : y ^ ds.length ≤ (x + ds.sum) ^ ds.length :=
    pow_le_pow_left₀ hypos.le hy.2 ds.length
  have hnorm := hlower y hy
  rw [div_mul_eq_mul_div] at hnorm
  have hmul : L * (ds.length.factorial : ℝ) ≤
      y ^ ds.length *
        |iteratedDeriv ds.length (reciprocalPhase N M j) y| :=
    (le_div_iff₀ hfac).mp hnorm
  rw [div_le_iff₀ htopPow]
  calc
    (ds.length.factorial : ℝ) * L ≤
        y ^ ds.length *
          |iteratedDeriv ds.length (reciprocalPhase N M j) y| := by
      simpa [mul_comm] using hmul
    _ ≤ (x + ds.sum) ^ ds.length *
          |iteratedDeriv ds.length (reciprocalPhase N M j) y| := by
      exact mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    _ = |iteratedDeriv ds.length (reciprocalPhase N M j) y| *
          (x + ds.sum) ^ ds.length := by ring

/-- The regular-set derivative lower bound after critical-interval deletion,
propagated all the way to the reciprocal phase's iterated finite difference. -/
theorem prod_mul_regularScale_div_pow_le_abs_iteratedRealForwardDifferenceNat_reciprocalPhase
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (ds : List ℕ)
    {X Y q x : ℝ} (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hxIcc : x ∈ Set.Icc X Y) (hevalY : x + ds.sum ≤ Y)
    (hevalTop : x + ds.sum ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc x (x + ds.sum),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : ds.length ∈ orders) :
    (ds.prod : ℝ) *
        ((ds.length.factorial : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
          (x + ds.sum) ^ ds.length) ≤
      |iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds x| := by
  apply prod_mul_normalizedLower_div_pow_le_abs_iteratedRealForwardDifferenceNat_reciprocalPhase
  · exact hX.trans_le hxIcc.1
  · positivity
  · intro y hy
    exact normalized_abs_iteratedDeriv_reciprocalPhase_ge_scale_mul_div_ten_of_regular
      N M orders hX hq hqOne hj
      ⟨hxIcc.1.trans hy.1, hy.2.trans hevalY⟩
      (hy.2.trans hevalTop) (hregular y hy) hr

/-- Iterated forward differences, in the order recorded by the lag list. -/
def iteratedForwardPhaseDifference (phase : ℕ → ℝ) :
    List ℕ → ℕ → ℝ
  | [], n => phase n
  | d :: ds, n =>
      iteratedForwardPhaseDifference (forwardPhaseDifference phase d) ds n

@[simp]
theorem iteratedForwardPhaseDifference_nil
    (phase : ℕ → ℝ) :
    iteratedForwardPhaseDifference phase [] = phase := rfl

@[simp]
theorem iteratedForwardPhaseDifference_cons
    (phase : ℕ → ℝ) (d : ℕ) (ds : List ℕ) :
    iteratedForwardPhaseDifference phase (d :: ds) =
      iteratedForwardPhaseDifference (forwardPhaseDifference phase d) ds := rfl

/-- Forward differences commute. -/
theorem forwardPhaseDifference_comm
    (phase : ℕ → ℝ) (d e : ℕ) :
    forwardPhaseDifference (forwardPhaseDifference phase d) e =
      forwardPhaseDifference (forwardPhaseDifference phase e) d := by
  funext n
  unfold forwardPhaseDifference
  have hadd : n + e + d = n + d + e := by omega
  rw [hadd]
  ring

/-- Sampling a real function on a translated integer lattice commutes with
one forward difference. -/
theorem forwardPhaseDifference_sample
    (f : ℝ → ℝ) (x : ℝ) (d : ℕ) :
    forwardPhaseDifference (fun n => f (x + n)) d =
      fun n : ℕ => realForwardDifferenceNat f d (x + n) := by
  funext n
  simp only [forwardPhaseDifference, realForwardDifferenceNat, Nat.cast_add]
  congr 2
  ring

/-- Sampling commutes with every finite list of forward differences. -/
theorem iteratedForwardPhaseDifference_sample
    (f : ℝ → ℝ) (x : ℝ) (ds : List ℕ) :
    iteratedForwardPhaseDifference (fun n => f (x + n)) ds =
      fun n : ℕ => iteratedRealForwardDifferenceNat f ds (x + n) := by
  induction ds generalizing f with
  | nil => rfl
  | cons d ds ih =>
      rw [iteratedForwardPhaseDifference_cons,
        forwardPhaseDifference_sample]
      exact ih (realForwardDifferenceNat f d)

/-- Appending a lag applies its forward difference after all previous lags.
This is the recursion law used by repeated van der Corput steps. -/
theorem iteratedForwardPhaseDifference_append_singleton
    (phase : ℕ → ℝ) (ds : List ℕ) (d : ℕ) :
    iteratedForwardPhaseDifference phase (ds ++ [d]) =
      forwardPhaseDifference (iteratedForwardPhaseDifference phase ds) d := by
  induction ds generalizing phase with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, iteratedForwardPhaseDifference_cons]
      rw [ih]

/-- The complex unit sequence attached to a real phase. -/
def phaseExponentialSequence (phase : ℕ → ℝ) (n : ℕ) : ℂ :=
  standardAdditiveCharacter (phase n)

/-- A phase exponential sum on the initial interval `[0,N)`. -/
def phaseExponentialSum (phase : ℕ → ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, phaseExponentialSequence phase n

@[simp]
theorem forwardPhaseDifference_zero (phase : ℕ → ℝ) :
    forwardPhaseDifference phase 0 = 0 := by
  funext n
  simp [forwardPhaseDifference]

@[simp]
theorem phaseExponentialSum_zero (N : ℕ) :
    phaseExponentialSum 0 N = (N : ℂ) := by
  simp [phaseExponentialSum, phaseExponentialSequence,
    standardAdditiveCharacter]

/-- Trivial length bound for every phase exponential sum. -/
theorem norm_phaseExponentialSum_le (phase : ℕ → ℝ) (N : ℕ) :
    ‖phaseExponentialSum phase N‖ ≤ (N : ℝ) := by
  calc
    ‖phaseExponentialSum phase N‖ ≤
        ∑ n ∈ Finset.range N, ‖phaseExponentialSequence phase n‖ := by
      exact norm_sum_le _ _
    _ = (N : ℝ) := by
      simp [phaseExponentialSequence, norm_standardAdditiveCharacter]

/-- Conversion between this development's turn-normalized additive character
and the radian-normalized phase used by the frozen Kusmin--Landau theorem. -/
theorem standardAdditiveCharacter_eq_unitaryPhase (x : ℝ) :
    standardAdditiveCharacter x =
      RiemannZeta.GuthMaynard.unitaryPhase (2 * Real.pi * x) := by
  unfold standardAdditiveCharacter RiemannZeta.GuthMaynard.unitaryPhase
  push_cast
  congr 1
  ring

/-- Turn-normalized Kusmin--Landau cancellation for increasing phase
increments contained in the single period `[δ, 1-δ]`. -/
theorem norm_phaseExponentialSum_le_inv_of_increments_increasing
    (phase : ℕ → ℝ) (L : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ n < L, δ ≤ phase (n + 1) - phase n)
    (hhigh : ∀ n < L, phase (n + 1) - phase n ≤ 1 - δ)
    (hmono : ∀ n, n + 1 < L →
      phase (n + 1) - phase n ≤ phase (n + 2) - phase (n + 1)) :
    ‖phaseExponentialSum phase L‖ ≤ 1 / δ := by
  by_cases hL : L = 0
  · subst L
    simp [phaseExponentialSum]
    positivity
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hL
    let f : ℕ → ℝ := fun n => 2 * Real.pi * phase n
    have hKL := RiemannZeta.GuthMaynard.kusminLandau_one_period
      f (L - 1) (2 * Real.pi * δ) (by positivity)
      (fun n hn => by
        dsimp only [f]
        have hnL : n < L := by omega
        have := hlow n hnL
        nlinarith [Real.pi_pos])
      (fun n hn => by
        dsimp only [f]
        have hnL : n < L := by omega
        have := hhigh n hnL
        nlinarith [Real.pi_pos])
      (fun n hn => by
        dsimp only [f]
        have hnL : n + 1 < L := by omega
        have := hmono n hnL
        nlinarith [Real.pi_pos])
    have hsum :
        phaseExponentialSum phase L =
          ∑ n ∈ Finset.range ((L - 1) + 1),
            RiemannZeta.GuthMaynard.unitaryPhase (f n) := by
      unfold phaseExponentialSum phaseExponentialSequence
      rw [Nat.sub_add_cancel hLpos]
      apply Finset.sum_congr rfl
      intro n hn
      exact standardAdditiveCharacter_eq_unitaryPhase (phase n)
    rw [hsum]
    calc
      ‖∑ n ∈ Finset.range (L - 1 + 1),
          RiemannZeta.GuthMaynard.unitaryPhase (f n)‖ ≤
          2 * Real.pi / (2 * Real.pi * δ) := hKL
      _ = 1 / δ := by field_simp [Real.pi_ne_zero]

/-- Turn-normalized Kusmin--Landau cancellation for decreasing phase
increments contained in the single period `[δ, 1-δ]`. -/
theorem norm_phaseExponentialSum_le_inv_of_increments_decreasing
    (phase : ℕ → ℝ) (L : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ n < L, δ ≤ phase (n + 1) - phase n)
    (hhigh : ∀ n < L, phase (n + 1) - phase n ≤ 1 - δ)
    (hmono : ∀ n, n + 1 < L →
      phase (n + 2) - phase (n + 1) ≤ phase (n + 1) - phase n) :
    ‖phaseExponentialSum phase L‖ ≤ 1 / δ := by
  by_cases hL : L = 0
  · subst L
    simp [phaseExponentialSum]
    positivity
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hL
    let f : ℕ → ℝ := fun n => 2 * Real.pi * phase n
    have hKL := RiemannZeta.GuthMaynard.kusminLandau_one_period_decreasing
      f (L - 1) (2 * Real.pi * δ) (by positivity)
      (fun n hn => by
        dsimp only [f]
        have hnL : n < L := by omega
        have := hlow n hnL
        nlinarith [Real.pi_pos])
      (fun n hn => by
        dsimp only [f]
        have hnL : n < L := by omega
        have := hhigh n hnL
        nlinarith [Real.pi_pos])
      (fun n hn => by
        dsimp only [f]
        have hnL : n + 1 < L := by omega
        have := hmono n hnL
        nlinarith [Real.pi_pos])
    have hsum :
        phaseExponentialSum phase L =
          ∑ n ∈ Finset.range ((L - 1) + 1),
            RiemannZeta.GuthMaynard.unitaryPhase (f n) := by
      unfold phaseExponentialSum phaseExponentialSequence
      rw [Nat.sub_add_cancel hLpos]
      apply Finset.sum_congr rfl
      intro n hn
      exact standardAdditiveCharacter_eq_unitaryPhase (phase n)
    rw [hsum]
    calc
      ‖∑ n ∈ Finset.range (L - 1 + 1),
          RiemannZeta.GuthMaynard.unitaryPhase (f n)‖ ≤
          2 * Real.pi / (2 * Real.pi * δ) := hKL
      _ = 1 / δ := by field_simp [Real.pi_ne_zero]

/-- Negating a real phase conjugates its finite exponential sum. -/
theorem phaseExponentialSum_neg (phase : ℕ → ℝ) (L : ℕ) :
    phaseExponentialSum (fun n => -phase n) L =
      starRingEnd ℂ (phaseExponentialSum phase L) := by
  unfold phaseExponentialSum phaseExponentialSequence
  simp_rw [standardAdditiveCharacter_neg]
  exact (map_sum (starRingEnd ℂ) _ _).symm

/-- Kusmin--Landau cancellation when the positive increments may be monotone
in either direction. -/
theorem norm_phaseExponentialSum_le_inv_of_positive_increments_monotone
    (phase : ℕ → ℝ) (L : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ n < L, δ ≤ phase (n + 1) - phase n)
    (hhigh : ∀ n < L, phase (n + 1) - phase n ≤ 1 - δ)
    (hmono :
      (∀ n, n + 1 < L →
        phase (n + 1) - phase n ≤ phase (n + 2) - phase (n + 1)) ∨
      (∀ n, n + 1 < L →
        phase (n + 2) - phase (n + 1) ≤ phase (n + 1) - phase n)) :
    ‖phaseExponentialSum phase L‖ ≤ 1 / δ := by
  rcases hmono with hinc | hdec
  · exact norm_phaseExponentialSum_le_inv_of_increments_increasing
      phase L hδ hlow hhigh hinc
  · exact norm_phaseExponentialSum_le_inv_of_increments_decreasing
      phase L hδ hlow hhigh hdec

/-- Sign-independent one-period Kusmin--Landau bound.  The increments may
all be positive or all negative and may be monotone in either direction. -/
theorem norm_phaseExponentialSum_le_inv_of_signed_increments_monotone
    (phase : ℕ → ℝ) (L : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hwindow :
      (∀ n < L,
        δ ≤ phase (n + 1) - phase n ∧
          phase (n + 1) - phase n ≤ 1 - δ) ∨
      (∀ n < L,
        δ ≤ -(phase (n + 1) - phase n) ∧
          -(phase (n + 1) - phase n) ≤ 1 - δ))
    (hmono :
      (∀ n, n + 1 < L →
        phase (n + 1) - phase n ≤ phase (n + 2) - phase (n + 1)) ∨
      (∀ n, n + 1 < L →
        phase (n + 2) - phase (n + 1) ≤ phase (n + 1) - phase n)) :
    ‖phaseExponentialSum phase L‖ ≤ 1 / δ := by
  rcases hwindow with hpos | hneg
  · apply norm_phaseExponentialSum_le_inv_of_positive_increments_monotone
      phase L hδ
    · exact fun n hn => (hpos n hn).1
    · exact fun n hn => (hpos n hn).2
    · exact hmono
  · have hbound :=
      norm_phaseExponentialSum_le_inv_of_positive_increments_monotone
        (fun n => -phase n) L hδ
        (fun n hn => by
          have h := (hneg n hn).1
          dsimp only
          linarith)
        (fun n hn => by
          have h := (hneg n hn).2
          dsimp only
          linarith)
        (by
          rcases hmono with hinc | hdec
          · right
            intro n hn
            have h := hinc n hn
            dsimp only
            linarith
          · left
            intro n hn
            have h := hdec n hn
            dsimp only
            linarith)
    rw [phaseExponentialSum_neg] at hbound
    simpa using hbound

/-- Mean-value representation of a unit phase increment. -/
theorem exists_phaseIncrement_eq_deriv
    {f f' : ℝ → ℝ} (x : ℝ)
    (hderiv : ∀ y ∈ Set.Icc x (x + 1), HasDerivAt f (f' y) y) :
    ∃ c ∈ Set.Ioo x (x + 1), f (x + 1) - f x = f' c := by
  have hcont : ContinuousOn f (Set.Icc x (x + 1)) := by
    intro y hy
    exact (hderiv y hy).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo x (x + 1)) := by
    intro y hy
    exact (hderiv y ⟨hy.1.le, hy.2.le⟩).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hslope⟩ :=
    exists_deriv_eq_slope f (by linarith : x < x + 1) hcont hdiff
  refine ⟨c, hc, ?_⟩
  rw [(hderiv c ⟨hc.1.le, hc.2.le⟩).deriv] at hslope
  have hden : x + 1 - x = 1 := by ring
  rw [hden, div_one] at hslope
  exact hslope.symm

/-- A signed first-derivative window transfers to unit sampled increments by
the mean value theorem, after which the discrete Kusmin--Landau estimate
applies.  Monotonicity is kept as a separate discrete input here. -/
theorem norm_phaseExponentialSum_sample_le_inv_of_deriv_window
    (f f' : ℝ → ℝ) (a : ℝ) (L : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ y ∈ Set.Icc a (a + L), HasDerivAt f (f' y) y)
    (hwindow :
      (∀ y ∈ Set.Icc a (a + L), δ ≤ f' y ∧ f' y ≤ 1 - δ) ∨
      (∀ y ∈ Set.Icc a (a + L), δ ≤ -f' y ∧ -f' y ≤ 1 - δ))
    (hmono :
      (∀ n, n + 1 < L →
        f (a + (n + 1 : ℕ)) - f (a + n) ≤
          f (a + (n + 2 : ℕ)) - f (a + (n + 1 : ℕ))) ∨
      (∀ n, n + 1 < L →
        f (a + (n + 2 : ℕ)) - f (a + (n + 1 : ℕ)) ≤
          f (a + (n + 1 : ℕ)) - f (a + n))) :
    ‖phaseExponentialSum (fun n => f (a + n)) L‖ ≤ 1 / δ := by
  have hincrement : ∀ n < L, ∃ c ∈ Set.Ioo (a + n) (a + n + 1),
      f (a + (n + 1 : ℕ)) - f (a + n) = f' c := by
    intro n hn
    have hnTop : ((n + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
    have hsub : Set.Icc (a + n) (a + n + 1) ⊆ Set.Icc a (a + L) := by
      intro y hy
      constructor
      · exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg n)) hy.1
      · push_cast at hnTop ⊢
        linarith [hy.2]
    obtain ⟨c, hc, heq⟩ := exists_phaseIncrement_eq_deriv
      (f := f) (f' := f') (a + n) (fun y hy => hderiv y (hsub hy))
    refine ⟨c, hc, ?_⟩
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using heq
  apply norm_phaseExponentialSum_le_inv_of_signed_increments_monotone
    (fun n => f (a + n)) L hδ
  · rcases hwindow with hpos | hneg
    · left
      intro n hn
      obtain ⟨c, hc, heq⟩ := hincrement n hn
      have hcGlobal : c ∈ Set.Icc a (a + L) := by
        have hnTop : ((n + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
        constructor
        · exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg n)) hc.1.le
        · push_cast at hnTop
          linarith [hc.2]
      simpa only [heq] using hpos c hcGlobal
    · right
      intro n hn
      obtain ⟨c, hc, heq⟩ := hincrement n hn
      have hcGlobal : c ∈ Set.Icc a (a + L) := by
        have hnTop : ((n + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
        constructor
        · exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg n)) hc.1.le
        · push_cast at hnTop
          linarith [hc.2]
      simpa only [heq] using hneg c hcGlobal
  · simpa only using hmono

/-- A fixed sign for the second derivative makes the sampled unit increments
monotone.  This is proved through the exact two-lag FTC product bounds. -/
theorem sample_increments_monotone_of_second_derivative_sign_of_pos
    (fs : ℕ → ℝ → ℝ) (a : ℝ) (L : ℕ) (ha : 0 < a)
    (hderiv : ∀ k < 2, ∀ y, 0 < y → HasDerivAt (fs k) (fs (k + 1) y) y)
    (hcont : ∀ k ≤ 2, ∀ y, 0 < y → ContinuousAt (fs k) y)
    (hsign :
      (∀ y ∈ Set.Icc a (a + L), 0 ≤ fs 2 y) ∨
      (∀ y ∈ Set.Icc a (a + L), fs 2 y ≤ 0)) :
    (∀ n, n + 1 < L →
      fs 0 (a + n + 1) - fs 0 (a + n) ≤
        fs 0 (a + n + 2) - fs 0 (a + n + 1)) ∨
    (∀ n, n + 1 < L →
      fs 0 (a + n + 2) - fs 0 (a + n + 1) ≤
        fs 0 (a + n + 1) - fs 0 (a + n)) := by
  rcases hsign with hpos | hneg
  · left
    intro n hn
    have hx : 0 < a + (n : ℝ) :=
      add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)
    have hfd := prod_mul_le_iteratedRealForwardDifferenceNat_of_pos
      fs [1, 1] (a + n) 0 hx (by simpa using hderiv) (by simpa using hcont)
      (by
        intro y hxy hyTop
        apply hpos y
        constructor
        · exact (le_add_of_nonneg_right (Nat.cast_nonneg n)).trans hxy
        · have hnTop : ((n + 2 : ℕ) : ℝ) ≤ L := by exact_mod_cast hn
          push_cast at hnTop
          norm_num at hyTop
          linarith)
    simp only [iteratedRealForwardDifferenceNat, realForwardDifferenceNat,
      List.prod_cons, List.prod_nil, Nat.cast_one, one_mul] at hfd
    have harg : a + (n : ℝ) + 1 + 1 = a + (n : ℝ) + 2 := by ring
    rw [harg] at hfd
    linarith
  · right
    intro n hn
    have hx : 0 < a + (n : ℝ) :=
      add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)
    have hfd := iteratedRealForwardDifferenceNat_le_neg_prod_mul_of_pos
      fs [1, 1] (a + n) 0 hx (by simpa using hderiv) (by simpa using hcont)
      (by
        intro y hxy hyTop
        have hy := hneg y ⟨
          (le_add_of_nonneg_right (Nat.cast_nonneg n)).trans hxy,
          by
            have hnTop : ((n + 2 : ℕ) : ℝ) ≤ L := by exact_mod_cast hn
            push_cast at hnTop
            norm_num at hyTop
            linarith⟩
        simpa using hy)
    simp only [iteratedRealForwardDifferenceNat, realForwardDifferenceNat,
      List.prod_cons, List.prod_nil, Nat.cast_one, one_mul, neg_zero] at hfd
    have harg : a + (n : ℝ) + 1 + 1 = a + (n : ℝ) + 2 := by ring
    rw [harg] at hfd
    linarith

/-- Complete smooth one-period Kusmin--Landau bridge on the positive ray.
A signed first-derivative window supplies the increment window, while a fixed
second-derivative sign supplies either monotonic direction. -/
theorem norm_phaseExponentialSum_sample_le_inv_of_deriv_window_of_second_derivative_sign_of_pos
    (fs : ℕ → ℝ → ℝ) (a : ℝ) (L : ℕ) {δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ)
    (hderiv : ∀ k < 2, ∀ y, 0 < y → HasDerivAt (fs k) (fs (k + 1) y) y)
    (hcont : ∀ k ≤ 2, ∀ y, 0 < y → ContinuousAt (fs k) y)
    (hwindow :
      (∀ y ∈ Set.Icc a (a + L), δ ≤ fs 1 y ∧ fs 1 y ≤ 1 - δ) ∨
      (∀ y ∈ Set.Icc a (a + L), δ ≤ -fs 1 y ∧ -fs 1 y ≤ 1 - δ))
    (hsecond :
      (∀ y ∈ Set.Icc a (a + L), 0 ≤ fs 2 y) ∨
      (∀ y ∈ Set.Icc a (a + L), fs 2 y ≤ 0)) :
    ‖phaseExponentialSum (fun n => fs 0 (a + n)) L‖ ≤ 1 / δ := by
  apply norm_phaseExponentialSum_sample_le_inv_of_deriv_window
    (fs 0) (fs 1) a L hδ
  · intro y hy
    exact hderiv 0 (by omega) y (ha.trans_le hy.1)
  · exact hwindow
  · have hm := sample_increments_monotone_of_second_derivative_sign_of_pos
      fs a L ha hderiv hcont hsecond
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hm

/-- Absolute first- and second-derivative windows imply the signed hypotheses
of the smooth Kusmin--Landau bridge by continuity and the intermediate value
theorem. -/
theorem norm_phaseExponentialSum_sample_le_inv_of_abs_deriv_windows_of_pos
    (fs : ℕ → ℝ → ℝ) (a : ℝ) (L : ℕ) {δ η : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hη : 0 < η)
    (hderiv : ∀ k < 2, ∀ y, 0 < y → HasDerivAt (fs k) (fs (k + 1) y) y)
    (hcont : ∀ k ≤ 2, ∀ y, 0 < y → ContinuousAt (fs k) y)
    (hfirst : ∀ y ∈ Set.Icc a (a + L),
      δ ≤ |fs 1 y| ∧ |fs 1 y| ≤ 1 - δ)
    (hsecond : ∀ y ∈ Set.Icc a (a + L), η ≤ |fs 2 y|) :
    ‖phaseExponentialSum (fun n => fs 0 (a + n)) L‖ ≤ 1 / δ := by
  have hinterval : a ≤ a + L :=
    le_add_of_nonneg_right (Nat.cast_nonneg L)
  have hcontOne : ContinuousOn (fs 1) (Set.Icc a (a + L)) := by
    intro y hy
    exact (hcont 1 (by omega) y (ha.trans_le hy.1)).continuousWithinAt
  have hcontTwo : ContinuousOn (fs 2) (Set.Icc a (a + L)) := by
    intro y hy
    exact (hcont 2 le_rfl y (ha.trans_le hy.1)).continuousWithinAt
  have hsignOne := continuousOn_sign_separated_of_abs_lower
    hinterval hδ hcontOne (fun y hy => (hfirst y hy).1)
  have hsignTwo := continuousOn_sign_separated_of_abs_lower
    hinterval hη hcontTwo hsecond
  apply norm_phaseExponentialSum_sample_le_inv_of_deriv_window_of_second_derivative_sign_of_pos
    fs a L ha hδ hderiv hcont
  · rcases hsignOne with hpos | hneg
    · left
      intro y hy
      exact ⟨hpos y hy, (le_abs_self (fs 1 y)).trans (hfirst y hy).2⟩
    · right
      intro y hy
      exact ⟨by linarith [hneg y hy], (neg_le_abs (fs 1 y)).trans (hfirst y hy).2⟩
  · rcases hsignTwo with hpos | hneg
    · left
      intro y hy
      exact hη.le.trans (hpos y hy)
    · right
      intro y hy
      exact (hneg y hy).trans (by linarith)

/-- Source-facing terminal Kusmin--Landau interface for an iterated reciprocal
phase.  Absolute windows for the first two derivatives of the terminal phase
are sufficient; smoothness, sign selection, sampling, and monotonicity are
discharged internally. -/
theorem norm_iteratedReciprocalPhaseExponentialSum_le_inv_of_terminalAbsDerivativeWindows
    (N M : ℝ) (j : ℕ) (ds : List ℕ) (a : ℝ) (L : ℕ) {δ η : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hη : 0 < η)
    (hfirst : ∀ y ∈ Set.Icc a (a + L),
      δ ≤ |iteratedRealForwardDifferenceNat
          (iteratedDeriv 1 (reciprocalPhase N M j)) ds y| ∧
        |iteratedRealForwardDifferenceNat
          (iteratedDeriv 1 (reciprocalPhase N M j)) ds y| ≤ 1 - δ)
    (hsecond : ∀ y ∈ Set.Icc a (a + L),
      η ≤ |iteratedRealForwardDifferenceNat
        (iteratedDeriv 2 (reciprocalPhase N M j)) ds y|) :
    ‖phaseExponentialSum
      (iteratedForwardPhaseDifference
        (fun n => reciprocalPhase N M j (a + n)) ds) L‖ ≤ 1 / δ := by
  rw [iteratedForwardPhaseDifference_sample]
  apply norm_phaseExponentialSum_sample_le_inv_of_abs_deriv_windows_of_pos
    (fs := fun k => iteratedRealForwardDifferenceNat
      (iteratedDeriv k (reciprocalPhase N M j)) ds) a L ha hδ hη
  · intro k hk y hy
    apply hasDerivAt_iteratedRealForwardDifferenceNat_of_pos
    · intro z hz
      exact hasDerivAt_iteratedDeriv_of_contDiffAt k
        (contDiffAt_reciprocalPhase_of_pos N M j (k + 1) hz)
    · exact hy
  · intro k hk y hy
    apply continuousAt_iteratedRealForwardDifferenceNat_of_pos
    intro z hz
    exact (ContDiffAt.iteratedDeriv_right
      (contDiffAt_reciprocalPhase_of_pos N M j k hz)
      (m := 0) (i := k) (by omega)).continuousAt
    exact hy
  · exact hfirst
  · exact hsecond

/-- The additive character of a natural multiple is the corresponding
natural power. -/
theorem standardAdditiveCharacter_nat_mul (x : ℝ) (n : ℕ) :
    standardAdditiveCharacter ((n : ℝ) * x) =
      standardAdditiveCharacter x ^ n := by
  induction n with
  | zero => simp [standardAdditiveCharacter]
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [add_mul, one_mul, standardAdditiveCharacter_add, ih, pow_succ]

/-- The geometric denominator is exactly twice the sine of the phase angle. -/
theorem norm_standardAdditiveCharacter_sub_one_eq_two_mul_abs_sin
    (alpha : ℝ) :
    ‖standardAdditiveCharacter alpha - 1‖ =
      2 * |Real.sin (Real.pi * alpha)| := by
  unfold standardAdditiveCharacter
  have harg :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (alpha : ℂ) =
        Complex.I * ((2 * Real.pi * alpha : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  congr 2
  ring_nf

/-- On the centered fundamental interval, the geometric denominator controls
four times the distance to the origin. -/
theorem four_mul_abs_le_norm_standardAdditiveCharacter_sub_one_of_abs_le_half
    {alpha : ℝ} (halpha : |alpha| ≤ 1 / 2) :
    4 * |alpha| ≤ ‖standardAdditiveCharacter alpha - 1‖ := by
  rw [norm_standardAdditiveCharacter_sub_one_eq_two_mul_abs_sin]
  have hpi : |Real.pi * alpha| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hpi
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hsin' : 2 * |alpha| ≤ |Real.sin (Real.pi * alpha)| := by
    calc
      2 * |alpha| = 2 / Real.pi * (Real.pi * |alpha|) := by
        field_simp
      _ ≤ |Real.sin (Real.pi * alpha)| := hsin
  linarith

/-- Distance from a real phase to its canonically rounded integer. -/
def nearestIntegerDistance (alpha : ℝ) : ℝ :=
  |alpha - (round alpha : ℝ)|

theorem nearestIntegerDistance_nonneg (alpha : ℝ) :
    0 ≤ nearestIntegerDistance alpha :=
  abs_nonneg _

theorem nearestIntegerDistance_le_half (alpha : ℝ) :
    nearestIntegerDistance alpha ≤ 1 / 2 := by
  exact abs_sub_round alpha

/-- Canonical rounding really minimizes the distance among all integers. -/
theorem nearestIntegerDistance_le_abs_sub_int (alpha : ℝ) (m : ℤ) :
    nearestIntegerDistance alpha ≤ |alpha - (m : ℝ)| := by
  exact round_le alpha m

/-- Integer translation replaces a phase by its centered representative
without changing the additive character. -/
theorem standardAdditiveCharacter_eq_nearestIntegerRepresentative
    (alpha : ℝ) :
    standardAdditiveCharacter alpha =
      standardAdditiveCharacter (alpha - (round alpha : ℝ)) := by
  calc
    standardAdditiveCharacter alpha =
        standardAdditiveCharacter
          ((alpha - (round alpha : ℝ)) + round alpha) := by
      congr 1
      ring
    _ = standardAdditiveCharacter (alpha - (round alpha : ℝ)) :=
      standardAdditiveCharacter_add_int _ _

/-- The geometric denominator controls the distance to the nearest integer. -/
theorem four_mul_nearestIntegerDistance_le_norm_standardAdditiveCharacter_sub_one
    (alpha : ℝ) :
    4 * nearestIntegerDistance alpha ≤
      ‖standardAdditiveCharacter alpha - 1‖ := by
  rw [standardAdditiveCharacter_eq_nearestIntegerRepresentative]
  exact four_mul_abs_le_norm_standardAdditiveCharacter_sub_one_of_abs_le_half
    (nearestIntegerDistance_le_half alpha)

/-- A phase is resonant exactly when its nearest-integer distance vanishes. -/
theorem nearestIntegerDistance_eq_zero_iff_standardAdditiveCharacter_eq_one
    (alpha : ℝ) :
    nearestIntegerDistance alpha = 0 ↔
      standardAdditiveCharacter alpha = 1 := by
  constructor
  · intro hdist
    have hsub : alpha - (round alpha : ℝ) = 0 := by
      exact abs_eq_zero.mp hdist
    have halpha : alpha = (round alpha : ℝ) := sub_eq_zero.mp hsub
    rw [halpha]
    exact standardAdditiveCharacter_int _
  · intro hchar
    have hlower :=
      four_mul_nearestIntegerDistance_le_norm_standardAdditiveCharacter_sub_one alpha
    rw [hchar, sub_self, norm_zero] at hlower
    nlinarith [nearestIntegerDistance_nonneg alpha]

theorem standardAdditiveCharacter_ne_one_of_nearestIntegerDistance_pos
    {alpha : ℝ} (halpha : 0 < nearestIntegerDistance alpha) :
    standardAdditiveCharacter alpha ≠ 1 := by
  intro h
  have hzero : ‖standardAdditiveCharacter alpha - 1‖ = 0 := by
    simp [h]
  have hlower :=
    four_mul_nearestIntegerDistance_le_norm_standardAdditiveCharacter_sub_one alpha
  rw [hzero] at hlower
  have : 0 < 4 * nearestIntegerDistance alpha :=
    mul_pos (by norm_num) halpha
  linarith

/-- Exact geometric-series expression for an affine phase. -/
theorem phaseExponentialSum_affine_eq
    (alpha beta : ℝ) (N : ℕ) :
    phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) N =
      standardAdditiveCharacter beta *
        ∑ n ∈ Finset.range N, standardAdditiveCharacter alpha ^ n := by
  unfold phaseExponentialSum phaseExponentialSequence
  calc
    ∑ n ∈ Finset.range N,
        standardAdditiveCharacter ((n : ℝ) * alpha + beta) =
      ∑ n ∈ Finset.range N,
        standardAdditiveCharacter beta *
          standardAdditiveCharacter alpha ^ n := by
        apply Finset.sum_congr rfl
        intro n _hn
        rw [standardAdditiveCharacter_add, mul_comm,
          standardAdditiveCharacter_nat_mul]
    _ = standardAdditiveCharacter beta *
        ∑ n ∈ Finset.range N, standardAdditiveCharacter alpha ^ n := by
      rw [Finset.mul_sum]

/-- Exact telescoping identity for an affine phase exponential sum. -/
theorem phaseExponentialSum_affine_mul_sub_one
    (alpha beta : ℝ) (N : ℕ) :
    phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) N *
        (standardAdditiveCharacter alpha - 1) =
      standardAdditiveCharacter beta *
        (standardAdditiveCharacter alpha ^ N - 1) := by
  rw [phaseExponentialSum_affine_eq, mul_assoc, geom_sum_mul]

/-- Denominator form of the terminal affine-phase estimate. -/
theorem norm_phaseExponentialSum_affine_mul_denominator_le_two
    (alpha beta : ℝ) (N : ℕ) :
    ‖phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) N‖ *
        ‖standardAdditiveCharacter alpha - 1‖ ≤ 2 := by
  rw [← norm_mul, phaseExponentialSum_affine_mul_sub_one, norm_mul,
    norm_standardAdditiveCharacter, one_mul]
  calc
    ‖standardAdditiveCharacter alpha ^ N - 1‖ ≤
        ‖standardAdditiveCharacter alpha ^ N‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = 2 := by norm_num

/-- Nonresonant affine phase sums are bounded by the reciprocal geometric
denominator. -/
theorem norm_phaseExponentialSum_affine_le_div
    (alpha beta : ℝ) (N : ℕ)
    (halpha : standardAdditiveCharacter alpha ≠ 1) :
    ‖phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) N‖ ≤
      2 / ‖standardAdditiveCharacter alpha - 1‖ := by
  have hden : 0 < ‖standardAdditiveCharacter alpha - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr halpha)
  rw [le_div_iff₀ hden]
  exact norm_phaseExponentialSum_affine_mul_denominator_le_two alpha beta N

/-- Combined trivial/geometric terminal estimate for a nonresonant affine
phase. -/
theorem norm_phaseExponentialSum_affine_le_min
    (alpha beta : ℝ) (N : ℕ)
    (halpha : standardAdditiveCharacter alpha ≠ 1) :
    ‖phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) N‖ ≤
      min (N : ℝ) (2 / ‖standardAdditiveCharacter alpha - 1‖) := by
  rw [le_min_iff]
  exact ⟨norm_phaseExponentialSum_le _ N,
    norm_phaseExponentialSum_affine_le_div alpha beta N halpha⟩

/-- Standard reciprocal-distance form of the nonresonant affine phase
estimate. -/
theorem norm_phaseExponentialSum_affine_le_nearestIntegerDistance
    (alpha beta : ℝ) (N : ℕ)
    (halpha : 0 < nearestIntegerDistance alpha) :
    ‖phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) N‖ ≤
      1 / (2 * nearestIntegerDistance alpha) := by
  have hchar : standardAdditiveCharacter alpha ≠ 1 :=
    standardAdditiveCharacter_ne_one_of_nearestIntegerDistance_pos halpha
  have hden : 0 < ‖standardAdditiveCharacter alpha - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hchar)
  have hfour : 0 < 4 * nearestIntegerDistance alpha :=
    mul_pos (by norm_num) halpha
  calc
    ‖phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) N‖ ≤
        2 / ‖standardAdditiveCharacter alpha - 1‖ :=
      norm_phaseExponentialSum_affine_le_div alpha beta N hchar
    _ ≤ 2 / (4 * nearestIntegerDistance alpha) := by
      rw [div_le_div_iff_of_pos_left (by norm_num) hden hfour]
      exact
        four_mul_nearestIntegerDistance_le_norm_standardAdditiveCharacter_sub_one alpha
    _ = 1 / (2 * nearestIntegerDistance alpha) := by
      field_simp
      norm_num

/-- Combined length and reciprocal-nearest-integer-distance form of the
terminal affine estimate. -/
theorem norm_phaseExponentialSum_affine_le_min_nearestIntegerDistance
    (alpha beta : ℝ) (N : ℕ)
    (halpha : 0 < nearestIntegerDistance alpha) :
    ‖phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) N‖ ≤
      min (N : ℝ) (1 / (2 * nearestIntegerDistance alpha)) := by
  rw [le_min_iff]
  exact ⟨norm_phaseExponentialSum_le _ N,
    norm_phaseExponentialSum_affine_le_nearestIntegerDistance
      alpha beta N halpha⟩

/-- Forward correlation of a phase exponential sequence is exactly the
exponential sum of the forward-difference phase. -/
theorem weylForwardCorrelation_phaseExponentialSequence
    (phase : ℕ → ℝ) (N d : ℕ) :
    weylForwardCorrelation (phaseExponentialSequence phase) N d =
      phaseExponentialSum (forwardPhaseDifference phase d) (N - d) := by
  unfold weylForwardCorrelation phaseExponentialSum
  apply Finset.sum_congr rfl
  intro n _hn
  exact standardAdditiveCharacter_mul_conj _ _

/-- Trivial support-length bound for a phase forward correlation. -/
theorem norm_weylForwardCorrelation_phaseExponentialSequence_le
    (phase : ℕ → ℝ) (N d : ℕ) :
    ‖weylForwardCorrelation (phaseExponentialSequence phase) N d‖ ≤
      (N - d : ℕ) := by
  rw [weylForwardCorrelation_phaseExponentialSequence]
  exact norm_phaseExponentialSum_le _ _

/-- Van der Corput specialized to an arbitrary real phase.  Its right side
contains exponential sums of one finite difference, so the theorem can be
applied recursively to the iterated differences above. -/
theorem norm_phaseExponentialSum_sq_mul_shift_le_differences
    (phase : ℕ → ℝ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖phaseExponentialSum phase N‖ ^ 2 ≤
      2 * ((N + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range (H + 1),
          ‖phaseExponentialSum (forwardPhaseDifference phase d) (N - d)‖ := by
  simpa only [phaseExponentialSum,
    weylForwardCorrelation_phaseExponentialSequence] using
      norm_sum_sq_mul_shift_le_forwardCorrelations
        (phaseExponentialSequence phase) N H hH

/-- Sharp-lag phase form of van der Corput, with exactly `d < H`. -/
theorem norm_phaseExponentialSum_sq_mul_shift_le_differences_sharp
    (phase : ℕ → ℝ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖phaseExponentialSum phase N‖ ^ 2 ≤
      2 * ((N + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range H,
          ‖phaseExponentialSum (forwardPhaseDifference phase d) (N - d)‖ := by
  simpa only [phaseExponentialSum,
    weylForwardCorrelation_phaseExponentialSequence] using
      norm_sum_sq_mul_shift_le_forwardCorrelations_sharp
        (phaseExponentialSequence phase) N H hH

/-- Standard diagonal/off-diagonal presentation of one Weyl step.  The
zero lag contributes exactly `N`; every remaining lag is positive. -/
theorem norm_phaseExponentialSum_sq_mul_shift_succ_le
    (phase : ℕ → ℝ) (N H : ℕ) :
    (H + 1 : ℕ) * ‖phaseExponentialSum phase N‖ ^ 2 ≤
      2 * ((N + (H + 1) : ℕ) : ℝ) *
        ((N : ℝ) +
          ∑ d ∈ Finset.range H,
            ‖phaseExponentialSum
              (forwardPhaseDifference phase (d + 1))
              (N - (d + 1))‖) := by
  have h := norm_phaseExponentialSum_sq_mul_shift_le_differences_sharp
    phase N (H + 1) (Nat.succ_pos H)
  rw [Finset.sum_range_succ'] at h
  simpa [add_comm] using h

/-- Uniform one-step Weyl rule.  A common bound `C` for all positive-lag
difference sums gives the standard diagonal term `N` plus `H*C`. -/
theorem norm_phaseExponentialSum_sq_mul_shift_succ_le_of_uniform
    (phase : ℕ → ℝ) (N H : ℕ) (C : ℝ)
    (hC : ∀ d < H,
      ‖phaseExponentialSum
        (forwardPhaseDifference phase (d + 1)) (N - (d + 1))‖ ≤ C) :
    (H + 1 : ℕ) * ‖phaseExponentialSum phase N‖ ^ 2 ≤
      2 * ((N + (H + 1) : ℕ) : ℝ) *
        ((N : ℝ) + (H : ℝ) * C) := by
  have hsum :
      ∑ d ∈ Finset.range H,
          ‖phaseExponentialSum
            (forwardPhaseDifference phase (d + 1))
            (N - (d + 1))‖ ≤
        (H : ℝ) * C := by
    calc
      ∑ d ∈ Finset.range H,
          ‖phaseExponentialSum
            (forwardPhaseDifference phase (d + 1))
            (N - (d + 1))‖ ≤
          ∑ _d ∈ Finset.range H, C := by
        apply Finset.sum_le_sum
        intro d hd
        exact hC d (Finset.mem_range.mp hd)
      _ = (H : ℝ) * C := by
        simp [nsmul_eq_mul]
  refine (norm_phaseExponentialSum_sq_mul_shift_succ_le phase N H).trans ?_
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hsum)
    (mul_nonneg (by positivity) (Nat.cast_nonneg _))

/-- The same one-step differencing inequality at any already-iterated phase.
This gives a stable recursion interface without assuming a cancellation
estimate. -/
theorem norm_iteratedPhaseExponentialSum_sq_mul_shift_le
    (phase : ℕ → ℝ) (ds : List ℕ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) *
        ‖phaseExponentialSum (iteratedForwardPhaseDifference phase ds) N‖ ^ 2 ≤
      2 * ((N + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range (H + 1),
          ‖phaseExponentialSum
            (forwardPhaseDifference
              (iteratedForwardPhaseDifference phase ds) d)
            (N - d)‖ :=
  norm_phaseExponentialSum_sq_mul_shift_le_differences _ N H hH

/-- Recursive form in which every right-hand phase is indexed by the lag
list obtained by appending the new differencing parameter. -/
theorem norm_iteratedPhaseExponentialSum_sq_mul_shift_le_append
    (phase : ℕ → ℝ) (ds : List ℕ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) *
        ‖phaseExponentialSum (iteratedForwardPhaseDifference phase ds) N‖ ^ 2 ≤
      2 * ((N + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range (H + 1),
          ‖phaseExponentialSum
            (iteratedForwardPhaseDifference phase (ds ++ [d]))
            (N - d)‖ := by
  simpa only [iteratedForwardPhaseDifference_append_singleton] using
    norm_iteratedPhaseExponentialSum_sq_mul_shift_le phase ds N H hH

/-- Sharp recursive phase-differencing form, ready for repeated application
with a growing lag list. -/
theorem norm_iteratedPhaseExponentialSum_sq_mul_shift_le_append_sharp
    (phase : ℕ → ℝ) (ds : List ℕ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) *
        ‖phaseExponentialSum (iteratedForwardPhaseDifference phase ds) N‖ ^ 2 ≤
      2 * ((N + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range H,
          ‖phaseExponentialSum
            (iteratedForwardPhaseDifference phase (ds ++ [d]))
            (N - d)‖ := by
  simpa only [iteratedForwardPhaseDifference_append_singleton] using
    norm_phaseExponentialSum_sq_mul_shift_le_differences_sharp
      (iteratedForwardPhaseDifference phase ds) N H hH

/-- Uniform recursive Weyl rule for an already-iterated phase.  The new lag
is appended to `ds`, making this theorem directly usable in an induction on
the number of differencing rounds. -/
theorem norm_iteratedPhaseExponentialSum_sq_mul_shift_succ_le_of_uniform
    (phase : ℕ → ℝ) (ds : List ℕ) (N H : ℕ) (C : ℝ)
    (hC : ∀ d < H,
      ‖phaseExponentialSum
        (iteratedForwardPhaseDifference phase (ds ++ [d + 1]))
        (N - (d + 1))‖ ≤ C) :
    (H + 1 : ℕ) *
        ‖phaseExponentialSum (iteratedForwardPhaseDifference phase ds) N‖ ^ 2 ≤
      2 * ((N + (H + 1) : ℕ) : ℝ) *
        ((N : ℝ) + (H : ℝ) * C) := by
  apply norm_phaseExponentialSum_sq_mul_shift_succ_le_of_uniform
  intro d hd
  simpa only [iteratedForwardPhaseDifference_append_singleton] using hC d hd

/-- Every lag used in a repeated Weyl step is positive and at most the
common differencing range `H`. -/
def AdmissibleWeylLags (H : ℕ) (ds : List ℕ) : Prop :=
  ∀ d ∈ ds, 0 < d ∧ d ≤ H

/-- The total displacement of an admissible lag list is at most its length
times the common Weyl range. -/
theorem sum_le_length_mul_of_admissibleWeylLags
    {H : ℕ} {ds : List ℕ} (hds : AdmissibleWeylLags H ds) :
    ds.sum ≤ ds.length * H := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hd : d ≤ H := (hds d (by simp)).2
      have htail : AdmissibleWeylLags H ds := by
        intro e he
        exact hds e (by simp [he])
      simp only [List.sum_cons, List.length_cons]
      calc
        d + ds.sum ≤ H + ds.length * H := Nat.add_le_add hd (ih htail)
        _ = (ds.length + 1) * H := by
          simp [Nat.add_mul, Nat.add_comm]

/-- Every admissible lag list has positive product, including the empty list
whose product is one. -/
theorem prod_pos_of_admissibleWeylLags
    {H : ℕ} {ds : List ℕ} (hds : AdmissibleWeylLags H ds) :
    0 < ds.prod := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hd : 0 < d := (hds d (by simp)).1
      have htail : AdmissibleWeylLags H ds := by
        intro e he
        exact hds e (by simp [he])
      simpa using Nat.mul_pos hd (ih htail)

/-- The lag product of an admissible list is at most the common Weyl range to
the number of differencing rounds. -/
theorem prod_le_pow_length_of_admissibleWeylLags
    {H : ℕ} {ds : List ℕ} (hds : AdmissibleWeylLags H ds) :
    ds.prod ≤ H ^ ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hd : d ≤ H := (hds d (by simp)).2
      have htail : AdmissibleWeylLags H ds := by
        intro e he
        exact hds e (by simp [he])
      simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul hd (ih htail)

/-- A uniform terminal estimate for every admissible `r`-fold difference and
every initial subinterval of length at most `N`.  The extra uniformity in the
length lets one iterate boundary-truncated van der Corput inequalities without
discarding their exact supports. -/
def UniformIteratedPhaseBound
    (phase : ℕ → ℝ) (r H N : ℕ) (C : ℝ) : Prop :=
  ∀ ds : List ℕ, ds.length = r → AdmissibleWeylLags H ds →
    ∀ L ≤ N,
      ‖phaseExponentialSum (iteratedForwardPhaseDifference phase ds) L‖ ≤ C

/-- Coarse one-step majorant obtained after dividing the uniform van der
Corput inequality and taking a square root. -/
def weylOneStepMajorant (N H : ℕ) (C : ℝ) : ℝ :=
  Real.sqrt
    ((2 * ((N + (H + 1) : ℕ) : ℝ) *
      ((N : ℝ) + (H : ℝ) * C)) / ((H + 1 : ℕ) : ℝ))

/-- The explicit majorant obtained by repeating the same Weyl step `r`
times. -/
def weylRecursiveMajorant (N H : ℕ) : ℕ → ℝ → ℝ
  | 0, C => C
  | r + 1, C =>
      weylOneStepMajorant N H (weylRecursiveMajorant N H r C)

theorem weylOneStepMajorant_nonneg (N H : ℕ) (C : ℝ) :
    0 ≤ weylOneStepMajorant N H C := by
  exact Real.sqrt_nonneg _

theorem weylRecursiveMajorant_nonneg
    (N H r : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ weylRecursiveMajorant N H r C := by
  induction r with
  | zero => exact hC
  | succ r _ih => exact weylOneStepMajorant_nonneg _ _ _

/-- Lag-sensitive recursive Weyl majorant.  Unlike
`weylRecursiveMajorant`, this tree retains the exact accumulated lag list and
the boundary-truncated length at every leaf. -/
def weylTreeMajorant (H : ℕ) (terminal : List ℕ → ℕ → ℝ) :
    ℕ → List ℕ → ℕ → ℝ
  | 0, ds, L => terminal ds L
  | r + 1, ds, L =>
      Real.sqrt
        ((2 * ((L + (H + 1) : ℕ) : ℝ) *
          ((L : ℝ) + ∑ d ∈ Finset.range H,
            weylTreeMajorant H terminal r (ds ++ [d + 1])
              (L - (d + 1)))) / ((H + 1 : ℕ) : ℝ))

theorem weylTreeMajorant_nonneg
    (H : ℕ) (terminal : List ℕ → ℕ → ℝ)
    (hterminal : ∀ ds L, 0 ≤ terminal ds L) (r : ℕ) (ds : List ℕ) (L : ℕ) :
    0 ≤ weylTreeMajorant H terminal r ds L := by
  cases r with
  | zero => exact hterminal ds L
  | succ r => exact Real.sqrt_nonneg _

/-- Every lag-sensitive terminal estimate propagates exactly through the
finite Weyl tree.  The theorem keeps each child `ds ++ [d+1]` and its actual
length `L-(d+1)`, so later estimates may sum the individual lag-product gain
rather than replacing all leaves by their worst case. -/
theorem norm_iteratedPhaseExponentialSum_le_weylTreeMajorant
    (phase : ℕ → ℝ) (H N : ℕ) (terminal : List ℕ → ℕ → ℝ)
    (hterminal_nonneg : ∀ ds L, 0 ≤ terminal ds L)
    (r : ℕ) (base : List ℕ) (hbase : AdmissibleWeylLags H base)
    (hterminal : ∀ ds : List ℕ, ds.length = base.length + r →
      AdmissibleWeylLags H ds → ∀ L ≤ N,
        ‖phaseExponentialSum (iteratedForwardPhaseDifference phase ds) L‖ ≤
          terminal ds L)
    (L : ℕ) (hLN : L ≤ N) :
    ‖phaseExponentialSum (iteratedForwardPhaseDifference phase base) L‖ ≤
      weylTreeMajorant H terminal r base L := by
  induction r generalizing base L with
  | zero =>
      exact hterminal base (by simp) hbase L hLN
  | succ r ih =>
      have hchild : ∀ d < H,
          ‖phaseExponentialSum
            (iteratedForwardPhaseDifference phase (base ++ [d + 1]))
            (L - (d + 1))‖ ≤
          weylTreeMajorant H terminal r (base ++ [d + 1])
            (L - (d + 1)) := by
        intro d hd
        have hbaseChild : AdmissibleWeylLags H (base ++ [d + 1]) := by
          intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hbase e he
          · omega
        apply ih (base := base ++ [d + 1]) hbaseChild
        · intro ds hlen hadmissible K hKN
          exact hterminal ds (by
            simp only [List.length_append, List.length_singleton] at hlen
            omega) hadmissible K hKN
        · omega
      have hsum :
          ∑ d ∈ Finset.range H,
              ‖phaseExponentialSum
                (iteratedForwardPhaseDifference phase (base ++ [d + 1]))
                (L - (d + 1))‖ ≤
            ∑ d ∈ Finset.range H,
              weylTreeMajorant H terminal r (base ++ [d + 1])
                (L - (d + 1)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hchild d (Finset.mem_range.mp hd)
      have hraw₀ := norm_phaseExponentialSum_sq_mul_shift_succ_le
        (iteratedForwardPhaseDifference phase base) L H
      have hraw :
          (H + 1 : ℕ) *
              ‖phaseExponentialSum
                (iteratedForwardPhaseDifference phase base) L‖ ^ 2 ≤
            2 * ((L + (H + 1) : ℕ) : ℝ) *
              ((L : ℝ) + ∑ d ∈ Finset.range H,
                ‖phaseExponentialSum
                  (iteratedForwardPhaseDifference phase (base ++ [d + 1]))
                  (L - (d + 1))‖) := by
        simpa only [iteratedForwardPhaseDifference_append_singleton] using hraw₀
      have hraw' :
          (H + 1 : ℕ) *
              ‖phaseExponentialSum
                (iteratedForwardPhaseDifference phase base) L‖ ^ 2 ≤
            2 * ((L + (H + 1) : ℕ) : ℝ) *
              ((L : ℝ) + ∑ d ∈ Finset.range H,
                weylTreeMajorant H terminal r (base ++ [d + 1])
                  (L - (d + 1))) :=
        hraw.trans (mul_le_mul_of_nonneg_left (add_le_add_right hsum _)
          (by positivity))
      have hden : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
      have hsum_nonneg : 0 ≤ ∑ d ∈ Finset.range H,
          weylTreeMajorant H terminal r (base ++ [d + 1])
            (L - (d + 1)) := by
        apply Finset.sum_nonneg
        intro d hd
        exact weylTreeMajorant_nonneg
          H terminal hterminal_nonneg r (base ++ [d + 1]) (L - (d + 1))
      have hsq :
          ‖phaseExponentialSum
              (iteratedForwardPhaseDifference phase base) L‖ ^ 2 ≤
            (2 * ((L + (H + 1) : ℕ) : ℝ) *
              ((L : ℝ) + ∑ d ∈ Finset.range H,
                weylTreeMajorant H terminal r (base ++ [d + 1])
                  (L - (d + 1)))) / ((H + 1 : ℕ) : ℝ) := by
        rw [le_div_iff₀ hden]
        simpa [mul_comm] using hraw'
      rw [weylTreeMajorant]
      have hrad : 0 ≤
          (2 * ((L + (H + 1) : ℕ) : ℝ) *
            ((L : ℝ) + ∑ d ∈ Finset.range H,
              weylTreeMajorant H terminal r (base ++ [d + 1])
                (L - (d + 1)))) / ((H + 1 : ℕ) : ℝ) := by
        positivity
      have hsqrt := Real.sq_sqrt hrad
      nlinarith [norm_nonneg
        (phaseExponentialSum (iteratedForwardPhaseDifference phase base) L),
        Real.sqrt_nonneg
          ((2 * ((L + (H + 1) : ℕ) : ℝ) *
            ((L : ℝ) + ∑ d ∈ Finset.range H,
              weylTreeMajorant H terminal r (base ++ [d + 1])
                (L - (d + 1)))) / ((H + 1 : ℕ) : ℝ))]

/-- Root form of the exact lag-sensitive finite Weyl tree. -/
theorem norm_phaseExponentialSum_le_weylTreeMajorant
    (phase : ℕ → ℝ) (r H N : ℕ) (terminal : List ℕ → ℕ → ℝ)
    (hterminal_nonneg : ∀ ds L, 0 ≤ terminal ds L)
    (hterminal : ∀ ds : List ℕ, ds.length = r →
      AdmissibleWeylLags H ds → ∀ L ≤ N,
        ‖phaseExponentialSum (iteratedForwardPhaseDifference phase ds) L‖ ≤
          terminal ds L) :
    ‖phaseExponentialSum phase N‖ ≤
      weylTreeMajorant H terminal r [] N := by
  simpa using norm_iteratedPhaseExponentialSum_le_weylTreeMajorant
    phase H N terminal hterminal_nonneg r [] (by simp [AdmissibleWeylLags])
      (by simpa using hterminal) N le_rfl

/-- One backward step for uniform iterated-difference bounds.  A bound at
depth `r+1` yields the explicit square-root majorant at depth `r`. -/
theorem uniformIteratedPhaseBound_oneStep
    (phase : ℕ → ℝ) (r H N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : UniformIteratedPhaseBound phase (r + 1) H N C) :
    UniformIteratedPhaseBound phase r H N
      (weylOneStepMajorant N H C) := by
  intro ds hlen hadmissible L hLN
  have hdiff : ∀ d < H,
      ‖phaseExponentialSum
        (iteratedForwardPhaseDifference phase (ds ++ [d + 1]))
        (L - (d + 1))‖ ≤ C := by
    intro d hd
    apply hbound (ds ++ [d + 1])
    · simp [hlen]
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hadmissible e he
      · omega
    · omega
  have hsq :=
    norm_iteratedPhaseExponentialSum_sq_mul_shift_succ_le_of_uniform
      phase ds L H C hdiff
  have hright :
      2 * ((L + (H + 1) : ℕ) : ℝ) *
          ((L : ℝ) + (H : ℝ) * C) ≤
        2 * ((N + (H + 1) : ℕ) : ℝ) *
          ((N : ℝ) + (H : ℝ) * C) := by
    gcongr
  have hsq' :
      ((H + 1 : ℕ) : ℝ) *
          ‖phaseExponentialSum
            (iteratedForwardPhaseDifference phase ds) L‖ ^ 2 ≤
        2 * ((N + (H + 1) : ℕ) : ℝ) *
          ((N : ℝ) + (H : ℝ) * C) := hsq.trans hright
  have hden : 0 < ((H + 1 : ℕ) : ℝ) := by positivity
  have hnum :
      0 ≤ 2 * ((N + (H + 1) : ℕ) : ℝ) *
        ((N : ℝ) + (H : ℝ) * C) := by positivity
  have hsquare :
      ‖phaseExponentialSum
          (iteratedForwardPhaseDifference phase ds) L‖ ^ 2 ≤
        (2 * ((N + (H + 1) : ℕ) : ℝ) *
          ((N : ℝ) + (H : ℝ) * C)) / ((H + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hden]
    simpa [mul_comm] using hsq'
  rw [weylOneStepMajorant]
  have hsqrt := Real.sq_sqrt (div_nonneg hnum hden.le)
  nlinarith [norm_nonneg
    (phaseExponentialSum (iteratedForwardPhaseDifference phase ds) L),
    Real.sqrt_nonneg
      ((2 * ((N + (H + 1) : ℕ) : ℝ) *
        ((N : ℝ) + (H : ℝ) * C)) / ((H + 1 : ℕ) : ℝ))]

/-- Iterate the backward Weyl step any finite number of times. -/
theorem uniformIteratedPhaseBound_of_deeper
    (phase : ℕ → ℝ) (r s H N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : UniformIteratedPhaseBound phase (r + s) H N C) :
    UniformIteratedPhaseBound phase r H N
      (weylRecursiveMajorant N H s C) := by
  induction s generalizing r C with
  | zero => simpa using hbound
  | succ s ih =>
      have hdeep : UniformIteratedPhaseBound phase (r + 1 + s) H N C := by
        convert hbound using 1
        omega
      have hmid := ih (r := r + 1) hC hdeep
      exact uniformIteratedPhaseBound_oneStep phase r H N
        (weylRecursiveMajorant_nonneg N H s hC) hmid

/-- Root bound after `r` Weyl rounds.  Thus an explicit uniform terminal
bound for all admissible `r`-fold differences immediately controls the
original exponential sum by `weylRecursiveMajorant`. -/
theorem norm_phaseExponentialSum_le_weylRecursiveMajorant
    (phase : ℕ → ℝ) (r H N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : UniformIteratedPhaseBound phase r H N C) :
    ‖phaseExponentialSum phase N‖ ≤
      weylRecursiveMajorant N H r C := by
  have hroot := uniformIteratedPhaseBound_of_deeper
    phase 0 r H N hC (by simpa using hbound)
  unfold UniformIteratedPhaseBound at hroot
  simpa using hroot [] rfl (by
    intro d hd
    simp at hd) N le_rfl

/-- Build a uniform terminal bound when every admissible `r`-fold difference
is affine and all of its slopes stay at least `delta` away from the integers.
This connects the repeated Weyl recursion to the geometric-sum endpoint. -/
theorem uniformIteratedPhaseBound_of_affine
    (phase : ℕ → ℝ) (r H N : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (haffine : ∀ ds : List ℕ, ds.length = r → AdmissibleWeylLags H ds →
      ∃ alpha beta : ℝ,
        (iteratedForwardPhaseDifference phase ds =
            fun n : ℕ => (n : ℝ) * alpha + beta) ∧
          delta ≤ nearestIntegerDistance alpha) :
    UniformIteratedPhaseBound phase r H N (1 / (2 * delta)) := by
  intro ds hlen hadmissible L _hLN
  obtain ⟨alpha, beta, hphase, hslope⟩ := haffine ds hlen hadmissible
  rw [hphase]
  have hslope_pos : 0 < nearestIntegerDistance alpha :=
    hdelta.trans_le hslope
  calc
    ‖phaseExponentialSum (fun n => (n : ℝ) * alpha + beta) L‖ ≤
        1 / (2 * nearestIntegerDistance alpha) :=
      norm_phaseExponentialSum_affine_le_nearestIntegerDistance
        alpha beta L hslope_pos
    _ ≤ 1 / (2 * delta) := by
      rw [div_le_div_iff_of_pos_left one_pos
        (mul_pos (by norm_num) hslope_pos)
        (mul_pos (by norm_num) hdelta)]
      nlinarith

/-- Repeated Weyl bound closed by the affine terminal estimate. -/
theorem norm_phaseExponentialSum_le_weylRecursiveMajorant_of_affine
    (phase : ℕ → ℝ) (r H N : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (haffine : ∀ ds : List ℕ, ds.length = r → AdmissibleWeylLags H ds →
      ∃ alpha beta : ℝ,
        (iteratedForwardPhaseDifference phase ds =
            fun n : ℕ => (n : ℝ) * alpha + beta) ∧
          delta ≤ nearestIntegerDistance alpha) :
    ‖phaseExponentialSum phase N‖ ≤
      weylRecursiveMajorant N H r (1 / (2 * delta)) := by
  apply norm_phaseExponentialSum_le_weylRecursiveMajorant
  · positivity
  · exact uniformIteratedPhaseBound_of_affine
      phase r H N hdelta haffine

/-- Translation of the source's half-open reciprocal-phase sum to the
initial-interval form consumed by finite differencing. -/
theorem reciprocalPhaseSum_eq_phaseExponentialSum_translate
    (N M : ℝ) (j a b : ℕ) :
    reciprocalPhaseSum N M j a b =
      phaseExponentialSum
        (fun n => reciprocalPhase N M j (a + n)) (b - a) := by
  unfold reciprocalPhaseSum phaseExponentialSum phaseExponentialSequence
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.cast_add]

/-- Source-facing repeated-Weyl interface.  Any uniform estimate for all
admissible `r`-fold differences of the translated reciprocal phase propagates
to the original half-open reciprocal-phase sum. -/
theorem norm_reciprocalPhaseSum_le_weylRecursiveMajorant
    (N M : ℝ) (j a b r H : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : UniformIteratedPhaseBound
      (fun n => reciprocalPhase N M j (a + n)) r H (b - a) C) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylRecursiveMajorant (b - a) H r C := by
  rw [reciprocalPhaseSum_eq_phaseExponentialSum_translate]
  exact norm_phaseExponentialSum_le_weylRecursiveMajorant _ r H (b - a) hC hbound

/-- The exact four-round interface used by the source's `k=5` Weyl branch.
Only the uniform terminal estimate for the fourth differences remains on the
hypothesis side. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylMajorant
    (N M : ℝ) (j a b H : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : UniformIteratedPhaseBound
      (fun n => reciprocalPhase N M j (a + n)) 4 H (b - a) C) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylRecursiveMajorant (b - a) H 4 C :=
  norm_reciprocalPhaseSum_le_weylRecursiveMajorant
    N M j a b 4 H hC hbound

/-- Every iterated discrete difference of the translated reciprocal phase
is the sampled iterated real difference of the smooth source phase. -/
theorem iteratedForwardPhaseDifference_reciprocalPhase_translate
    (N M : ℝ) (j a : ℕ) (ds : List ℕ) :
    iteratedForwardPhaseDifference
        (fun n => reciprocalPhase N M j (a + n)) ds =
      fun n : ℕ => iteratedRealForwardDifferenceNat
        (reciprocalPhase N M j) ds (a + n) := by
  simpa only [Nat.cast_add] using
    iteratedForwardPhaseDifference_sample
      (reciprocalPhase N M j) (a : ℝ) ds

/-- The derivative of an iterated real difference of the reciprocal phase is
the corresponding iterated difference of its derivative on the positive
ray. -/
theorem hasDerivAt_iteratedRealForwardDifferenceNat_reciprocalPhase
    (N M : ℝ) (j : ℕ) (ds : List ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds)
      (iteratedRealForwardDifferenceNat
        (deriv (reciprocalPhase N M j)) ds x) x := by
  refine hasDerivAt_iteratedRealForwardDifferenceNat_of_pos ?_ ds hx
  intro y hy
  exact (differentiableAt_reciprocalPhase_of_pos N M j hy).hasDerivAt

/-- The derivative of an iterated reciprocal-phase difference is controlled
by the next derivative of the original phase.  The source scale is frozen at
any positive lower endpoint `X`, making this form uniform as `x` varies to its
right. -/
theorem abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase_le_product_scale_of_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) (ds : List ℕ) {X x : ℝ}
    (hX : 0 < X) (hXx : X ≤ x) :
    |deriv (iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds) x| ≤
      (ds.prod : ℝ) *
        (((ds.length + 1).factorial : ℝ) *
            (((((ds.length + 1) + j) ^ (ds.length + 1) : ℕ) : ℝ) *
              reciprocalPhaseScale N M j X) /
          X ^ (ds.length + 1)) := by
  have hx : 0 < x := hX.trans_le hXx
  rw [(hasDerivAt_iteratedRealForwardDifferenceNat_reciprocalPhase
    N M j ds hx).deriv]
  rw [← iteratedDeriv_one]
  apply abs_iteratedRealForwardDifferenceNat_le_prod_of_pos
      (fs := fun k => iteratedDeriv (k + 1) (reciprocalPhase N M j))
  · exact hx
  · intro k hk y hy
    exact hasDerivAt_iteratedDeriv_of_contDiffAt (k + 1)
      (contDiffAt_reciprocalPhase_of_pos N M j (k + 2) hy)
  · intro k hk y hy
    exact (ContDiffAt.iteratedDeriv_right
      (contDiffAt_reciprocalPhase_of_pos N M j (k + 1) hy)
      (m := 0) (i := k + 1) (by omega)).continuousAt
  · intro y hxy hyTop
    simpa [Nat.add_comm] using
      (abs_iteratedDeriv_reciprocalPhase_le_scale_div_pow
        N M (r := ds.length + 1) hj hX (hXx.trans hxy))

/-- An absolute lower bound for the next reciprocal-phase derivative has one
fixed sign on the exact evaluation interval and therefore controls the
derivative of the iterated difference with the exact lag product. -/
theorem prod_mul_le_abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase_of_abs_lower
    (N M : ℝ) (j : ℕ) (ds : List ℕ) (x c : ℝ) (hx : 0 < x) (hc : 0 < c)
    (hlower : ∀ y ∈ Set.Icc x (x + ds.sum),
      c ≤ |iteratedDeriv (ds.length + 1) (reciprocalPhase N M j) y|) :
    (ds.prod : ℝ) * c ≤
      |deriv (iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds) x| := by
  rw [(hasDerivAt_iteratedRealForwardDifferenceNat_reciprocalPhase
    N M j ds hx).deriv]
  rw [← iteratedDeriv_one]
  have hinterval : x ≤ x + ds.sum :=
    le_add_of_nonneg_right (Nat.cast_nonneg ds.sum)
  have hcont : ContinuousOn
      (iteratedDeriv (ds.length + 1) (reciprocalPhase N M j))
      (Set.Icc x (x + ds.sum)) := by
    intro y hy
    have hypos : 0 < y := hx.trans_le hy.1
    exact (ContDiffAt.iteratedDeriv_right
      (contDiffAt_reciprocalPhase_of_pos N M j (ds.length + 1) hypos)
      (m := 0) (i := ds.length + 1) (by omega)).continuousAt.continuousWithinAt
  have hsep := continuousOn_sign_separated_of_abs_lower
    hinterval hc hcont hlower
  apply prod_mul_le_abs_iteratedRealForwardDifferenceNat_of_pos_separated
      (fs := fun k => iteratedDeriv (k + 1) (reciprocalPhase N M j))
  · exact hx
  · intro k hk y hy
    exact hasDerivAt_iteratedDeriv_of_contDiffAt (k + 1)
      (contDiffAt_reciprocalPhase_of_pos N M j (k + 2) hy)
  · intro k hk y hy
    exact (ContDiffAt.iteratedDeriv_right
      (contDiffAt_reciprocalPhase_of_pos N M j (k + 1) hy)
      (m := 0) (i := k + 1) (by omega)).continuousAt
  · simpa [Nat.add_comm] using hsep

/-- A normalized lower bound for the next reciprocal derivative gives the
matching lower bound for the derivative of an iterated finite difference. -/
theorem prod_mul_normalizedLower_div_pow_le_abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase
    (N M : ℝ) (j : ℕ) (ds : List ℕ) (x L : ℝ) (hx : 0 < x) (hL : 0 < L)
    (hlower : ∀ y ∈ Set.Icc x (x + ds.sum),
      L ≤ y ^ (ds.length + 1) / ((ds.length + 1).factorial : ℝ) *
        |iteratedDeriv (ds.length + 1) (reciprocalPhase N M j) y|) :
    (ds.prod : ℝ) *
        (((ds.length + 1).factorial : ℝ) * L /
          (x + ds.sum) ^ (ds.length + 1)) ≤
      |deriv (iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds) x| := by
  have htop : 0 < x + (ds.sum : ℝ) := by positivity
  have hfac : (0 : ℝ) < (ds.length + 1).factorial := by positivity
  have hc : 0 < ((ds.length + 1).factorial : ℝ) * L /
      (x + ds.sum) ^ (ds.length + 1) := by positivity
  apply prod_mul_le_abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase_of_abs_lower
    N M j ds x _ hx hc
  intro y hy
  have hypos : 0 < y := hx.trans_le hy.1
  have hypow : 0 < y ^ (ds.length + 1) := pow_pos hypos _
  have htopPow : 0 < (x + ds.sum) ^ (ds.length + 1) := pow_pos htop _
  have hpow : y ^ (ds.length + 1) ≤
      (x + ds.sum) ^ (ds.length + 1) :=
    pow_le_pow_left₀ hypos.le hy.2 _
  have hnorm := hlower y hy
  rw [div_mul_eq_mul_div] at hnorm
  have hmul : L * ((ds.length + 1).factorial : ℝ) ≤
      y ^ (ds.length + 1) *
        |iteratedDeriv (ds.length + 1) (reciprocalPhase N M j) y| :=
    (le_div_iff₀ hfac).mp hnorm
  rw [div_le_iff₀ htopPow]
  calc
    ((ds.length + 1).factorial : ℝ) * L ≤
        y ^ (ds.length + 1) *
          |iteratedDeriv (ds.length + 1) (reciprocalPhase N M j) y| := by
      simpa [mul_comm] using hmul
    _ ≤ (x + ds.sum) ^ (ds.length + 1) *
          |iteratedDeriv (ds.length + 1) (reciprocalPhase N M j) y| := by
      exact mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    _ = |iteratedDeriv (ds.length + 1) (reciprocalPhase N M j) y| *
          (x + ds.sum) ^ (ds.length + 1) := by ring

/-- The regular-set normalized derivative lower bound, propagated to the
derivative of the terminal iterated phase. -/
theorem prod_mul_regularScale_div_pow_le_abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (ds : List ℕ)
    {X Y q x : ℝ} (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hxIcc : x ∈ Set.Icc X Y) (hevalY : x + ds.sum ≤ Y)
    (hevalTop : x + ds.sum ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc x (x + ds.sum),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : ds.length + 1 ∈ orders) :
    (ds.prod : ℝ) *
        (((ds.length + 1).factorial : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
          (x + ds.sum) ^ (ds.length + 1)) ≤
      |deriv (iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds) x| := by
  apply prod_mul_normalizedLower_div_pow_le_abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase
  · exact hX.trans_le hxIcc.1
  · positivity
  · intro y hy
    exact normalized_abs_iteratedDeriv_reciprocalPhase_ge_scale_mul_div_ten_of_regular
      N M orders hX hq hqOne hj
      ⟨hxIcc.1.trans hy.1, hy.2.trans hevalY⟩
      (hy.2.trans hevalTop) (hregular y hy) hr

/-- Uniformized lower endpoint for the terminal derivative window: replacing
the exact top `x + sum(lags)` by `2X` produces a bound independent of `x`. -/
theorem prod_mul_regularScale_div_two_pow_le_abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (ds : List ℕ)
    {X Y q x : ℝ} (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hxIcc : x ∈ Set.Icc X Y) (hevalY : x + ds.sum ≤ Y)
    (hevalTop : x + ds.sum ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc x (x + ds.sum),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : ds.length + 1 ∈ orders) :
    (ds.prod : ℝ) *
        (((ds.length + 1).factorial : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
          (2 * X) ^ (ds.length + 1)) ≤
      |deriv (iteratedRealForwardDifferenceNat (reciprocalPhase N M j) ds) x| := by
  have hraw :=
    prod_mul_regularScale_div_pow_le_abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase
      N M orders ds hX hF hq hqOne hj hxIcc hevalY hevalTop hregular hr
  have hx : 0 < x := hX.trans_le hxIcc.1
  have hxtop : 0 < x + (ds.sum : ℝ) :=
    add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg _)
  have hpow : (x + ds.sum) ^ (ds.length + 1) ≤
      (2 * X) ^ (ds.length + 1) :=
    pow_le_pow_left₀ hxtop.le hevalTop _
  have hnum : 0 ≤ ((ds.length + 1).factorial : ℝ) *
      (reciprocalPhaseScale N M j X * q / 10) := by positivity
  have hfrac :
      ((ds.length + 1).factorial : ℝ) *
          (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (ds.length + 1) ≤
        ((ds.length + 1).factorial : ℝ) *
          (reciprocalPhaseScale N M j X * q / 10) /
            (x + ds.sum) ^ (ds.length + 1) := by
    exact div_le_div_of_nonneg_left hnum (pow_pos hxtop _) hpow
  exact (mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg ds.prod)).trans hraw

/-- Complete uniform two-sided first-derivative window for a terminal
iterated reciprocal phase on a critical-regular evaluation interval.  For
four Weyl lags this consumes the fifth original derivative. -/
theorem reciprocalPhase_terminalDifference_derivative_bounds_on_regular
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (ds : List ℕ)
    {X Y q x : ℝ} (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hxIcc : x ∈ Set.Icc X Y) (hevalY : x + ds.sum ≤ Y)
    (hevalTop : x + ds.sum ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc x (x + ds.sum),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : ds.length + 1 ∈ orders) :
    (ds.prod : ℝ) *
          (((ds.length + 1).factorial : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (ds.length + 1)) ≤
        |deriv (iteratedRealForwardDifferenceNat
          (reciprocalPhase N M j) ds) x| ∧
      |deriv (iteratedRealForwardDifferenceNat
          (reciprocalPhase N M j) ds) x| ≤
        (ds.prod : ℝ) *
          (((ds.length + 1).factorial : ℝ) *
              (((((ds.length + 1) + j) ^ (ds.length + 1) : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) /
            X ^ (ds.length + 1)) := by
  exact ⟨
    prod_mul_regularScale_div_two_pow_le_abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase
      N M orders ds hX hF hq hqOne hj hxIcc hevalY hevalTop hregular hr,
    abs_deriv_iteratedRealForwardDifferenceNat_reciprocalPhase_le_product_scale_of_le
      N M hj ds hX hxIcc.1⟩

/-- Absolute derivative separation for any shifted derivative order propagates
through an arbitrary lag list with the exact lag product. -/
theorem prod_mul_le_abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase_of_abs_lower
    (N M : ℝ) (j r : ℕ) (ds : List ℕ) (x c : ℝ) (hx : 0 < x) (hc : 0 < c)
    (hlower : ∀ y ∈ Set.Icc x (x + ds.sum),
      c ≤ |iteratedDeriv (r + ds.length) (reciprocalPhase N M j) y|) :
    (ds.prod : ℝ) * c ≤
      |iteratedRealForwardDifferenceNat
        (iteratedDeriv r (reciprocalPhase N M j)) ds x| := by
  have hinterval : x ≤ x + ds.sum :=
    le_add_of_nonneg_right (Nat.cast_nonneg ds.sum)
  have hcontTop : ContinuousOn
      (iteratedDeriv (r + ds.length) (reciprocalPhase N M j))
      (Set.Icc x (x + ds.sum)) := by
    intro y hy
    have hypos : 0 < y := hx.trans_le hy.1
    exact (ContDiffAt.iteratedDeriv_right
      (contDiffAt_reciprocalPhase_of_pos N M j (r + ds.length) hypos)
      (m := 0) (i := r + ds.length) (by omega)).continuousAt.continuousWithinAt
  have hsep := continuousOn_sign_separated_of_abs_lower
    hinterval hc hcontTop hlower
  apply prod_mul_le_abs_iteratedRealForwardDifferenceNat_of_pos_separated
      (fs := fun k => iteratedDeriv (r + k) (reciprocalPhase N M j))
  · exact hx
  · intro k hk y hy
    exact hasDerivAt_iteratedDeriv_of_contDiffAt (r + k)
      (contDiffAt_reciprocalPhase_of_pos N M j (r + k + 1) hy)
  · intro k hk y hy
    exact (ContDiffAt.iteratedDeriv_right
      (contDiffAt_reciprocalPhase_of_pos N M j (r + k) hy)
      (m := 0) (i := r + k) (by omega)).continuousAt
  · rcases hsep with hpos | hneg
    · left
      intro y hxy hyTop
      exact hpos y ⟨hxy, hyTop⟩
    · right
      intro y hxy hyTop
      exact hneg y ⟨hxy, hyTop⟩

/-- A normalized lower bound at order `r + length(lags)` controls the
`r`-th derivative of the terminal iterated phase. -/
theorem prod_mul_normalizedLower_div_pow_le_abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase
    (N M : ℝ) (j r : ℕ) (ds : List ℕ) (x L : ℝ) (hx : 0 < x) (hL : 0 < L)
    (hlower : ∀ y ∈ Set.Icc x (x + ds.sum),
      L ≤ y ^ (r + ds.length) / ((r + ds.length).factorial : ℝ) *
        |iteratedDeriv (r + ds.length) (reciprocalPhase N M j) y|) :
    (ds.prod : ℝ) *
        (((r + ds.length).factorial : ℝ) * L /
          (x + ds.sum) ^ (r + ds.length)) ≤
      |iteratedRealForwardDifferenceNat
        (iteratedDeriv r (reciprocalPhase N M j)) ds x| := by
  have htop : 0 < x + (ds.sum : ℝ) := by positivity
  have hfac : (0 : ℝ) < (r + ds.length).factorial := by positivity
  have hc : 0 < ((r + ds.length).factorial : ℝ) * L /
      (x + ds.sum) ^ (r + ds.length) := by positivity
  apply prod_mul_le_abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase_of_abs_lower
    N M j r ds x _ hx hc
  intro y hy
  have hypos : 0 < y := hx.trans_le hy.1
  have htopPow : 0 < (x + ds.sum) ^ (r + ds.length) := pow_pos htop _
  have hpow : y ^ (r + ds.length) ≤
      (x + ds.sum) ^ (r + ds.length) :=
    pow_le_pow_left₀ hypos.le hy.2 _
  have hnorm := hlower y hy
  rw [div_mul_eq_mul_div] at hnorm
  have hmul : L * ((r + ds.length).factorial : ℝ) ≤
      y ^ (r + ds.length) *
        |iteratedDeriv (r + ds.length) (reciprocalPhase N M j) y| :=
    (le_div_iff₀ hfac).mp hnorm
  rw [div_le_iff₀ htopPow]
  calc
    ((r + ds.length).factorial : ℝ) * L ≤
        y ^ (r + ds.length) *
          |iteratedDeriv (r + ds.length) (reciprocalPhase N M j) y| := by
      simpa [mul_comm] using hmul
    _ ≤ (x + ds.sum) ^ (r + ds.length) *
          |iteratedDeriv (r + ds.length) (reciprocalPhase N M j) y| := by
      exact mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    _ = |iteratedDeriv (r + ds.length) (reciprocalPhase N M j) y| *
          (x + ds.sum) ^ (r + ds.length) := by ring

/-- Uniform critical-regular lower bound for any derivative order of the
terminal iterated reciprocal phase. -/
theorem prod_mul_regularScale_div_two_pow_le_abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (r : ℕ) (ds : List ℕ)
    {X Y q x : ℝ} (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hxIcc : x ∈ Set.Icc X Y) (hevalY : x + ds.sum ≤ Y)
    (hevalTop : x + ds.sum ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc x (x + ds.sum),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hr : r + ds.length ∈ orders) :
    (ds.prod : ℝ) *
        (((r + ds.length).factorial : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
          (2 * X) ^ (r + ds.length)) ≤
      |iteratedRealForwardDifferenceNat
        (iteratedDeriv r (reciprocalPhase N M j)) ds x| := by
  have hraw :=
    prod_mul_normalizedLower_div_pow_le_abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase
      N M j r ds x (reciprocalPhaseScale N M j X * q / 10)
      (hX.trans_le hxIcc.1) (by positivity)
      (by
        intro y hy
        exact normalized_abs_iteratedDeriv_reciprocalPhase_ge_scale_mul_div_ten_of_regular
          N M orders hX hq hqOne hj
          ⟨hxIcc.1.trans hy.1, hy.2.trans hevalY⟩
          (hy.2.trans hevalTop) (hregular y hy) hr)
  have hx : 0 < x := hX.trans_le hxIcc.1
  have hxtop : 0 < x + (ds.sum : ℝ) :=
    add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg _)
  have hpow : (x + ds.sum) ^ (r + ds.length) ≤
      (2 * X) ^ (r + ds.length) :=
    pow_le_pow_left₀ hxtop.le hevalTop _
  have hnum : 0 ≤ ((r + ds.length).factorial : ℝ) *
      (reciprocalPhaseScale N M j X * q / 10) := by positivity
  have hfrac :
      ((r + ds.length).factorial : ℝ) *
          (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (r + ds.length) ≤
        ((r + ds.length).factorial : ℝ) *
          (reciprocalPhaseScale N M j X * q / 10) /
            (x + ds.sum) ^ (r + ds.length) := by
    exact div_le_div_of_nonneg_left hnum (pow_pos hxtop _) hpow
  exact (mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg ds.prod)).trans hraw

/-- Uniform raw upper bound for any derivative order of the terminal iterated
reciprocal phase. -/
theorem abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase_le_product_scale_of_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) (r : ℕ) (ds : List ℕ) {X x : ℝ}
    (hX : 0 < X) (hXx : X ≤ x) :
    |iteratedRealForwardDifferenceNat
        (iteratedDeriv r (reciprocalPhase N M j)) ds x| ≤
      (ds.prod : ℝ) *
        (((r + ds.length).factorial : ℝ) *
            (((((r + ds.length) + j) ^ (r + ds.length) : ℕ) : ℝ) *
              reciprocalPhaseScale N M j X) /
          X ^ (r + ds.length)) := by
  have hx : 0 < x := hX.trans_le hXx
  apply abs_iteratedRealForwardDifferenceNat_le_prod_of_pos
      (fs := fun k => iteratedDeriv (r + k) (reciprocalPhase N M j))
  · exact hx
  · intro k hk y hy
    exact hasDerivAt_iteratedDeriv_of_contDiffAt (r + k)
      (contDiffAt_reciprocalPhase_of_pos N M j (r + k + 1) hy)
  · intro k hk y hy
    exact (ContDiffAt.iteratedDeriv_right
      (contDiffAt_reciprocalPhase_of_pos N M j (r + k) hy)
      (m := 0) (i := r + k) (by omega)).continuousAt
  · intro y hxy hyTop
    exact abs_iteratedDeriv_reciprocalPhase_le_scale_div_pow
      N M (r := r + ds.length) hj hX (hXx.trans hxy)

/-- Complete critical-regular terminal Kusmin--Landau estimate for an iterated
reciprocal phase.  The lower scale comes from derivative orders one and two
of the terminal phase; the sole size condition keeps the first derivative
inside one turn, away from both endpoints. -/
theorem norm_iteratedReciprocalPhaseExponentialSum_le_inv_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (ds : List ℕ)
    {X Y q a : ℝ} (L : ℕ)
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hprod : 0 < ds.prod) (haIcc : a ∈ Set.Icc X Y)
    (hevalY : a + L + ds.sum ≤ Y) (hevalTop : a + L + ds.sum ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc a (a + L + ds.sum),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrOne : 1 + ds.length ∈ orders) (hrTwo : 2 + ds.length ∈ orders)
    (hupperSmall :
      (ds.prod : ℝ) *
          (((1 + ds.length).factorial : ℝ) *
              (((((1 + ds.length) + j) ^ (1 + ds.length) : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) /
            X ^ (1 + ds.length)) ≤
        1 - (ds.prod : ℝ) *
          (((1 + ds.length).factorial : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (1 + ds.length))) :
    ‖phaseExponentialSum
      (iteratedForwardPhaseDifference
        (fun n => reciprocalPhase N M j (a + n)) ds) L‖ ≤
      1 / ((ds.prod : ℝ) *
        (((1 + ds.length).factorial : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
          (2 * X) ^ (1 + ds.length))) := by
  let δ : ℝ := (ds.prod : ℝ) *
    (((1 + ds.length).factorial : ℝ) *
        (reciprocalPhaseScale N M j X * q / 10) /
      (2 * X) ^ (1 + ds.length))
  let η : ℝ := (ds.prod : ℝ) *
    (((2 + ds.length).factorial : ℝ) *
        (reciprocalPhaseScale N M j X * q / 10) /
      (2 * X) ^ (2 + ds.length))
  have hprodR : (0 : ℝ) < ds.prod := by exact_mod_cast hprod
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have ha : 0 < a := hX.trans_le haIcc.1
  have hsumR : (0 : ℝ) ≤ ds.sum := Nat.cast_nonneg _
  change _ ≤ 1 / δ
  apply norm_iteratedReciprocalPhaseExponentialSum_le_inv_of_terminalAbsDerivativeWindows
    N M j ds a L ha hδ hη
  · intro y hy
    have hyIcc : y ∈ Set.Icc X Y := by
      constructor
      · exact haIcc.1.trans hy.1
      · linarith [hy.2, hevalY, hsumR]
    have hyEvalY : y + ds.sum ≤ Y := by linarith [hy.2, hevalY]
    have hyEvalTop : y + ds.sum ≤ 2 * X := by linarith [hy.2, hevalTop]
    have hyRegular : ∀ z ∈ Set.Icc y (y + ds.sum),
        z ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q := by
      intro z hz
      apply hregular z
      constructor
      · exact hy.1.trans hz.1
      · linarith [hz.2, hy.2]
    constructor
    · change δ ≤ _
      exact prod_mul_regularScale_div_two_pow_le_abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase
        N M orders 1 ds hX hF hq hqOne hj hyIcc hyEvalY hyEvalTop hyRegular hrOne
    · calc
        |iteratedRealForwardDifferenceNat
            (iteratedDeriv 1 (reciprocalPhase N M j)) ds y| ≤
            (ds.prod : ℝ) *
              (((1 + ds.length).factorial : ℝ) *
                  (((((1 + ds.length) + j) ^ (1 + ds.length) : ℕ) : ℝ) *
                    reciprocalPhaseScale N M j X) /
                X ^ (1 + ds.length)) :=
          abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase_le_product_scale_of_le
            N M hj 1 ds hX hyIcc.1
        _ ≤ 1 - δ := by simpa only [δ] using hupperSmall
  · intro y hy
    have hyIcc : y ∈ Set.Icc X Y := by
      constructor
      · exact haIcc.1.trans hy.1
      · linarith [hy.2, hevalY, hsumR]
    have hyEvalY : y + ds.sum ≤ Y := by linarith [hy.2, hevalY]
    have hyEvalTop : y + ds.sum ≤ 2 * X := by linarith [hy.2, hevalTop]
    have hyRegular : ∀ z ∈ Set.Icc y (y + ds.sum),
        z ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q := by
      intro z hz
      apply hregular z
      constructor
      · exact hy.1.trans hz.1
      · linarith [hz.2, hy.2]
    change η ≤ _
    exact prod_mul_regularScale_div_two_pow_le_abs_iteratedRealForwardDifferenceNat_iteratedDeriv_reciprocalPhase
      N M orders 2 ds hX hF hq hqOne hj hyIcc hyEvalY hyEvalTop hyRegular hrTwo

/-- Uniform critical-regular terminal bound for every admissible `r`-lag list
and every truncated initial length.  The maximum total displacement is `r*H`,
while the maximum lag product is `H^r`; the latter single worst-case condition
simultaneously keeps every terminal first derivative inside one additive turn.
The conclusion removes the individual lag product from the denominator using
its automatic lower bound by one. -/
theorem uniformIteratedPhaseBound_reciprocalPhase_of_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (r a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (r * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrOne : 1 + r ∈ orders) (hrTwo : 2 + r ∈ orders)
    (hupperSmall :
      ((H ^ r : ℕ) : ℝ) *
          (((1 + r).factorial : ℝ) *
              (((((1 + r) + j) ^ (1 + r) : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) /
            X ^ (1 + r)) ≤
        1 - ((H ^ r : ℕ) : ℝ) *
          (((1 + r).factorial : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (1 + r))) :
    UniformIteratedPhaseBound
      (fun n => reciprocalPhase N M j (a + n)) r H (b - a)
      (1 / (((1 + r).factorial : ℝ) *
        (reciprocalPhaseScale N M j X * q / 10) /
          (2 * X) ^ (1 + r))) := by
  intro ds hlen hadmissible L hLN
  have hprodPos : 0 < ds.prod :=
    prod_pos_of_admissibleWeylLags hadmissible
  have hsum : ds.sum ≤ r * H := by
    simpa only [hlen] using
      sum_le_length_mul_of_admissibleWeylLags hadmissible
  have hprodLe : ds.prod ≤ H ^ r := by
    simpa only [hlen] using
      prod_le_pow_length_of_admissibleWeylLags hadmissible
  have hendpoint :
      (a : ℝ) + (L : ℝ) + (ds.sum : ℝ) ≤
        (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) := by
    have hLR : (L : ℝ) ≤ (b - a : ℕ) := by exact_mod_cast hLN
    have hsumR : (ds.sum : ℝ) ≤ (r * H : ℕ) := by exact_mod_cast hsum
    linarith
  have hprodOne : (1 : ℝ) ≤ ds.prod := by
    exact_mod_cast hprodPos
  have hprodLeR : (ds.prod : ℝ) ≤ (H ^ r : ℕ) := by
    exact_mod_cast hprodLe
  let A : ℝ := ((1 + r).factorial : ℝ) *
    (reciprocalPhaseScale N M j X * q / 10) /
      (2 * X) ^ (1 + r)
  let B : ℝ := ((1 + r).factorial : ℝ) *
    (((((1 + r) + j) ^ (1 + r) : ℕ) : ℝ) *
      reciprocalPhaseScale N M j X) /
        X ^ (1 + r)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hupperSmallDs : (ds.prod : ℝ) * B ≤ 1 - (ds.prod : ℝ) * A := by
    calc
      (ds.prod : ℝ) * B ≤ ((H ^ r : ℕ) : ℝ) * B :=
        mul_le_mul_of_nonneg_right hprodLeR hB
      _ ≤ 1 - ((H ^ r : ℕ) : ℝ) * A := by
        simpa only [A, B] using hupperSmall
      _ ≤ 1 - (ds.prod : ℝ) * A := by
        have := mul_le_mul_of_nonneg_right hprodLeR hA.le
        linarith
  have hterminal :=
    norm_iteratedReciprocalPhaseExponentialSum_le_inv_regularScale
      N M orders ds (X := X) (Y := Y) (q := q) (a := (a : ℝ)) L
      hX hF hq hqOne hj hprodPos haIcc
      (hendpoint.trans hevalY) (hendpoint.trans hevalTop)
      (by
        intro y hy
        exact hregular y ⟨hy.1, hy.2.trans hendpoint⟩)
      (by simpa only [hlen] using hrOne)
      (by simpa only [hlen] using hrTwo)
      (by simpa only [hlen, A, B] using hupperSmallDs)
  have hden : A ≤ (ds.prod : ℝ) * A := by
    nlinarith
  calc
    ‖phaseExponentialSum
        (iteratedForwardPhaseDifference
          (fun n => reciprocalPhase N M j (a + n)) ds) L‖ =
        ‖phaseExponentialSum
          (iteratedForwardPhaseDifference
            (fun n => reciprocalPhase N M j ((a : ℝ) + n)) ds) L‖ := by
          congr 4
    _ ≤ 1 / ((ds.prod : ℝ) * A) := by
      simpa only [hlen, A] using hterminal
    _ ≤ 1 / A := one_div_le_one_div_of_le hA hden
    _ = 1 / (((1 + r).factorial : ℝ) *
        (reciprocalPhaseScale N M j X * q / 10) /
          (2 * X) ^ (1 + r)) := rfl

/-- The uniform critical-regular terminal estimate fed directly through all
`r` finite Weyl rounds to the original reciprocal-phase interval sum. -/
theorem norm_reciprocalPhaseSum_le_weylRecursiveMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (r a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (r * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrOne : 1 + r ∈ orders) (hrTwo : 2 + r ∈ orders)
    (hupperSmall :
      ((H ^ r : ℕ) : ℝ) *
          (((1 + r).factorial : ℝ) *
              (((((1 + r) + j) ^ (1 + r) : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) /
            X ^ (1 + r)) ≤
        1 - ((H ^ r : ℕ) : ℝ) *
          (((1 + r).factorial : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (1 + r))) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylRecursiveMajorant (b - a) H r
        (1 / (((1 + r).factorial : ℝ) *
          (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (1 + r))) := by
  apply norm_reciprocalPhaseSum_le_weylRecursiveMajorant
  · positivity
  · exact uniformIteratedPhaseBound_reciprocalPhase_of_regularScale
      N M orders r a b H hX hF hq hqOne hj haIcc hevalY hevalTop
      hregular hrOne hrTwo hupperSmall

/-- Literal four-round critical-regular Weyl interface for the source's
degree-five branch.  The terminal Kusmin--Landau test uses derivative orders
five and six, and all admissible lag products are controlled uniformly by
`H^4`. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (4 * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (((((5 + j) ^ 5 : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) / X ^ 5)) ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylRecursiveMajorant (b - a) H 4
        (1 / ((Nat.factorial 5 : ℝ) *
          (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) := by
  apply norm_reciprocalPhaseSum_le_weylRecursiveMajorant_regularScale
    N M orders 4 a b H hX hF hq hqOne hj haIcc hevalY hevalTop
    hregular hrFive hrSix
  norm_num at hupperSmall ⊢
  convert hupperSmall using 1
  ring

/-- Terminal profile retaining both the trivial truncation-length bound and
the inverse lag-product gain from Kusmin--Landau. -/
def lagProductTerminalMajorant (scale : ℝ) (ds : List ℕ) (L : ℕ) : ℝ :=
  min (L : ℝ) (1 / ((ds.prod : ℝ) * scale))

theorem lagProductTerminalMajorant_nonneg
    {scale : ℝ} (hscale : 0 ≤ scale) (ds : List ℕ) (L : ℕ) :
    0 ≤ lagProductTerminalMajorant scale ds L := by
  unfold lagProductTerminalMajorant
  positivity

/-- The reciprocal successor sum over the strict Weyl lag range is exactly
the real cast of the `H`-th harmonic number. -/
theorem sum_range_inv_succ_eq_harmonic (H : ℕ) :
    ∑ d ∈ Finset.range H, (1 / ((d + 1 : ℕ) : ℝ)) =
      ((harmonic H : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [Finset.Icc_eq_Ico]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.cast_add, Nat.cast_one, one_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [add_comm]

/-- Summing the lag-sensitive terminal profile over one newly appended lag
costs exactly one harmonic factor while retaining the inverse product of all
earlier lags.  The boundary-truncated terminal lengths may vary arbitrarily. -/
theorem sum_lagProductTerminalMajorant_append_le_harmonic
    {scale : ℝ} (hscale : 0 < scale) (base : List ℕ) (hprod : 0 < base.prod)
    (H : ℕ) (K : ℕ → ℕ) :
    ∑ d ∈ Finset.range H,
        lagProductTerminalMajorant scale (base ++ [d + 1]) (K d) ≤
      (1 / ((base.prod : ℝ) * scale)) * ((harmonic H : ℚ) : ℝ) := by
  have hbaseR : (0 : ℝ) < base.prod := by exact_mod_cast hprod
  calc
    ∑ d ∈ Finset.range H,
        lagProductTerminalMajorant scale (base ++ [d + 1]) (K d) ≤
        ∑ d ∈ Finset.range H,
          1 / ((((base ++ [d + 1]).prod : ℕ) : ℝ) * scale) := by
      apply Finset.sum_le_sum
      intro d hd
      exact min_le_right _ _
    _ = ∑ d ∈ Finset.range H,
        (1 / ((base.prod : ℝ) * scale)) *
          (1 / ((d + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [List.prod_append, List.prod_singleton, Nat.cast_mul]
      have hdR : (0 : ℝ) < d + 1 := by positivity
      field_simp
    _ = (1 / ((base.prod : ℝ) * scale)) *
        (∑ d ∈ Finset.range H, 1 / ((d + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (1 / ((base.prod : ℝ) * scale)) *
        ((harmonic H : ℚ) : ℝ) := by
      rw [sum_range_inv_succ_eq_harmonic]

/-- The innermost Weyl-tree level is bounded explicitly by one harmonic
factor and the inverse product of the previously accumulated lags. -/
theorem weylTreeMajorant_one_lagProduct_le_harmonic
    {scale : ℝ} (hscale : 0 < scale) (base : List ℕ) (hprod : 0 < base.prod)
    (H L : ℕ) :
    weylTreeMajorant H (lagProductTerminalMajorant scale) 1 base L ≤
      Real.sqrt
        ((2 * ((L + (H + 1) : ℕ) : ℝ) *
          ((L : ℝ) + (1 / ((base.prod : ℝ) * scale)) *
            ((harmonic H : ℚ) : ℝ))) / ((H + 1 : ℕ) : ℝ)) := by
  rw [weylTreeMajorant]
  gcongr
  exact sum_lagProductTerminalMajorant_append_le_harmonic
   hscale base hprod H (fun d => L - (d + 1))

theorem inv_sqrt_succ_le_two_mul_sqrt_sub (n : ℕ) :
    1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hn1 : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_iff₀ hs1]
  have hsq0 := Real.sq_sqrt hn
  have hsq1 := Real.sq_sqrt hn1
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  nlinarith [sq_nonneg
    (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))]

theorem sum_range_inv_sqrt_succ_le (H : ℕ) :
    ∑ d ∈ Finset.range H, 1 / Real.sqrt ((d + 1 : ℕ) : ℝ) ≤
      2 * Real.sqrt (H : ℝ) := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ x ∈ Finset.range H, 1 / Real.sqrt ((x + 1 : ℕ) : ℝ)) +
            1 / Real.sqrt ((H + 1 : ℕ) : ℝ) ≤
            2 * Real.sqrt (H : ℝ) +
              2 * (Real.sqrt ((H + 1 : ℕ) : ℝ) - Real.sqrt (H : ℝ)) :=
          add_le_add ih (inv_sqrt_succ_le_two_mul_sqrt_sub H)
        _ = 2 * Real.sqrt ((H + 1 : ℕ) : ℝ) := by ring


theorem sqrt_add_le_add_sqrt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A + B) ≤ Real.sqrt A + Real.sqrt B := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have hsAB := Real.sq_sqrt (add_nonneg hA hB)
  nlinarith [Real.sqrt_nonneg A, Real.sqrt_nonneg B,
    Real.sqrt_nonneg (A + B),
    mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]

theorem sum_sqrt_affine_inv_succ_le
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (H : ℕ) :
    ∑ d ∈ Finset.range H,
        Real.sqrt (A * (B + C / ((d + 1 : ℕ) : ℝ))) ≤
      Real.sqrt A *
        ((H : ℝ) * Real.sqrt B +
          2 * Real.sqrt (H : ℝ) * Real.sqrt C) := by
  calc
    ∑ d ∈ Finset.range H,
        Real.sqrt (A * (B + C / ((d + 1 : ℕ) : ℝ))) =
        ∑ d ∈ Finset.range H,
          Real.sqrt A * Real.sqrt (B + C / ((d + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Real.sqrt_mul hA]
    _ ≤ ∑ d ∈ Finset.range H,
        Real.sqrt A *
          (Real.sqrt B + Real.sqrt (C / ((d + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro d hd
      gcongr
      exact sqrt_add_le_add_sqrt hB (div_nonneg hC (by positivity))
    _ = Real.sqrt A *
        ((H : ℝ) * Real.sqrt B +
          Real.sqrt C *
            (∑ d ∈ Finset.range H,
              1 / Real.sqrt ((d + 1 : ℕ) : ℝ))) := by
      calc
        ∑ d ∈ Finset.range H,
            Real.sqrt A *
              (Real.sqrt B + Real.sqrt (C / ((d + 1 : ℕ) : ℝ))) =
            ∑ d ∈ Finset.range H,
              (Real.sqrt A * Real.sqrt B +
                Real.sqrt A * Real.sqrt (C / ((d + 1 : ℕ) : ℝ))) := by
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = (H : ℝ) * (Real.sqrt A * Real.sqrt B) +
            ∑ x ∈ Finset.range H,
              Real.sqrt A * Real.sqrt (C / ((x + 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ =
            Real.sqrt A * ((H : ℝ) * Real.sqrt B +
              ∑ x ∈ Finset.range H,
                Real.sqrt (C / ((x + 1 : ℕ) : ℝ))) := by
          rw [← Finset.mul_sum]
          ring
        _ = Real.sqrt A * ((H : ℝ) * Real.sqrt B +
            Real.sqrt C *
              (∑ d ∈ Finset.range H,
                1 / Real.sqrt ((d + 1 : ℕ) : ℝ))) := by
          congr 2
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Real.sqrt_div hC]
          ring
    _ ≤ Real.sqrt A *
        ((H : ℝ) * Real.sqrt B +
          Real.sqrt C * (2 * Real.sqrt (H : ℝ))) := by
      gcongr
      exact sum_range_inv_sqrt_succ_le H
    _ = Real.sqrt A *
        ((H : ℝ) * Real.sqrt B +
          2 * Real.sqrt (H : ℝ) * Real.sqrt C) := by ring

def weylTreeStepFactor (H L : ℕ) : ℝ :=
  2 * ((L + (H + 1) : ℕ) : ℝ) / ((H + 1 : ℕ) : ℝ)

theorem weylTreeStepFactor_nonneg (H L : ℕ) :
    0 ≤ weylTreeStepFactor H L := by
  unfold weylTreeStepFactor
  positivity

theorem weylTreeStepFactor_mono {H K L : ℕ} (hKL : K ≤ L) :
    weylTreeStepFactor H K ≤ weylTreeStepFactor H L := by
  unfold weylTreeStepFactor
  gcongr

def lagProductTwoStepMajorant
    (H : ℕ) (scale : ℝ) (base : List ℕ) (L : ℕ) : ℝ :=
  Real.sqrt (weylTreeStepFactor H L *
    ((L : ℝ) + Real.sqrt (weylTreeStepFactor H L) *
      ((H : ℝ) * Real.sqrt (L : ℝ) +
        2 * Real.sqrt (H : ℝ) *
          Real.sqrt
            ((1 / ((base.prod : ℝ) * scale)) *
              ((harmonic H : ℚ) : ℝ)))))

theorem weylTreeMajorant_two_lagProduct_le
    {scale : ℝ} (hscale : 0 < scale) (base : List ℕ) (hprod : 0 < base.prod)
    (H L : ℕ) :
    weylTreeMajorant H (lagProductTerminalMajorant scale) 2 base L ≤
      lagProductTwoStepMajorant H scale base L := by
  have hbaseR : (0 : ℝ) < base.prod := by exact_mod_cast hprod
  have hharm : (0 : ℝ) ≤ ((harmonic H : ℚ) : ℝ) := by
    rw [← sum_range_inv_succ_eq_harmonic]
    positivity
  have hC : 0 ≤
      (1 / ((base.prod : ℝ) * scale)) * ((harmonic H : ℚ) : ℝ) := by
    positivity
  rw [weylTreeMajorant]
  unfold lagProductTwoStepMajorant
  apply Real.sqrt_le_sqrt
  have hstep (Z : ℝ) :
      (2 * ((L + (H + 1) : ℕ) : ℝ) * Z) / ((H + 1 : ℕ) : ℝ) =
        weylTreeStepFactor H L * Z := by
    unfold weylTreeStepFactor
    ring
  rw [hstep]
  change weylTreeStepFactor H L *
      ((L : ℝ) + ∑ d ∈ Finset.range H,
        weylTreeMajorant H (lagProductTerminalMajorant scale) 1
          (base ++ [d + 1]) (L - (d + 1))) ≤
    weylTreeStepFactor H L *
      ((L : ℝ) + Real.sqrt (weylTreeStepFactor H L) *
        ((H : ℝ) * Real.sqrt (L : ℝ) +
          2 * Real.sqrt (H : ℝ) *
            Real.sqrt
              ((1 / ((base.prod : ℝ) * scale)) *
                ((harmonic H : ℚ) : ℝ))))
  apply mul_le_mul_of_nonneg_left
  apply add_le_add_right
  calc
    ∑ d ∈ Finset.range H,
        weylTreeMajorant H (lagProductTerminalMajorant scale) 1
          (base ++ [d + 1]) (L - (d + 1)) ≤
        ∑ d ∈ Finset.range H,
          Real.sqrt (weylTreeStepFactor H L *
            ((L : ℝ) +
              ((1 / ((base.prod : ℝ) * scale)) *
                ((harmonic H : ℚ) : ℝ)) /
                  ((d + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d + 1 := by omega
      have hprodChild : 0 < (base ++ [d + 1]).prod := by
        simp only [List.prod_append, List.prod_singleton]
        positivity
      calc
        weylTreeMajorant H (lagProductTerminalMajorant scale) 1
            (base ++ [d + 1]) (L - (d + 1)) ≤
            Real.sqrt
              ((2 * ((((L - (d + 1)) + (H + 1) : ℕ)) : ℝ) *
                (((L - (d + 1) : ℕ) : ℝ) +
                  (1 / ((((base ++ [d + 1]).prod : ℕ) : ℝ) * scale)) *
                    ((harmonic H : ℚ) : ℝ))) /
                  ((H + 1 : ℕ) : ℝ)) :=
          weylTreeMajorant_one_lagProduct_le_harmonic
            hscale (base ++ [d + 1]) hprodChild H (L - (d + 1))
        _ ≤ Real.sqrt (weylTreeStepFactor H L *
            ((L : ℝ) +
              ((1 / ((base.prod : ℝ) * scale)) *
                ((harmonic H : ℚ) : ℝ)) /
                  ((d + 1 : ℕ) : ℝ))) := by
          apply Real.sqrt_le_sqrt
          have hlen : L - (d + 1) ≤ L := Nat.sub_le _ _
          have hfactor := weylTreeStepFactor_mono (H := H) hlen
          have hinner :
              (((L - (d + 1) : ℕ) : ℝ) +
                  (1 / ((((base ++ [d + 1]).prod : ℕ) : ℝ) * scale)) *
                    ((harmonic H : ℚ) : ℝ)) ≤
                (L : ℝ) +
                  ((1 / ((base.prod : ℝ) * scale)) *
                    ((harmonic H : ℚ) : ℝ)) /
                      ((d + 1 : ℕ) : ℝ) := by
            have hlenR : ((L - (d + 1) : ℕ) : ℝ) ≤ (L : ℝ) := by
              exact_mod_cast hlen
            have hident :
                (1 / ((((base ++ [d + 1]).prod : ℕ) : ℝ) * scale)) *
                    ((harmonic H : ℚ) : ℝ) =
                  ((1 / ((base.prod : ℝ) * scale)) *
                    ((harmonic H : ℚ) : ℝ)) /
                      ((d + 1 : ℕ) : ℝ) := by
              simp only [List.prod_append, List.prod_singleton, Nat.cast_mul]
              field_simp
            rw [hident]
            exact add_le_add_left hlenR _
          have hfactor0 := weylTreeStepFactor_nonneg H (L - (d + 1))
          have hinner0 : 0 ≤
              (((L - (d + 1) : ℕ) : ℝ) +
                (1 / ((((base ++ [d + 1]).prod : ℕ) : ℝ) * scale)) *
                  ((harmonic H : ℚ) : ℝ)) := by positivity
          have hstepChild (Z : ℝ) :
              (2 * ((((L - (d + 1)) + (H + 1) : ℕ)) : ℝ) * Z) /
                  ((H + 1 : ℕ) : ℝ) =
                weylTreeStepFactor H (L - (d + 1)) * Z := by
            unfold weylTreeStepFactor
            ring
          rw [hstepChild]
          change weylTreeStepFactor H (L - (d + 1)) *
              (((L - (d + 1) : ℕ) : ℝ) +
                (1 / ((((base ++ [d + 1]).prod : ℕ) : ℝ) * scale)) *
                  ((harmonic H : ℚ) : ℝ)) ≤ _
          exact mul_le_mul hfactor hinner hinner0
            (weylTreeStepFactor_nonneg H L)
    _ ≤ Real.sqrt (weylTreeStepFactor H L) *
        ((H : ℝ) * Real.sqrt (L : ℝ) +
          2 * Real.sqrt (H : ℝ) *
            Real.sqrt
              ((1 / ((base.prod : ℝ) * scale)) *
                ((harmonic H : ℚ) : ℝ))) := by
      exact sum_sqrt_affine_inv_succ_le
        (weylTreeStepFactor_nonneg H L) (by positivity) hC H
  exact weylTreeStepFactor_nonneg H L

/-- Repeated principal square root, used to record the exact exponent halving
at each outer Weyl-differencing level. -/
def iteratedSqrt : ℕ → ℝ → ℝ
  | 0, x => x
  | r + 1, x => Real.sqrt (iteratedSqrt r x)

theorem iteratedSqrt_nonneg {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    0 ≤ iteratedSqrt r x := by
  cases r with
  | zero => exact hx
  | succ r => exact Real.sqrt_nonneg _

theorem iteratedSqrt_mono {x y : ℝ} (hxy : x ≤ y) (r : ℕ) :
    iteratedSqrt r x ≤ iteratedSqrt r y := by
  induction r with
  | zero => exact hxy
  | succ r ih =>
      simp only [iteratedSqrt]
      exact Real.sqrt_le_sqrt ih

theorem iteratedSqrt_pos {x : ℝ} (hx : 0 < x) (r : ℕ) :
    0 < iteratedSqrt r x := by
  induction r with
  | zero => exact hx
  | succ r ih =>
      rw [iteratedSqrt]
      exact Real.sqrt_pos.2 ih

theorem iteratedSqrt_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (r : ℕ) :
    iteratedSqrt r (x / y) =
      iteratedSqrt r x / iteratedSqrt r y := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [iteratedSqrt, iteratedSqrt, iteratedSqrt, ih,
        Real.sqrt_div (iteratedSqrt_nonneg hx r)]

/-- Exact finite generalized harmonic factor produced at Weyl depth `r`.
For `r=0` this is the ordinary harmonic sum, while each later depth halves
the reciprocal exponent. -/
def iteratedRootHarmonic (r H : ℕ) : ℝ :=
  ∑ d ∈ Finset.range H,
    1 / iteratedSqrt r ((d + 1 : ℕ) : ℝ)

theorem iteratedRootHarmonic_nonneg (r H : ℕ) :
    0 ≤ iteratedRootHarmonic r H := by
  unfold iteratedRootHarmonic
  apply Finset.sum_nonneg
  intro d hd
  exact one_div_nonneg.mpr
    (iteratedSqrt_nonneg (by positivity) r)

theorem iteratedSqrt_one (r : ℕ) :
    iteratedSqrt r 1 = 1 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [iteratedSqrt, ih]

theorem one_le_iteratedSqrt {x : ℝ} (hx : 1 ≤ x) (r : ℕ) :
    1 ≤ iteratedSqrt r x := by
  induction r with
  | zero => exact hx
  | succ r ih =>
      rw [iteratedSqrt]
      have hs := Real.sqrt_le_sqrt ih
      simpa using hs

/-- Every generalized harmonic factor in the closed Weyl envelope is at most
the number of available lags. -/
theorem iteratedRootHarmonic_le (r H : ℕ) :
    iteratedRootHarmonic r H ≤ (H : ℝ) := by
  unfold iteratedRootHarmonic
  calc
    ∑ d ∈ Finset.range H,
        1 / iteratedSqrt r ((d + 1 : ℕ) : ℝ) ≤
        ∑ _d ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have harg : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
      have hden := one_le_iteratedSqrt harg r
      exact (div_le_one (iteratedSqrt_pos (by positivity) r)).2 hden
    _ = (H : ℝ) := by simp

/-- At depth zero the generalized harmonic sum is the ordinary harmonic
number. -/
theorem iteratedRootHarmonic_zero_eq_harmonic (H : ℕ) :
    iteratedRootHarmonic 0 H = ((harmonic H : ℚ) : ℝ) := by
  unfold iteratedRootHarmonic
  simpa [iteratedSqrt] using sum_range_inv_succ_eq_harmonic H

/-- The only genuinely logarithmic factor in the sharp four-step terminal
term is controlled by the standard harmonic-number estimate. -/
theorem iteratedRootHarmonic_zero_le_one_add_log (H : ℕ) :
    iteratedRootHarmonic 0 H ≤ 1 + Real.log H := by
  rw [iteratedRootHarmonic_zero_eq_harmonic]
  exact harmonic_le_one_add_log H

/-- Cauchy--Schwarz propagation for successive generalized harmonic sums.
Each extra root halves the reciprocal exponent without paying the full factor
`H`. -/
theorem iteratedRootHarmonic_succ_sq_le (r H : ℕ) :
    (iteratedRootHarmonic (r + 1) H) ^ 2 ≤
      (H : ℝ) * iteratedRootHarmonic r H := by
  unfold iteratedRootHarmonic
  calc
    (∑ d ∈ Finset.range H,
        1 / iteratedSqrt (r + 1) ((d + 1 : ℕ) : ℝ)) ^ 2 ≤
      ((Finset.range H).card : ℝ) *
        ∑ d ∈ Finset.range H,
          (1 / iteratedSqrt (r + 1) ((d + 1 : ℕ) : ℝ)) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (H : ℝ) * ∑ d ∈ Finset.range H,
          1 / iteratedSqrt r ((d + 1 : ℕ) : ℝ) := by
      rw [Finset.card_range]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [div_pow, one_pow, iteratedSqrt,
        Real.sq_sqrt (iteratedSqrt_nonneg (by positivity) r)]

/-- Four iterated square roots are exactly a nonnegative sixteenth root. -/
theorem iteratedSqrt_four_pow_sixteen {x : ℝ} (hx : 0 ≤ x) :
    (iteratedSqrt 4 x) ^ 16 = x := by
  change (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt x)))) ^ 16 = x
  rw [show (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt x)))) ^ 16 =
      ((Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt x)))) ^ 2) ^ 8 by ring,
    Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [show (Real.sqrt (Real.sqrt (Real.sqrt x))) ^ 8 =
      ((Real.sqrt (Real.sqrt (Real.sqrt x))) ^ 2) ^ 4 by ring,
    Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [show (Real.sqrt (Real.sqrt x)) ^ 4 =
      ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 by ring,
    Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt hx]

/-- The length/diagonal part of the closed lag-sensitive Weyl envelope. -/
def weylLagLengthCoefficient (H L : ℕ) : ℕ → ℝ
  | 0 => 0
  | r + 1 =>
      Real.sqrt (weylTreeStepFactor H L *
        ((L : ℝ) + (H : ℝ) * weylLagLengthCoefficient H L r))

/-- The scale-dependent coefficient of the closed lag-sensitive Weyl
envelope. -/
def weylLagScaleCoefficient (H L : ℕ) : ℕ → ℝ
  | 0 => 1
  | r + 1 =>
      Real.sqrt (weylTreeStepFactor H L *
        weylLagScaleCoefficient H L r *
          iteratedRootHarmonic r H)

theorem weylLagLengthCoefficient_nonneg (H L r : ℕ) :
    0 ≤ weylLagLengthCoefficient H L r := by
  cases r with
  | zero => simp [weylLagLengthCoefficient]
  | succ r => exact Real.sqrt_nonneg _

theorem weylLagScaleCoefficient_nonneg (H L r : ℕ) :
    0 ≤ weylLagScaleCoefficient H L r := by
  cases r with
  | zero => simp [weylLagScaleCoefficient]
  | succ r => exact Real.sqrt_nonneg _

/-- Closed scalar envelope for the entire lag-sensitive Weyl tree. -/
def weylLagClosedMajorant
    (H L r : ℕ) (scale : ℝ) (base : List ℕ) : ℝ :=
  weylLagLengthCoefficient H L r +
    weylLagScaleCoefficient H L r *
      iteratedSqrt r (1 / ((base.prod : ℝ) * scale))

theorem weylTreeMajorant_lagProduct_le_closed
    {scale : ℝ} (hscale : 0 < scale) (base : List ℕ) (hprod : 0 < base.prod)
    (H L r K : ℕ) (hKL : K ≤ L) :
    weylTreeMajorant H (lagProductTerminalMajorant scale) r base K ≤
      weylLagClosedMajorant H L r scale base := by
  induction r generalizing base K with
  | zero =>
      simp only [weylTreeMajorant, weylLagClosedMajorant,
        weylLagLengthCoefficient, weylLagScaleCoefficient,
        iteratedSqrt, zero_add, one_mul]
      exact (min_le_right _ _)
  | succ r ih =>
      have hbaseR : (0 : ℝ) < base.prod := by exact_mod_cast hprod
      let C : ℝ := 1 / ((base.prod : ℝ) * scale)
      have hC : 0 < C := by dsimp only [C]; positivity
      let A : ℝ := weylLagLengthCoefficient H L r
      let B : ℝ := weylLagScaleCoefficient H L r
      let R : ℝ := iteratedSqrt r C
      let S : ℝ := iteratedRootHarmonic r H
      have hA : 0 ≤ A := by
        exact weylLagLengthCoefficient_nonneg H L r
      have hB : 0 ≤ B := by
        exact weylLagScaleCoefficient_nonneg H L r
      have hR : 0 ≤ R := iteratedSqrt_nonneg hC.le r
      have hS : 0 ≤ S := iteratedRootHarmonic_nonneg r H
      have hsum :
          ∑ d ∈ Finset.range H,
              weylTreeMajorant H (lagProductTerminalMajorant scale) r
                (base ++ [d + 1]) (K - (d + 1)) ≤
            (H : ℝ) * A + B * R * S := by
        calc
          ∑ d ∈ Finset.range H,
              weylTreeMajorant H (lagProductTerminalMajorant scale) r
                (base ++ [d + 1]) (K - (d + 1)) ≤
              ∑ d ∈ Finset.range H,
                (A + B * iteratedSqrt r
                  (C / ((d + 1 : ℕ) : ℝ))) := by
            apply Finset.sum_le_sum
            intro d hd
            have hdpos : 0 < d + 1 := by omega
            have hprodChild : 0 < (base ++ [d + 1]).prod := by
              simp only [List.prod_append, List.prod_singleton]
              positivity
            have hchild := ih (base ++ [d + 1]) hprodChild
              (K - (d + 1)) ((Nat.sub_le K (d + 1)).trans hKL)
            unfold weylLagClosedMajorant at hchild
            change _ ≤ A + B * iteratedSqrt r
              (1 / ((((base ++ [d + 1]).prod : ℕ) : ℝ) * scale)) at hchild
            have hident :
                1 / ((((base ++ [d + 1]).prod : ℕ) : ℝ) * scale) =
                  C / ((d + 1 : ℕ) : ℝ) := by
              dsimp only [C]
              simp only [List.prod_append, List.prod_singleton, Nat.cast_mul]
              field_simp
            simpa only [hident] using hchild
          _ = (H : ℝ) * A + B *
              (∑ d ∈ Finset.range H,
                iteratedSqrt r (C / ((d + 1 : ℕ) : ℝ))) := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [Finset.mul_sum]
          _ = (H : ℝ) * A + B * R * S := by
            have hrootSum :
                (∑ d ∈ Finset.range H,
                  iteratedSqrt r (C / ((d + 1 : ℕ) : ℝ))) =
                  R * S := by
              dsimp only [R, S, iteratedRootHarmonic]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro d hd
              rw [iteratedSqrt_div hC.le]
              ring
            rw [hrootSum]
            ring
      rw [weylTreeMajorant]
      unfold weylLagClosedMajorant
      rw [weylLagLengthCoefficient, weylLagScaleCoefficient,
        iteratedSqrt]
      have hstepK (Z : ℝ) :
          (2 * ((K + (H + 1) : ℕ) : ℝ) * Z) / ((H + 1 : ℕ) : ℝ) =
            weylTreeStepFactor H K * Z := by
        unfold weylTreeStepFactor
        ring
      rw [hstepK]
      have hfactor : weylTreeStepFactor H K ≤
          weylTreeStepFactor H L :=
        weylTreeStepFactor_mono hKL
      have hKR : (K : ℝ) ≤ (L : ℝ) := by exact_mod_cast hKL
      have htreeNonneg : 0 ≤
          (K : ℝ) + ∑ d ∈ Finset.range H,
            weylTreeMajorant H (lagProductTerminalMajorant scale) r
              (base ++ [d + 1]) (K - (d + 1)) := by
        apply add_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro d hd
        apply weylTreeMajorant_nonneg
        intro ds J
        exact lagProductTerminalMajorant_nonneg hscale.le ds J
      calc
        Real.sqrt (weylTreeStepFactor H K *
            ((K : ℝ) + ∑ d ∈ Finset.range H,
              weylTreeMajorant H (lagProductTerminalMajorant scale) r
                (base ++ [d + 1]) (K - (d + 1)))) ≤
            Real.sqrt (weylTreeStepFactor H L *
              ((L : ℝ) + ((H : ℝ) * A + B * R * S))) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul hfactor (add_le_add hKR hsum)
            htreeNonneg (weylTreeStepFactor_nonneg H L)
        _ = Real.sqrt (weylTreeStepFactor H L *
              ((L : ℝ) + (H : ℝ) * A) +
            (weylTreeStepFactor H L * B * S) * R) := by
          congr 1
          ring
        _ ≤ Real.sqrt (weylTreeStepFactor H L *
              ((L : ℝ) + (H : ℝ) * A)) +
            Real.sqrt ((weylTreeStepFactor H L * B * S) * R) :=
          sqrt_add_le_add_sqrt
            (mul_nonneg (weylTreeStepFactor_nonneg H L)
              (add_nonneg (by positivity) (mul_nonneg (by positivity) hA)))
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (weylTreeStepFactor_nonneg H L) hB) hS) hR)
        _ = Real.sqrt (weylTreeStepFactor H L *
              ((L : ℝ) + (H : ℝ) * A)) +
            Real.sqrt (weylTreeStepFactor H L * B * S) *
              Real.sqrt R := by
          rw [Real.sqrt_mul
            (mul_nonneg
              (mul_nonneg (weylTreeStepFactor_nonneg H L) hB) hS)]
        _ = Real.sqrt (weylTreeStepFactor H L *
              ((L : ℝ) + (H : ℝ) *
                weylLagLengthCoefficient H L r)) +
            Real.sqrt (weylTreeStepFactor H L *
              weylLagScaleCoefficient H L r *
                iteratedRootHarmonic r H) *
              Real.sqrt (iteratedSqrt r C) := by rfl
        _ = Real.sqrt (weylTreeStepFactor H L *
              ((L : ℝ) + (H : ℝ) *
                weylLagLengthCoefficient H L r)) +
            Real.sqrt (weylTreeStepFactor H L *
              weylLagScaleCoefficient H L r *
                iteratedRootHarmonic r H) *
              Real.sqrt (iteratedSqrt r
               (1 / ((base.prod : ℝ) * scale))) := by rfl

/-- Coarse scale recurrence obtained by bounding every generalized harmonic
factor in the exact closed Weyl envelope by `H`. -/
def weylLagScaleCoarseCoefficient (H L : ℕ) : ℕ → ℝ
  | 0 => 1
  | r + 1 =>
      Real.sqrt (weylTreeStepFactor H L * (H : ℝ) *
        weylLagScaleCoarseCoefficient H L r)

theorem weylLagScaleCoarseCoefficient_nonneg (H L r : ℕ) :
    0 ≤ weylLagScaleCoarseCoefficient H L r := by
  cases r with
  | zero => simp [weylLagScaleCoarseCoefficient]
  | succ r => exact Real.sqrt_nonneg _

theorem weylLagScaleCoefficient_le_coarse (H L r : ℕ) :
    weylLagScaleCoefficient H L r ≤
      weylLagScaleCoarseCoefficient H L r := by
  induction r with
  | zero => simp [weylLagScaleCoefficient,
      weylLagScaleCoarseCoefficient]
  | succ r ih =>
      rw [weylLagScaleCoefficient, weylLagScaleCoarseCoefficient]
      apply Real.sqrt_le_sqrt
      have hm := mul_le_mul ih (iteratedRootHarmonic_le r H)
        (iteratedRootHarmonic_nonneg r H)
        (weylLagScaleCoarseCoefficient_nonneg H L r)
      calc
        weylTreeStepFactor H L * weylLagScaleCoefficient H L r *
            iteratedRootHarmonic r H =
            weylTreeStepFactor H L *
              (weylLagScaleCoefficient H L r * iteratedRootHarmonic r H) := by ring
        _ ≤ weylTreeStepFactor H L *
              (weylLagScaleCoarseCoefficient H L r * (H : ℝ)) :=
          mul_le_mul_of_nonneg_left hm (weylTreeStepFactor_nonneg H L)
        _ = weylTreeStepFactor H L * (H : ℝ) *
              weylLagScaleCoarseCoefficient H L r := by ring

theorem weylLagClosedMajorant_le_coarseScale
    {scale : ℝ} (hscale : 0 < scale) (base : List ℕ) (hprod : 0 < base.prod)
    (H L r : ℕ) :
    weylLagClosedMajorant H L r scale base ≤
      weylLagLengthCoefficient H L r +
        weylLagScaleCoarseCoefficient H L r *
          iteratedSqrt r (1 / ((base.prod : ℝ) * scale)) := by
  unfold weylLagClosedMajorant
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right
  · exact weylLagScaleCoefficient_le_coarse H L r
  · apply iteratedSqrt_nonneg
    positivity

theorem weylLagScaleCoarseCoefficient_four_pow_sixteen
    (H L : ℕ) :
    (weylLagScaleCoarseCoefficient H L 4) ^ 16 =
      (weylTreeStepFactor H L * (H : ℝ)) ^ 15 := by
  let E : ℝ := weylTreeStepFactor H L * (H : ℝ)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  change (Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * 1))))) ^ 16 =
    E ^ 15
  have h1 : 0 ≤ Real.sqrt (E * 1) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (E * Real.sqrt (E * 1)) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * 1))) :=
    Real.sqrt_nonneg _
  rw [show (Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * 1))))) ^ 16 =
      ((Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * 1))))) ^ 2) ^ 8 by ring,
    Real.sq_sqrt (mul_nonneg hE h3)]
  rw [show (E * Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * 1)))) ^ 8 =
      E ^ 8 *
        ((Real.sqrt (E * Real.sqrt (E * Real.sqrt (E * 1)))) ^ 2) ^ 4 by ring,
    Real.sq_sqrt (mul_nonneg hE h2)]
  rw [show E ^ 8 * (E * Real.sqrt (E * Real.sqrt (E * 1))) ^ 4 =
      E ^ 12 * ((Real.sqrt (E * Real.sqrt (E * 1))) ^ 2) ^ 2 by ring,
    Real.sq_sqrt (mul_nonneg hE h1)]
  rw [show E ^ 12 * (E * Real.sqrt (E * 1)) ^ 2 =
      E ^ 14 * (Real.sqrt (E * 1)) ^ 2 by ring,
    Real.sq_sqrt (mul_nonneg hE (by positivity))]
  ring

theorem weylLagScaleTerm_four_pow_sixteen
    {scale : ℝ} (hscale : 0 < scale) (H L : ℕ) :
    (weylLagScaleCoarseCoefficient H L 4 *
        iteratedSqrt 4 (1 / scale)) ^ 16 =
      (weylTreeStepFactor H L * (H : ℝ)) ^ 15 * (1 / scale) := by
  rw [mul_pow, weylLagScaleCoarseCoefficient_four_pow_sixteen,
   iteratedSqrt_four_pow_sixteen (by positivity)]

theorem weylLagLengthCoefficient_succ (H L r : ℕ) :
    weylLagLengthCoefficient H L (r + 1) =
      Real.sqrt
        (weylTreeStepFactor H L * (L : ℝ) +
          (weylTreeStepFactor H L * (H : ℝ)) *
            weylLagLengthCoefficient H L r) := by
  rw [weylLagLengthCoefficient]
  congr 1
  ring

def weylLagLengthTerms (D E : ℝ) : ℕ → List ℝ
  | 0 => []
  | r + 1 =>
      Real.sqrt D ::
        (weylLagLengthTerms D E r).map
          (fun t => Real.sqrt E * Real.sqrt t)

theorem mem_weylLagLengthTerms_nonneg
    (D E : ℝ) (r : ℕ) :
    ∀ t ∈ weylLagLengthTerms D E r, 0 ≤ t := by
  induction r with
  | zero => simp [weylLagLengthTerms]
  | succ r ih =>
      intro t ht
      simp only [weylLagLengthTerms, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨u, hu, rfl⟩
      · exact Real.sqrt_nonneg _
      · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem sqrt_list_sum_le_sum_sqrt (l : List ℝ)
    (hl : ∀ x ∈ l, 0 ≤ x) :
    Real.sqrt l.sum ≤ (l.map Real.sqrt).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : 0 ≤ a := hl a (by simp)
      have hl' : ∀ x ∈ l, 0 ≤ x := by
        intro x hx
        exact hl x (by simp [hx])
      have hsum : 0 ≤ l.sum := List.sum_nonneg hl'
      simp only [List.sum_cons, List.map_cons]
      calc
        Real.sqrt (a + l.sum) ≤ Real.sqrt a + Real.sqrt l.sum :=
          sqrt_add_le_add_sqrt ha hsum
        _ ≤ Real.sqrt a + (l.map Real.sqrt).sum := by
          gcongr
          exact ih hl'

theorem weylLagLengthCoefficient_le_terms (H L r : ℕ) :
    weylLagLengthCoefficient H L r ≤
      (weylLagLengthTerms
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) r).sum := by
  let D : ℝ := weylTreeStepFactor H L * (L : ℝ)
  let E : ℝ := weylTreeStepFactor H L * (H : ℝ)
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  induction r with
  | zero => simp [weylLagLengthCoefficient, weylLagLengthTerms]
  | succ r ih =>
      rw [weylLagLengthCoefficient_succ]
      change Real.sqrt (D + E * weylLagLengthCoefficient H L r) ≤ _
      calc
        Real.sqrt (D + E * weylLagLengthCoefficient H L r) ≤
            Real.sqrt (D + E *
              (weylLagLengthTerms D E r).sum) := by
          apply Real.sqrt_le_sqrt
          gcongr
        _ ≤ Real.sqrt D +
            Real.sqrt (E * (weylLagLengthTerms D E r).sum) :=
          sqrt_add_le_add_sqrt hD
            (mul_nonneg hE (List.sum_nonneg
              (mem_weylLagLengthTerms_nonneg D E r)))
        _ = Real.sqrt D + Real.sqrt E *
            Real.sqrt (weylLagLengthTerms D E r).sum := by
          rw [Real.sqrt_mul hE]
        _ ≤ Real.sqrt D + Real.sqrt E *
            ((weylLagLengthTerms D E r).map Real.sqrt).sum := by
          gcongr
          exact sqrt_list_sum_le_sum_sqrt _
            (mem_weylLagLengthTerms_nonneg D E r)
        _ = (weylLagLengthTerms D E (r + 1)).sum := by
          rw [weylLagLengthTerms, List.sum_cons, List.sum_map_mul_left]

def weylLagLengthFourMajorant (H L : ℕ) : ℝ :=
  (weylLagLengthTerms
    (weylTreeStepFactor H L * (L : ℝ))
    (weylTreeStepFactor H L * (H : ℝ)) 4).sum

theorem weylLagLengthCoefficient_four_le (H L : ℕ) :
    weylLagLengthCoefficient H L 4 ≤
      weylLagLengthFourMajorant H L :=
  weylLagLengthCoefficient_le_terms H L 4

/-- The successive diagonal monomials exposed by repeatedly splitting square
roots in the length recurrence. -/
def weylLagLengthTerm (D E : ℝ) : ℕ → ℝ
  | 0 => Real.sqrt D
  | k + 1 => Real.sqrt E * Real.sqrt (weylLagLengthTerm D E k)

theorem weylLagLengthTerm_nonneg (D E : ℝ) (k : ℕ) :
    0 ≤ weylLagLengthTerm D E k := by
  cases k with
  | zero => exact Real.sqrt_nonneg _
  | succ k => exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem weylLagLengthFourMajorant_eq_sum_terms (H L : ℕ) :
    weylLagLengthFourMajorant H L =
      weylLagLengthTerm
          (weylTreeStepFactor H L * (L : ℝ))
          (weylTreeStepFactor H L * (H : ℝ)) 0 +
        weylLagLengthTerm
          (weylTreeStepFactor H L * (L : ℝ))
          (weylTreeStepFactor H L * (H : ℝ)) 1 +
        weylLagLengthTerm
          (weylTreeStepFactor H L * (L : ℝ))
          (weylTreeStepFactor H L * (H : ℝ)) 2 +
        weylLagLengthTerm
          (weylTreeStepFactor H L * (L : ℝ))
          (weylTreeStepFactor H L * (H : ℝ)) 3 := by
  simp only [weylLagLengthFourMajorant, weylLagLengthTerms,
    weylLagLengthTerm, List.map, List.sum_cons, List.sum_nil]
  ring

theorem weylLagLengthTerm_zero_pow_sixteen
    {D E : ℝ} (hD : 0 ≤ D) :
    (weylLagLengthTerm D E 0) ^ 16 = D ^ 8 := by
  change (Real.sqrt D) ^ 16 = D ^ 8
  rw [show (Real.sqrt D) ^ 16 = ((Real.sqrt D) ^ 2) ^ 8 by ring,
    Real.sq_sqrt hD]

theorem weylLagLengthTerm_one_pow_sixteen
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (weylLagLengthTerm D E 1) ^ 16 = E ^ 8 * D ^ 4 := by
  change (Real.sqrt E * Real.sqrt (Real.sqrt D)) ^ 16 = E ^ 8 * D ^ 4
  rw [show (Real.sqrt E * Real.sqrt (Real.sqrt D)) ^ 16 =
      ((Real.sqrt E) ^ 2) ^ 8 *
        (((Real.sqrt (Real.sqrt D)) ^ 2) ^ 4) ^ 2 by ring,
    Real.sq_sqrt hE, Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [show ((Real.sqrt D) ^ 4) ^ 2 =
      ((Real.sqrt D) ^ 2) ^ 4 by ring,
    Real.sq_sqrt hD]

theorem weylLagLengthTerm_two_pow_sixteen
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (weylLagLengthTerm D E 2) ^ 16 = E ^ 12 * D ^ 2 := by
  change (Real.sqrt E *
      Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D))) ^ 16 =
    E ^ 12 * D ^ 2
  rw [show (Real.sqrt E *
      Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D))) ^ 16 =
      ((Real.sqrt E) ^ 2) ^ 8 *
        (((Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D))) ^ 2) ^ 4) ^ 2 by ring,
    Real.sq_sqrt hE,
    Real.sq_sqrt (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  rw [show ((Real.sqrt E * Real.sqrt (Real.sqrt D)) ^ 4) ^ 2 =
      (Real.sqrt E * Real.sqrt (Real.sqrt D)) ^ 8 by ring]
  rw [show (Real.sqrt E * Real.sqrt (Real.sqrt D)) ^ 8 =
      ((Real.sqrt E) ^ 2) ^ 4 *
        (((Real.sqrt (Real.sqrt D)) ^ 2) ^ 2) ^ 2 by ring,
    Real.sq_sqrt hE, Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt hD]
  ring

theorem weylLagLengthTerm_three_pow_sixteen
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (weylLagLengthTerm D E 3) ^ 16 = E ^ 14 * D := by
  change (Real.sqrt E * Real.sqrt (Real.sqrt E *
      Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D)))) ^ 16 =
    E ^ 14 * D
  rw [show (Real.sqrt E * Real.sqrt (Real.sqrt E *
      Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D)))) ^ 16 =
      ((Real.sqrt E) ^ 2) ^ 8 *
        (((Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt E *
          Real.sqrt (Real.sqrt D)))) ^ 2) ^ 4) ^ 2 by ring,
    Real.sq_sqrt hE,
    Real.sq_sqrt (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  rw [show ((Real.sqrt E *
      Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D))) ^ 4) ^ 2 =
      (Real.sqrt E *
        Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D))) ^ 8 by ring]
  rw [show (Real.sqrt E *
      Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D))) ^ 8 =
      ((Real.sqrt E) ^ 2) ^ 4 *
        (((Real.sqrt (Real.sqrt E * Real.sqrt (Real.sqrt D))) ^ 2) ^ 2) ^ 2 by ring,
    Real.sq_sqrt hE,
    Real.sq_sqrt (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hsquare :
      (Real.sqrt E * Real.sqrt (Real.sqrt D)) ^ 2 =
        E * Real.sqrt D := by
    rw [mul_pow, Real.sq_sqrt hE,
      Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [hsquare]
  have hlast : (E * Real.sqrt D) ^ 2 = E ^ 2 * D := by
    rw [mul_pow, Real.sq_sqrt hD]
  rw [hlast]
  ring

theorem weylTreeStepFactor_mul_succ (H L : ℕ) :
    weylTreeStepFactor H L * ((H + 1 : ℕ) : ℝ) =
      2 * ((L + (H + 1) : ℕ) : ℝ) := by
  unfold weylTreeStepFactor
  field_simp

theorem weylTreeStepFactor_mul_lag_le_six_mul_length
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylTreeStepFactor H L * (H : ℝ) ≤ 6 * (L : ℝ) := by
  have hfactor0 := weylTreeStepFactor_nonneg H L
  have hHsucc : (H : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ H
  have hfirst := mul_le_mul_of_nonneg_left hHsucc hfactor0
  rw [weylTreeStepFactor_mul_succ] at hfirst
  have hHLR : (H : ℝ) ≤ (L : ℝ) := by exact_mod_cast hHL
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  norm_num [Nat.cast_add, Nat.cast_one] at hfirst ⊢
  linarith

/-- Exact four-round sixteenth power of the scale coefficient before the
generalized harmonic factors are coarsened. -/
theorem weylLagScaleCoefficient_four_pow_sixteen_exact
    (H L : ℕ) :
    (weylLagScaleCoefficient H L 4) ^ 16 =
      (weylTreeStepFactor H L) ^ 15 *
        iteratedRootHarmonic 0 H *
        (iteratedRootHarmonic 1 H) ^ 2 *
        (iteratedRootHarmonic 2 H) ^ 4 *
        (iteratedRootHarmonic 3 H) ^ 8 := by
  let Q := weylTreeStepFactor H L
  let A := fun r => iteratedRootHarmonic r H
  let B := fun r => weylLagScaleCoefficient H L r
  have hQ : 0 ≤ Q := weylTreeStepFactor_nonneg H L
  have hA (r : ℕ) : 0 ≤ A r := iteratedRootHarmonic_nonneg r H
  have hB (r : ℕ) : 0 ≤ B r := weylLagScaleCoefficient_nonneg H L r
  have hs (r : ℕ) : (B (r + 1)) ^ 2 = Q * B r * A r := by
    dsimp only [B, Q, A]
    rw [weylLagScaleCoefficient, Real.sq_sqrt]
    exact mul_nonneg (mul_nonneg hQ (hB r)) (hA r)
  calc
    (B 4) ^ 16 = ((B 4) ^ 2) ^ 8 := by ring
    _ = (Q * B 3 * A 3) ^ 8 := by rw [show 4 = 3 + 1 by omega, hs 3]
    _ = Q ^ 8 * (B 3) ^ 8 * (A 3) ^ 8 := by ring
    _ = Q ^ 8 * ((B 3) ^ 2) ^ 4 * (A 3) ^ 8 := by ring
    _ = Q ^ 8 * (Q * B 2 * A 2) ^ 4 * (A 3) ^ 8 := by
      rw [show 3 = 2 + 1 by omega, hs 2]
    _ = Q ^ 12 * (B 2) ^ 4 * (A 2) ^ 4 * (A 3) ^ 8 := by ring
    _ = Q ^ 12 * ((B 2) ^ 2) ^ 2 * (A 2) ^ 4 * (A 3) ^ 8 := by ring
    _ = Q ^ 12 * (Q * B 1 * A 1) ^ 2 * (A 2) ^ 4 * (A 3) ^ 8 := by
      rw [show 2 = 1 + 1 by omega, hs 1]
    _ = Q ^ 14 * (B 1) ^ 2 * (A 1) ^ 2 * (A 2) ^ 4 * (A 3) ^ 8 := by ring
    _ = Q ^ 14 * (Q * B 0 * A 0) * (A 1) ^ 2 *
        (A 2) ^ 4 * (A 3) ^ 8 := by rw [show 1 = 0 + 1 by omega, hs 0]
    _ = Q ^ 15 * A 0 * (A 1) ^ 2 * (A 2) ^ 4 * (A 3) ^ 8 := by
      dsimp only [B]
      rw [weylLagScaleCoefficient]
      ring
    _ = (weylTreeStepFactor H L) ^ 15 *
        iteratedRootHarmonic 0 H *
        (iteratedRootHarmonic 1 H) ^ 2 *
        (iteratedRootHarmonic 2 H) ^ 4 *
        (iteratedRootHarmonic 3 H) ^ 8 := rfl

/-- The four generalized harmonic factors cost only `H^11` times the fourth
power of the ordinary harmonic factor. -/
theorem iteratedRootHarmonic_product_four_le (H : ℕ) :
    iteratedRootHarmonic 0 H *
        (iteratedRootHarmonic 1 H) ^ 2 *
        (iteratedRootHarmonic 2 H) ^ 4 *
        (iteratedRootHarmonic 3 H) ^ 8 ≤
      (H : ℝ) ^ 11 * (iteratedRootHarmonic 0 H) ^ 4 := by
  let A := fun r => iteratedRootHarmonic r H
  have hA (r : ℕ) : 0 ≤ A r := iteratedRootHarmonic_nonneg r H
  have h1 : (A 1) ^ 2 ≤ (H : ℝ) * A 0 := by
    simpa using iteratedRootHarmonic_succ_sq_le 0 H
  have h2 : (A 2) ^ 2 ≤ (H : ℝ) * A 1 := by
    simpa using iteratedRootHarmonic_succ_sq_le 1 H
  have h3 : (A 3) ^ 2 ≤ (H : ℝ) * A 2 := by
    simpa using iteratedRootHarmonic_succ_sq_le 2 H
  have h1pow : (A 1) ^ 6 ≤ ((H : ℝ) * A 0) ^ 3 := by
    calc
      (A 1) ^ 6 = ((A 1) ^ 2) ^ 3 := by ring
      _ ≤ ((H : ℝ) * A 0) ^ 3 := by gcongr
  have h2pow : (A 2) ^ 8 ≤ ((H : ℝ) * A 1) ^ 4 := by
    calc
      (A 2) ^ 8 = ((A 2) ^ 2) ^ 4 := by ring
      _ ≤ ((H : ℝ) * A 1) ^ 4 := by gcongr
  have h3pow : (A 3) ^ 8 ≤ ((H : ℝ) * A 2) ^ 4 := by
    calc
      (A 3) ^ 8 = ((A 3) ^ 2) ^ 4 := by ring
      _ ≤ ((H : ℝ) * A 2) ^ 4 := by gcongr
  change A 0 * A 1 ^ 2 * A 2 ^ 4 * A 3 ^ 8 ≤
    (H : ℝ) ^ 11 * A 0 ^ 4
  calc
    A 0 * A 1 ^ 2 * A 2 ^ 4 * A 3 ^ 8 ≤
        A 0 * A 1 ^ 2 * A 2 ^ 4 * (((H : ℝ) * A 2) ^ 4) := by
      exact mul_le_mul_of_nonneg_left h3pow
        (mul_nonneg (mul_nonneg (hA 0) (sq_nonneg _))
          (pow_nonneg (hA 2) 4))
    _ = (H : ℝ) ^ 4 * A 0 * A 1 ^ 2 * A 2 ^ 8 := by ring
    _ ≤ (H : ℝ) ^ 4 * A 0 * A 1 ^ 2 * (((H : ℝ) * A 1) ^ 4) := by
      exact mul_le_mul_of_nonneg_left h2pow
        (mul_nonneg (mul_nonneg (by positivity) (hA 0)) (sq_nonneg _))
    _ = (H : ℝ) ^ 8 * A 0 * A 1 ^ 6 := by ring
    _ ≤ (H : ℝ) ^ 8 * A 0 * (((H : ℝ) * A 0) ^ 3) := by
      exact mul_le_mul_of_nonneg_left h1pow
        (mul_nonneg (by positivity) (hA 0))
    _ = (H : ℝ) ^ 11 * A 0 ^ 4 := by ring

/-- Sharp four-round scale-coefficient bound retaining four powers of the
differencing range in the denominator. -/
theorem weylLagScaleCoefficient_four_power_bound_sharp
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    (weylLagScaleCoefficient H L 4) ^ 16 ≤
      (6 * (L : ℝ)) ^ 15 * (iteratedRootHarmonic 0 H) ^ 4 /
        (((H + 1 : ℕ) : ℝ) ^ 4) := by
  let Q := weylTreeStepFactor H L
  let A0 := iteratedRootHarmonic 0 H
  have hQ : 0 ≤ Q := weylTreeStepFactor_nonneg H L
  have hA0 : 0 ≤ A0 := iteratedRootHarmonic_nonneg 0 H
  have hSixL : 0 ≤ 6 * (L : ℝ) := by positivity
  have hden : 0 < (((H + 1 : ℕ) : ℝ)) := by positivity
  have hQmul : Q * (((H + 1 : ℕ) : ℝ)) ≤ 6 * (L : ℝ) := by
    rw [show Q = weylTreeStepFactor H L by rfl,
      weylTreeStepFactor_mul_succ]
    have hHLR : (H : ℝ) ≤ L := by exact_mod_cast hHL
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hQdiv : Q ≤ (6 * (L : ℝ)) / (((H + 1 : ℕ) : ℝ)) := by
    exact (le_div_iff₀ hden).2 hQmul
  have hE : Q * (H : ℝ) ≤ 6 * (L : ℝ) := by
    exact weylTreeStepFactor_mul_lag_le_six_mul_length hL hHL
  have hEpow : (Q * (H : ℝ)) ^ 11 ≤ (6 * (L : ℝ)) ^ 11 := by
    exact pow_le_pow_left₀ (mul_nonneg hQ (by positivity)) hE 11
  have hQpow : Q ^ 4 ≤
      ((6 * (L : ℝ)) / (((H + 1 : ℕ) : ℝ))) ^ 4 := by
    exact pow_le_pow_left₀ hQ hQdiv 4
  rw [weylLagScaleCoefficient_four_pow_sixteen_exact]
  calc
    Q ^ 15 * (iteratedRootHarmonic 0 H) *
        (iteratedRootHarmonic 1 H) ^ 2 *
        (iteratedRootHarmonic 2 H) ^ 4 *
        (iteratedRootHarmonic 3 H) ^ 8 ≤
      Q ^ 15 * ((H : ℝ) ^ 11 * A0 ^ 4) := by
        have hp := mul_le_mul_of_nonneg_left
          (iteratedRootHarmonic_product_four_le H)
          (pow_nonneg hQ 15)
        simpa only [A0, mul_assoc] using hp
    _ = (Q * (H : ℝ)) ^ 11 * Q ^ 4 * A0 ^ 4 := by ring
    _ ≤ (6 * (L : ℝ)) ^ 11 *
        (((6 * (L : ℝ)) / (((H + 1 : ℕ) : ℝ))) ^ 4) * A0 ^ 4 := by
      gcongr
    _ = (6 * (L : ℝ)) ^ 15 * A0 ^ 4 /
        (((H + 1 : ℕ) : ℝ) ^ 4) := by
      field_simp

theorem weylTreeStepFactor_mul_length_mul_succ_le_six_mul_sq
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    (weylTreeStepFactor H L * (L : ℝ)) * ((H + 1 : ℕ) : ℝ) ≤
      6 * (L : ℝ) ^ 2 := by
  have hHLR : (H : ℝ) ≤ (L : ℝ) := by exact_mod_cast hHL
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hsum : ((L + (H + 1) : ℕ) : ℝ) ≤ 3 * (L : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 * L by positivity)
  rw [show (weylTreeStepFactor H L * (L : ℝ)) *
      ((H + 1 : ℕ) : ℝ) =
      (2 * (L : ℝ)) * ((L + (H + 1) : ℕ) : ℝ) by
        calc
          (weylTreeStepFactor H L * (L : ℝ)) *
              ((H + 1 : ℕ) : ℝ) =
              (L : ℝ) * (weylTreeStepFactor H L *
                ((H + 1 : ℕ) : ℝ)) := by ring
          _ = (L : ℝ) * (2 * ((L + (H + 1) : ℕ) : ℝ)) := by
            rw [weylTreeStepFactor_mul_succ]
          _ = (2 * (L : ℝ)) * ((L + (H + 1) : ℕ) : ℝ) := by ring]
  nlinarith

theorem weylLagLengthTerm_zero_power_bound
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    (weylLagLengthTerm
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) 0) ^ 16 *
          (((H + 1 : ℕ) : ℝ) ^ 8) ≤
      6 ^ 8 * (L : ℝ) ^ 16 := by
  have hD0 : 0 ≤ weylTreeStepFactor H L * (L : ℝ) :=
    mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  rw [weylLagLengthTerm_zero_pow_sixteen hD0]
  have hD := weylTreeStepFactor_mul_length_mul_succ_le_six_mul_sq hL hHL
  have hDmul0 : 0 ≤ (weylTreeStepFactor H L * (L : ℝ)) *
      ((H + 1 : ℕ) : ℝ) := mul_nonneg hD0 (by positivity)
  calc
    (weylTreeStepFactor H L * (L : ℝ)) ^ 8 *
        ((H + 1 : ℕ) : ℝ) ^ 8 =
        ((weylTreeStepFactor H L * (L : ℝ)) *
          ((H + 1 : ℕ) : ℝ)) ^ 8 := by ring
    _ ≤ (6 * (L : ℝ) ^ 2) ^ 8 := by gcongr
    _ = 6 ^ 8 * (L : ℝ) ^ 16 := by ring

theorem weylLagLengthTerm_one_power_bound
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    (weylLagLengthTerm
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) 1) ^ 16 *
          (((H + 1 : ℕ) : ℝ) ^ 4) ≤
      6 ^ 12 * (L : ℝ) ^ 16 := by
  have hD0 : 0 ≤ weylTreeStepFactor H L * (L : ℝ) :=
    mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  have hE0 : 0 ≤ weylTreeStepFactor H L * (H : ℝ) :=
    mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  rw [weylLagLengthTerm_one_pow_sixteen hD0 hE0]
  have hD := weylTreeStepFactor_mul_length_mul_succ_le_six_mul_sq hL hHL
  have hE := weylTreeStepFactor_mul_lag_le_six_mul_length hL hHL
  have hDmul0 : 0 ≤ (weylTreeStepFactor H L * (L : ℝ)) *
      ((H + 1 : ℕ) : ℝ) := mul_nonneg hD0 (by positivity)
  calc
    (weylTreeStepFactor H L * (H : ℝ)) ^ 8 *
          (weylTreeStepFactor H L * (L : ℝ)) ^ 4 *
            ((H + 1 : ℕ) : ℝ) ^ 4 =
        (weylTreeStepFactor H L * (H : ℝ)) ^ 8 *
          ((weylTreeStepFactor H L * (L : ℝ)) *
            ((H + 1 : ℕ) : ℝ)) ^ 4 := by ring
    _ ≤ (6 * (L : ℝ)) ^ 8 * (6 * (L : ℝ) ^ 2) ^ 4 := by gcongr
    _ = 6 ^ 12 * (L : ℝ) ^ 16 := by ring

theorem weylLagLengthTerm_two_power_bound
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    (weylLagLengthTerm
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) 2) ^ 16 *
          (((H + 1 : ℕ) : ℝ) ^ 2) ≤
      6 ^ 14 * (L : ℝ) ^ 16 := by
  have hD0 : 0 ≤ weylTreeStepFactor H L * (L : ℝ) :=
    mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  have hE0 : 0 ≤ weylTreeStepFactor H L * (H : ℝ) :=
    mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  rw [weylLagLengthTerm_two_pow_sixteen hD0 hE0]
  have hD := weylTreeStepFactor_mul_length_mul_succ_le_six_mul_sq hL hHL
  have hE := weylTreeStepFactor_mul_lag_le_six_mul_length hL hHL
  have hDmul0 : 0 ≤ (weylTreeStepFactor H L * (L : ℝ)) *
      ((H + 1 : ℕ) : ℝ) := mul_nonneg hD0 (by positivity)
  calc
    (weylTreeStepFactor H L * (H : ℝ)) ^ 12 *
          (weylTreeStepFactor H L * (L : ℝ)) ^ 2 *
            ((H + 1 : ℕ) : ℝ) ^ 2 =
        (weylTreeStepFactor H L * (H : ℝ)) ^ 12 *
          ((weylTreeStepFactor H L * (L : ℝ)) *
            ((H + 1 : ℕ) : ℝ)) ^ 2 := by ring
    _ ≤ (6 * (L : ℝ)) ^ 12 * (6 * (L : ℝ) ^ 2) ^ 2 := by gcongr
    _ = 6 ^ 14 * (L : ℝ) ^ 16 := by ring

theorem weylLagLengthTerm_three_power_bound
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    (weylLagLengthTerm
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) 3) ^ 16 *
          ((H + 1 : ℕ) : ℝ) ≤
      6 ^ 15 * (L : ℝ) ^ 16 := by
  have hD0 : 0 ≤ weylTreeStepFactor H L * (L : ℝ) :=
    mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  have hE0 : 0 ≤ weylTreeStepFactor H L * (H : ℝ) :=
    mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity)
  rw [weylLagLengthTerm_three_pow_sixteen hD0 hE0]
  have hD := weylTreeStepFactor_mul_length_mul_succ_le_six_mul_sq hL hHL
  have hE := weylTreeStepFactor_mul_lag_le_six_mul_length hL hHL
  have hDmul0 : 0 ≤ (weylTreeStepFactor H L * (L : ℝ)) *
      ((H + 1 : ℕ) : ℝ) := mul_nonneg hD0 (by positivity)
  calc
    (weylTreeStepFactor H L * (H : ℝ)) ^ 14 *
          (weylTreeStepFactor H L * (L : ℝ)) *
            ((H + 1 : ℕ) : ℝ) =
        (weylTreeStepFactor H L * (H : ℝ)) ^ 14 *
          ((weylTreeStepFactor H L * (L : ℝ)) *
            ((H + 1 : ℕ) : ℝ)) := by ring
    _ ≤ (6 * (L : ℝ)) ^ 14 * (6 * (L : ℝ) ^ 2) := by gcongr
    _ = 6 ^ 15 * (L : ℝ) ^ 16 := by ring

theorem le_iteratedSqrt_four_div_of_pow_mul_le
    {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hpow : x ^ 16 * B ≤ A) :
    x ≤ iteratedSqrt 4 (A / B) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0)
    (iteratedSqrt_nonneg (div_nonneg hA hB.le) 4)
  rw [iteratedSqrt_four_pow_sixteen (div_nonneg hA hB.le)]
  exact (le_div_iff₀ hB).2 hpow

theorem weylLagLengthTerm_zero_root_bound
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylLagLengthTerm
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) 0 ≤
      iteratedSqrt 4
        ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) := by
  apply le_iteratedSqrt_four_div_of_pow_mul_le (by positivity) (by positivity)
  exact weylLagLengthTerm_zero_power_bound hL hHL

theorem weylLagLengthTerm_one_root_bound
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylLagLengthTerm
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) 1 ≤
      iteratedSqrt 4
        ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) := by
  apply le_iteratedSqrt_four_div_of_pow_mul_le (by positivity) (by positivity)
  exact weylLagLengthTerm_one_power_bound hL hHL

theorem weylLagLengthTerm_two_root_bound
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylLagLengthTerm
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) 2 ≤
      iteratedSqrt 4
        ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) := by
  apply le_iteratedSqrt_four_div_of_pow_mul_le (by positivity) (by positivity)
  exact weylLagLengthTerm_two_power_bound hL hHL

theorem weylLagLengthTerm_three_root_bound
    {H L : ℕ} (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylLagLengthTerm
        (weylTreeStepFactor H L * (L : ℝ))
        (weylTreeStepFactor H L * (H : ℝ)) 3 ≤
      iteratedSqrt 4
        ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) := by
  apply le_iteratedSqrt_four_div_of_pow_mul_le (by positivity) (by positivity)
  exact weylLagLengthTerm_three_power_bound hL hHL

theorem weylLagScaleTerm_four_power_bound
    {scale : ℝ} (hscale : 0 < scale) {H L : ℕ}
    (hL : 1 ≤ L) (hHL : H ≤ L) :
    (weylLagScaleCoarseCoefficient H L 4 *
        iteratedSqrt 4 (1 / scale)) ^ 16 ≤
      (6 * (L : ℝ)) ^ 15 / scale := by
  rw [weylLagScaleTerm_four_pow_sixteen hscale]
  calc
    (weylTreeStepFactor H L * (H : ℝ)) ^ 15 * (1 / scale) =
        (weylTreeStepFactor H L * (H : ℝ)) ^ 15 / scale := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (6 * (L : ℝ)) ^ 15 / scale := by
      apply div_le_div_of_nonneg_right _ hscale.le
      exact pow_le_pow_left₀
        (mul_nonneg (weylTreeStepFactor_nonneg H L) (by positivity))
        (weylTreeStepFactor_mul_lag_le_six_mul_length hL hHL) 15

theorem weylLagScaleTerm_four_root_bound
    {scale : ℝ} (hscale : 0 < scale) {H L : ℕ}
    (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylLagScaleCoarseCoefficient H L 4 *
        iteratedSqrt 4 (1 / scale) ≤
      iteratedSqrt 4 ((6 * (L : ℝ)) ^ 15 / scale) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0)
    (iteratedSqrt_nonneg (div_nonneg (by positivity) hscale.le) 4)
  rw [iteratedSqrt_four_pow_sixteen (div_nonneg (by positivity) hscale.le)]
  exact weylLagScaleTerm_four_power_bound hscale hL hHL

/-- Sharp scale-term sixteenth-power estimate obtained from the exact
generalized harmonic factors. -/
theorem weylLagScaleTerm_four_power_bound_sharp
    {scale : ℝ} (hscale : 0 < scale) {H L : ℕ}
    (hL : 1 ≤ L) (hHL : H ≤ L) :
    (weylLagScaleCoefficient H L 4 *
        iteratedSqrt 4 (1 / scale)) ^ 16 ≤
      (6 * (L : ℝ)) ^ 15 * (iteratedRootHarmonic 0 H) ^ 4 /
        ((((H + 1 : ℕ) : ℝ) ^ 4) * scale) := by
  rw [mul_pow, iteratedSqrt_four_pow_sixteen (by positivity)]
  calc
    (weylLagScaleCoefficient H L 4) ^ 16 * (1 / scale) ≤
        ((6 * (L : ℝ)) ^ 15 * (iteratedRootHarmonic 0 H) ^ 4 /
          (((H + 1 : ℕ) : ℝ) ^ 4)) * (1 / scale) := by
      apply mul_le_mul_of_nonneg_right
        (weylLagScaleCoefficient_four_power_bound_sharp hL hHL)
      positivity
    _ = (6 * (L : ℝ)) ^ 15 * (iteratedRootHarmonic 0 H) ^ 4 /
        ((((H + 1 : ℕ) : ℝ) ^ 4) * scale) := by ring

theorem weylLagScaleTerm_four_root_bound_sharp
    {scale : ℝ} (hscale : 0 < scale) {H L : ℕ}
    (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylLagScaleCoefficient H L 4 * iteratedSqrt 4 (1 / scale) ≤
      iteratedSqrt 4
        ((6 * (L : ℝ)) ^ 15 * (iteratedRootHarmonic 0 H) ^ 4 /
          ((((H + 1 : ℕ) : ℝ) ^ 4) * scale)) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0)
    (iteratedSqrt_nonneg (by positivity) 4)
  rw [iteratedSqrt_four_pow_sixteen (by positivity)]
  exact weylLagScaleTerm_four_power_bound_sharp hscale hL hHL

/-- Fully root-extracted four-round scalar majorant. -/
def weylLagFourRootMajorant (H L : ℕ) (scale : ℝ) : ℝ :=
  iteratedSqrt 4
      ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) +
    iteratedSqrt 4
      ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) +
    iteratedSqrt 4
      ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) +
    iteratedSqrt 4
      ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) +
    iteratedSqrt 4 ((6 * (L : ℝ)) ^ 15 / scale)

theorem weylLagFourRootMajorant_nonneg (H L : ℕ) {scale : ℝ}
    (hscale : 0 < scale) :
    0 ≤ weylLagFourRootMajorant H L scale := by
  unfold weylLagFourRootMajorant
  repeat' apply add_nonneg
  all_goals
    apply iteratedSqrt_nonneg
    positivity

/-- Four-round root majorant retaining the exact harmonic gain in the
scale-dependent term. -/
noncomputable def weylLagFourSharpRootMajorant
    (H L : ℕ) (scale : ℝ) : ℝ :=
  iteratedSqrt 4
      ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) +
    iteratedSqrt 4
      ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) +
    iteratedSqrt 4
      ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) +
    iteratedSqrt 4
      ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) +
    iteratedSqrt 4
      ((6 * (L : ℝ)) ^ 15 * (iteratedRootHarmonic 0 H) ^ 4 /
        ((((H + 1 : ℕ) : ℝ) ^ 4) * scale))

/-- Source-readable version of the sharp majorant, with its sole harmonic
factor replaced by `1 + log H`. -/
noncomputable def weylLagFourLogRootMajorant
    (H L : ℕ) (scale : ℝ) : ℝ :=
  iteratedSqrt 4
      ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) +
    iteratedSqrt 4
      ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) +
    iteratedSqrt 4
      ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) +
    iteratedSqrt 4
      ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) +
    iteratedSqrt 4
      ((6 * (L : ℝ)) ^ 15 * (1 + Real.log H) ^ 4 /
        ((((H + 1 : ℕ) : ℝ) ^ 4) * scale))

theorem weylLagFourSharpRootMajorant_nonneg
    (H L : ℕ) {scale : ℝ} (hscale : 0 < scale) :
    0 ≤ weylLagFourSharpRootMajorant H L scale := by
  unfold weylLagFourSharpRootMajorant
  repeat' apply add_nonneg
  all_goals
    apply iteratedSqrt_nonneg
    positivity

theorem weylLagClosedMajorant_four_le_sharpRootMajorant
    {scale : ℝ} (hscale : 0 < scale) {H L : ℕ}
    (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylLagClosedMajorant H L 4 scale [] ≤
      weylLagFourSharpRootMajorant H L scale := by
  unfold weylLagClosedMajorant
  simp only [List.prod_nil, Nat.cast_one, one_mul]
  calc
    weylLagLengthCoefficient H L 4 +
        weylLagScaleCoefficient H L 4 * iteratedSqrt 4 (1 / scale) ≤
      weylLagLengthFourMajorant H L +
        weylLagScaleCoefficient H L 4 * iteratedSqrt 4 (1 / scale) := by
      gcongr
      exact weylLagLengthCoefficient_four_le H L
    _ ≤ weylLagFourSharpRootMajorant H L scale := by
      rw [weylLagLengthFourMajorant_eq_sum_terms]
      unfold weylLagFourSharpRootMajorant
      gcongr
      · exact weylLagLengthTerm_zero_root_bound hL hHL
      · exact weylLagLengthTerm_one_root_bound hL hHL
      · exact weylLagLengthTerm_two_root_bound hL hHL
      · exact weylLagLengthTerm_three_root_bound hL hHL
      · exact weylLagScaleTerm_four_root_bound_sharp hscale hL hHL

theorem weylLagFourSharpRootMajorant_mono_length
    (H : ℕ) {L K : ℕ} (hLK : L ≤ K) {scale : ℝ} (hscale : 0 < scale) :
    weylLagFourSharpRootMajorant H L scale ≤
      weylLagFourSharpRootMajorant H K scale := by
  unfold weylLagFourSharpRootMajorant
  repeat' apply add_le_add
  all_goals
    apply iteratedSqrt_mono
    apply div_le_div_of_nonneg_right
    · gcongr
    · positivity

theorem weylLagFourSharpRootMajorant_le_logRootMajorant
    (H L : ℕ) {scale : ℝ} (hscale : 0 < scale) :
    weylLagFourSharpRootMajorant H L scale ≤
      weylLagFourLogRootMajorant H L scale := by
  unfold weylLagFourSharpRootMajorant weylLagFourLogRootMajorant
  apply add_le_add_right
  apply iteratedSqrt_mono
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (iteratedRootHarmonic_nonneg 0 H)
    (iteratedRootHarmonic_zero_le_one_add_log H) 4

theorem weylLagFourRootMajorant_mono_length
    (H : ℕ) {L K : ℕ} (hLK : L ≤ K) {scale : ℝ} (hscale : 0 < scale) :
    weylLagFourRootMajorant H L scale ≤
      weylLagFourRootMajorant H K scale := by
  unfold weylLagFourRootMajorant
  repeat' apply add_le_add
  all_goals
    apply iteratedSqrt_mono
    apply div_le_div_of_nonneg_right
    · gcongr
    · positivity

theorem weylLagLengthFourMajorant_add_scale_le_rootMajorant
    {scale : ℝ} (hscale : 0 < scale) {H L : ℕ}
    (hL : 1 ≤ L) (hHL : H ≤ L) :
    weylLagLengthFourMajorant H L +
        weylLagScaleCoarseCoefficient H L 4 *
          iteratedSqrt 4 (1 / scale) ≤
      weylLagFourRootMajorant H L scale := by
  rw [weylLagLengthFourMajorant_eq_sum_terms]
  unfold weylLagFourRootMajorant
  gcongr
  · exact weylLagLengthTerm_zero_root_bound hL hHL
  · exact weylLagLengthTerm_one_root_bound hL hHL
  · exact weylLagLengthTerm_two_root_bound hL hHL
  · exact weylLagLengthTerm_three_root_bound hL hHL
  · exact weylLagScaleTerm_four_root_bound hscale hL hHL

/-- Four nested square roots are exactly a real sixteenth power. -/
theorem iteratedSqrt_four_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    iteratedSqrt 4 x = x ^ (1 / 16 : ℝ) := by
  change Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt x))) = _
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hx]
  rw [← Real.rpow_mul hx]
  rw [← Real.rpow_mul hx]
  norm_num

/-- The root-extracted four-round majorant in conventional `1/16`-power
notation. -/
theorem weylLagFourRootMajorant_eq_rpow
    (H L : ℕ) {scale : ℝ} (hscale : 0 < scale) :
    weylLagFourRootMajorant H L scale =
      ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) ^ (1 / 16 : ℝ) +
      ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) ^ (1 / 16 : ℝ) +
      ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) ^ (1 / 16 : ℝ) +
      ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) ^ (1 / 16 : ℝ) +
      (((6 * (L : ℝ)) ^ 15 / scale) ^ (1 / 16 : ℝ)) := by
  unfold weylLagFourRootMajorant
  rw [iteratedSqrt_four_eq_rpow (by positivity),
    iteratedSqrt_four_eq_rpow (by positivity),
    iteratedSqrt_four_eq_rpow (by positivity),
    iteratedSqrt_four_eq_rpow (by positivity),
    iteratedSqrt_four_eq_rpow (div_nonneg (by positivity) hscale.le)]

/-- Natural differencing range obtained by rounding down the positive real
fourth root of `1 / (2u)`. -/
noncomputable def fourthRootFloor (u : ℝ) : ℕ :=
  ⌊Real.sqrt (Real.sqrt (1 / (2 * u)))⌋₊

theorem fourthRootFloor_range {u : ℝ} (hu : 0 < u) :
    2 * ((fourthRootFloor u ^ 4 : ℕ) : ℝ) * u ≤ 1 := by
  have hx : 0 ≤ 1 / (2 * u) := by positivity
  have hs : 0 ≤ Real.sqrt (1 / (2 * u)) := Real.sqrt_nonneg _
  have hfloor :
      ((fourthRootFloor u : ℕ) : ℝ) ≤
        Real.sqrt (Real.sqrt (1 / (2 * u))) := by
    exact Nat.floor_le (Real.sqrt_nonneg _)
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ _) hfloor 4
  have hroot :
      (Real.sqrt (Real.sqrt (1 / (2 * u)))) ^ 4 = 1 / (2 * u) := by
    calc
      (Real.sqrt (Real.sqrt (1 / (2 * u)))) ^ 4 =
          (Real.sqrt (Real.sqrt (1 / (2 * u))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (1 / (2 * u))) ^ 2 := by rw [Real.sq_sqrt hs]
      _ = 1 / (2 * u) := Real.sq_sqrt hx
  rw [hroot] at hp
  have hpcast : ((fourthRootFloor u ^ 4 : ℕ) : ℝ) ≤ 1 / (2 * u) := by
    norm_num only [Nat.cast_pow]
    exact hp
  calc
    2 * ((fourthRootFloor u ^ 4 : ℕ) : ℝ) * u ≤
        2 * (1 / (2 * u)) * u := by gcongr
    _ = 1 := by field_simp

theorem fourthRootFloor_add_one_gt {u : ℝ} :
    Real.sqrt (Real.sqrt (1 / (2 * u))) <
      ((fourthRootFloor u + 1 : ℕ) : ℝ) := by
  simpa [fourthRootFloor] using
    (Nat.lt_floor_add_one (Real.sqrt (Real.sqrt (1 / (2 * u)))))

theorem one_div_fourthRootFloor_add_one_pow_four_le
    {u : ℝ} (hu : 0 < u) :
    1 / ((((fourthRootFloor u) + 1 : ℕ) : ℝ) ^ 4) ≤ 2 * u := by
  have hroot := fourthRootFloor_add_one_gt (u := u)
  have hrootNonneg :
      0 ≤ Real.sqrt (Real.sqrt (1 / (2 * u))) := Real.sqrt_nonneg _
  have hpow := pow_lt_pow_left₀ hroot hrootNonneg (by omega : (4 : ℕ) ≠ 0)
  have hs : 0 ≤ Real.sqrt (1 / (2 * u)) := Real.sqrt_nonneg _
  have hx : 0 ≤ 1 / (2 * u) := by positivity
  have hrootPow :
      (Real.sqrt (Real.sqrt (1 / (2 * u)))) ^ 4 = 1 / (2 * u) := by
    calc
      (Real.sqrt (Real.sqrt (1 / (2 * u)))) ^ 4 =
          (Real.sqrt (Real.sqrt (1 / (2 * u))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (1 / (2 * u))) ^ 2 := by rw [Real.sq_sqrt hs]
      _ = 1 / (2 * u) := Real.sq_sqrt hx
  rw [hrootPow] at hpow
  have hproduct :
      1 ≤ 2 * u * ((((fourthRootFloor u) + 1 : ℕ) : ℝ) ^ 4) := by
    have := (div_lt_iff₀ (by positivity : 0 < 2 * u)).1 hpow
    nlinarith
  exact (div_le_iff₀
    (by positivity : 0 < ((((fourthRootFloor u) + 1 : ℕ) : ℝ) ^ 4))).2
      (by nlinarith)

theorem fourthRootFloor_pos {u : ℝ} (hu : 0 < u) (huSmall : 2 * u ≤ 1) :
    0 < fourthRootFloor u := by
  rw [fourthRootFloor, Nat.floor_pos]
  apply Real.one_le_sqrt.mpr
  apply Real.one_le_sqrt.mpr
  exact (le_div_iff₀ (by positivity : 0 < 2 * u)).2 (by nlinarith)

theorem fourthRootFloor_le {u : ℝ} {L : ℕ}
    (hfit : 1 / (2 * u) < (((L + 1 : ℕ) : ℝ) ^ 4)) :
    fourthRootFloor u ≤ L := by
  have hroot : Real.sqrt (Real.sqrt (1 / (2 * u))) < ((L + 1 : ℕ) : ℝ) := by
    apply (Real.sqrt_lt' (by positivity)).2
    apply (Real.sqrt_lt' (by positivity)).2
    calc
      1 / (2 * u) < (((L + 1 : ℕ) : ℝ) ^ 4) := hfit
      _ = ((((L + 1 : ℕ) : ℝ) ^ 2) ^ 2) := by ring
  have hfloor : fourthRootFloor u < L + 1 := by
    rw [fourthRootFloor, Nat.floor_lt (Real.sqrt_nonneg _)]
    exact hroot
  omega

/-- Raw upper derivative scale entering the four-round finite-difference
smallness condition. -/
noncomputable def reciprocalPhaseFourStepUpperScale
    (N M : ℝ) (j : ℕ) (X : ℝ) : ℝ :=
  (Nat.factorial 5 : ℝ) *
    (((((5 + j) ^ 5 : ℕ) : ℝ) * reciprocalPhaseScale N M j X) / X ^ 5)

/-- Critical-regular lower derivative scale used at the terminal fifth
derivative test. -/
noncomputable def reciprocalPhaseFourStepLowerScale
    (N M : ℝ) (j : ℕ) (X q : ℝ) : ℝ :=
  (Nat.factorial 5 : ℝ) *
    (reciprocalPhaseScale N M j X * q / 10) / (2 * X) ^ 5

/-- Exact dimensionless normalization of the terminal lower fifth-derivative
scale.  This exposes the `Fq/X^5` quantity used in the source optimization. -/
theorem reciprocalPhaseFourStepLowerScale_eq
    (N M : ℝ) (j : ℕ) {X q : ℝ} (hX : X ≠ 0) :
    reciprocalPhaseFourStepLowerScale N M j X q =
      3 * reciprocalPhaseScale N M j X * q / (8 * X ^ 5) := by
  unfold reciprocalPhaseFourStepLowerScale
  norm_num [Nat.factorial]
  field_simp [hX]
  ring

/-- Exact dimensionless normalization of the upper fifth-derivative scale. -/
theorem reciprocalPhaseFourStepUpperScale_eq
    (N M : ℝ) (j : ℕ) (X : ℝ) :
    reciprocalPhaseFourStepUpperScale N M j X =
      120 * (((5 + j) ^ 5 : ℕ) : ℝ) *
        reciprocalPhaseScale N M j X / X ^ 5 := by
  unfold reciprocalPhaseFourStepUpperScale
  norm_num [Nat.factorial]
  ring

theorem reciprocalPhaseFourStepUpperScale_pos
    (N M : ℝ) {j : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    0 < reciprocalPhaseFourStepUpperScale N M j X := by
  unfold reciprocalPhaseFourStepUpperScale
  positivity

theorem reciprocalPhaseFourStepLowerScale_le_upperScale
    (N M : ℝ) {j : ℕ} {X q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hqOne : q ≤ 1) :
    reciprocalPhaseFourStepLowerScale N M j X q ≤
      reciprocalPhaseFourStepUpperScale N M j X := by
  unfold reciprocalPhaseFourStepLowerScale reciprocalPhaseFourStepUpperScale
  norm_num [Nat.factorial]
  field_simp
  have hjpowNat : 1 ≤ (5 + j) ^ 5 := by
    exact one_le_pow₀ (by omega : 1 ≤ 5 + j)
  have hjpow : (1 : ℝ) ≤ (5 + (j : ℝ)) ^ 5 := by
    exact_mod_cast hjpowNat
  nlinarith

/-- Canonical natural four-round differencing range for the reciprocal phase.
-/
noncomputable def reciprocalPhaseFourStepRange
    (N M : ℝ) (j : ℕ) (X : ℝ) : ℕ :=
  fourthRootFloor (reciprocalPhaseFourStepUpperScale N M j X)

/-- The canonical differencing range automatically discharges the terminal
upper-smallness inequality. -/
theorem reciprocalPhaseFourStepRange_upperSmall
    (N M : ℝ) {j : ℕ} {X q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hqOne : q ≤ 1) :
    (((reciprocalPhaseFourStepRange N M j X) ^ 4 : ℕ) : ℝ) *
        reciprocalPhaseFourStepUpperScale N M j X ≤
      1 - (((reciprocalPhaseFourStepRange N M j X) ^ 4 : ℕ) : ℝ) *
        reciprocalPhaseFourStepLowerScale N M j X q := by
  have hlower := reciprocalPhaseFourStepLowerScale_le_upperScale
    N M hX hF hqOne
  have hH : 0 ≤
      (((reciprocalPhaseFourStepRange N M j X) ^ 4 : ℕ) : ℝ) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hlower hH
  have hrange := fourthRootFloor_range
    (reciprocalPhaseFourStepUpperScale_pos N M hX hF)
  unfold reciprocalPhaseFourStepRange at hrange ⊢
  nlinarith

theorem reciprocalPhaseFourStepRange_pos
    (N M : ℝ) {j : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hsmall : 2 * reciprocalPhaseFourStepUpperScale N M j X ≤ 1) :
    0 < reciprocalPhaseFourStepRange N M j X := by
  unfold reciprocalPhaseFourStepRange
  exact fourthRootFloor_pos
    (reciprocalPhaseFourStepUpperScale_pos N M hX hF) hsmall

theorem reciprocalPhaseFourStepRange_le
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hfit : 1 / (2 * reciprocalPhaseFourStepUpperScale N M j X) <
      (((L + 1 : ℕ) : ℝ) ^ 4)) :
    reciprocalPhaseFourStepRange N M j X ≤ L := by
  unfold reciprocalPhaseFourStepRange
  exact fourthRootFloor_le hfit






/-- Lag-sensitive form of the critical-regular reciprocal-phase terminal
estimate.  Every leaf keeps `min(L, 1/(prod(ds)*scale))`, rather than replacing
the lag product by one before the Weyl tree is summed. -/
theorem terminalLagSensitiveBound_reciprocalPhase_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (r a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (r * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrOne : 1 + r ∈ orders) (hrTwo : 2 + r ∈ orders)
    (hupperSmall :
      ((H ^ r : ℕ) : ℝ) *
          (((1 + r).factorial : ℝ) *
              (((((1 + r) + j) ^ (1 + r) : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) /
            X ^ (1 + r)) ≤
        1 - ((H ^ r : ℕ) : ℝ) *
          (((1 + r).factorial : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (1 + r))) :
    ∀ ds : List ℕ, ds.length = r → AdmissibleWeylLags H ds →
      ∀ L ≤ b - a,
        ‖phaseExponentialSum
          (iteratedForwardPhaseDifference
            (fun n => reciprocalPhase N M j (a + n)) ds) L‖ ≤
          lagProductTerminalMajorant
            (((1 + r).factorial : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
                (2 * X) ^ (1 + r)) ds L := by
  intro ds hlen hadmissible L hLN
  have hprodPos : 0 < ds.prod :=
    prod_pos_of_admissibleWeylLags hadmissible
  have hsum : ds.sum ≤ r * H := by
    simpa only [hlen] using
      sum_le_length_mul_of_admissibleWeylLags hadmissible
  have hprodLe : ds.prod ≤ H ^ r := by
    simpa only [hlen] using
      prod_le_pow_length_of_admissibleWeylLags hadmissible
  have hendpoint :
      (a : ℝ) + (L : ℝ) + (ds.sum : ℝ) ≤
        (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) := by
    have hLR : (L : ℝ) ≤ (b - a : ℕ) := by exact_mod_cast hLN
    have hsumR : (ds.sum : ℝ) ≤ (r * H : ℕ) := by exact_mod_cast hsum
    linarith
  have hprodLeR : (ds.prod : ℝ) ≤ (H ^ r : ℕ) := by
    exact_mod_cast hprodLe
  let A : ℝ := ((1 + r).factorial : ℝ) *
    (reciprocalPhaseScale N M j X * q / 10) /
      (2 * X) ^ (1 + r)
  let B : ℝ := ((1 + r).factorial : ℝ) *
    (((((1 + r) + j) ^ (1 + r) : ℕ) : ℝ) *
      reciprocalPhaseScale N M j X) /
        X ^ (1 + r)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hupperSmallDs : (ds.prod : ℝ) * B ≤ 1 - (ds.prod : ℝ) * A := by
    calc
      (ds.prod : ℝ) * B ≤ ((H ^ r : ℕ) : ℝ) * B :=
        mul_le_mul_of_nonneg_right hprodLeR hB
      _ ≤ 1 - ((H ^ r : ℕ) : ℝ) * A := by
        simpa only [A, B] using hupperSmall
      _ ≤ 1 - (ds.prod : ℝ) * A := by
        have := mul_le_mul_of_nonneg_right hprodLeR hA.le
        linarith
  rw [lagProductTerminalMajorant, le_min_iff]
  constructor
  · exact norm_phaseExponentialSum_le _ L
  · have hterminal :=
      norm_iteratedReciprocalPhaseExponentialSum_le_inv_regularScale
        N M orders ds (X := X) (Y := Y) (q := q) (a := (a : ℝ)) L
        hX hF hq hqOne hj hprodPos haIcc
        (hendpoint.trans hevalY) (hendpoint.trans hevalTop)
        (by
          intro y hy
          exact hregular y ⟨hy.1, hy.2.trans hendpoint⟩)
        (by simpa only [hlen] using hrOne)
        (by simpa only [hlen] using hrTwo)
        (by simpa only [hlen, A, B] using hupperSmallDs)
    calc
      ‖phaseExponentialSum
          (iteratedForwardPhaseDifference
            (fun n => reciprocalPhase N M j (a + n)) ds) L‖ =
          ‖phaseExponentialSum
            (iteratedForwardPhaseDifference
              (fun n => reciprocalPhase N M j ((a : ℝ) + n)) ds) L‖ := by
            congr 4
      _ ≤ 1 / ((ds.prod : ℝ) * A) := by
        simpa only [hlen, A] using hterminal
      _ = 1 / ((ds.prod : ℝ) *
          (((1 + r).factorial : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
              (2 * X) ^ (1 + r))) := rfl

/-- Critical-regular reciprocal-phase estimate through the exact
lag-sensitive Weyl tree.  This retains the individual product at every leaf
for the subsequent harmonic-sum and differencing-range optimization. -/
theorem norm_reciprocalPhaseSum_le_weylTreeMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (r a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (r * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (r * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrOne : 1 + r ∈ orders) (hrTwo : 2 + r ∈ orders)
    (hupperSmall :
      ((H ^ r : ℕ) : ℝ) *
          (((1 + r).factorial : ℝ) *
              (((((1 + r) + j) ^ (1 + r) : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) /
            X ^ (1 + r)) ≤
        1 - ((H ^ r : ℕ) : ℝ) *
          (((1 + r).factorial : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ (1 + r))) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylTreeMajorant H
        (lagProductTerminalMajorant
          (((1 + r).factorial : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
              (2 * X) ^ (1 + r))) r [] (b - a) := by
  rw [reciprocalPhaseSum_eq_phaseExponentialSum_translate]
  apply norm_phaseExponentialSum_le_weylTreeMajorant
  · intro ds L
    apply lagProductTerminalMajorant_nonneg
    positivity
  · exact terminalLagSensitiveBound_reciprocalPhase_regularScale
      N M orders r a b H hX hF hq hqOne hj haIcc hevalY hevalTop
      hregular hrOne hrTwo hupperSmall

/-- Literal four-round lag-sensitive Weyl tree for the source's degree-five
critical-regular branch. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylTreeMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (4 * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (((((5 + j) ^ 5 : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) / X ^ 5)) ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylTreeMajorant H
        (lagProductTerminalMajorant
          ((Nat.factorial 5 : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
              (2 * X) ^ 5)) 4 [] (b - a) := by
  apply norm_reciprocalPhaseSum_le_weylTreeMajorant_regularScale
    N M orders 4 a b H hX hF hq hqOne hj haIcc hevalY hevalTop
    hregular hrFive hrSix
  norm_num at hupperSmall ⊢
  convert hupperSmall using 1
  ring

/-- Closed four-round source estimate obtained by summing every lag-sensitive
branch.  The scale-dependent term has undergone four exact square-root
iterations, so it records the characteristic sixteenth-root dependence of the
degree-five Weyl argument. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagClosedMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (4 * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (((((5 + j) ^ 5 : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) / X ^ 5)) ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylLagClosedMajorant H (b - a) 4
        ((Nat.factorial 5 : ℝ) *
          (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5) [] := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeylTreeMajorant_regularScale
    N M orders a b H hX hF hq hqOne hj haIcc hevalY hevalTop hregular
      hrFive hrSix hupperSmall).trans ?_
  exact weylTreeMajorant_lagProduct_le_closed (by positivity) [] (by simp)
    H (b - a) 4 (b - a) le_rfl

/-- Four-round reciprocal-phase estimate after replacing every generalized
harmonic factor by `H`.  The remaining length coefficient is independent of
the reciprocal derivative scale, while the second summand has the exact
sixteenth-power identity proved by `weylLagScaleTerm_four_pow_sixteen`. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagCoarseMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (4 * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (((((5 + j) ^ 5 : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) / X ^ 5)) ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylLagLengthCoefficient H (b - a) 4 +
        weylLagScaleCoarseCoefficient H (b - a) 4 *
          iteratedSqrt 4
            (1 / ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
                (2 * X) ^ 5)) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeylLagClosedMajorant_regularScale
    N M orders a b H hX hF hq hqOne hj haIcc hevalY hevalTop hregular
      hrFive hrSix hupperSmall).trans ?_
  simpa only [List.prod_nil, Nat.cast_one, one_mul] using
    (weylLagClosedMajorant_le_coarseScale
      (by positivity : 0 < (Nat.factorial 5 : ℝ) *
        (reciprocalPhaseScale N M j X * q / 10) / (2 * X) ^ 5)
      [] (by simp) H (b - a) 4)

/-- Source-facing four-round estimate with the diagonal recurrence completely
split into its four explicit nonnegative Weyl terms.  Their individual
sixteenth powers are given by the `weylLagLengthTerm_*_pow_sixteen` theorems. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagExpandedMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (4 * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (((((5 + j) ^ 5 : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) / X ^ 5)) ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylLagLengthFourMajorant H (b - a) +
        weylLagScaleCoarseCoefficient H (b - a) 4 *
          iteratedSqrt 4
            (1 / ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
                (2 * X) ^ 5)) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeylLagCoarseMajorant_regularScale
    N M orders a b H hX hF hq hqOne hj haIcc hevalY hevalTop hregular
      hrFive hrSix hupperSmall).trans ?_
  exact add_le_add_left (weylLagLengthCoefficient_four_le H (b - a)) _

/-- Fully root-extracted source estimate.  The right side is the explicit sum
of the four diagonal sixteenth roots and the inverse-derivative-scale
sixteenth root. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagRootMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hLength : 1 ≤ b - a) (hHL : H ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (4 * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (((((5 + j) ^ 5 : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) / X ^ 5)) ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylLagFourRootMajorant H (b - a)
        ((Nat.factorial 5 : ℝ) *
          (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeylLagExpandedMajorant_regularScale
    N M orders a b H hX hF hq hqOne hj haIcc hevalY hevalTop hregular
      hrFive hrSix hupperSmall).trans ?_
  exact weylLagLengthFourMajorant_add_scale_le_rootMajorant
    (by positivity) hLength hHL

/-- Root-extracted four-round source estimate retaining the generalized
harmonic gain in its inverse-scale term. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagSharpRootMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hLength : 1 ≤ b - a) (hHL : H ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (4 * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (((((5 + j) ^ 5 : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) / X ^ 5)) ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylLagFourSharpRootMajorant H (b - a)
        (reciprocalPhaseFourStepLowerScale N M j X q) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeylLagClosedMajorant_regularScale
    N M orders a b H hX hF hq hqOne hj haIcc hevalY hevalTop hregular
      hrFive hrSix hupperSmall).trans ?_
  exact weylLagClosedMajorant_four_le_sharpRootMajorant
    (by positivity) hLength hHL

/-- Source-facing four-round Weyl estimate with all five summands displayed
as conventional real sixteenth powers. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagRpowMajorant_regularScale
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hLength : 1 ≤ b - a) (hHL : H ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) + (4 * H : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) + (4 * H : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (((((5 + j) ^ 5 : ℕ) : ℝ) *
                reciprocalPhaseScale N M j X) / X ^ 5)) ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          ((Nat.factorial 5 : ℝ) *
              (reciprocalPhaseScale N M j X * q / 10) /
            (2 * X) ^ 5)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((6 ^ 8 * ((b - a : ℕ) : ℝ) ^ 16) /
          (((H + 1 : ℕ) : ℝ) ^ 8)) ^ (1 / 16 : ℝ) +
      ((6 ^ 12 * ((b - a : ℕ) : ℝ) ^ 16) /
          (((H + 1 : ℕ) : ℝ) ^ 4)) ^ (1 / 16 : ℝ) +
      ((6 ^ 14 * ((b - a : ℕ) : ℝ) ^ 16) /
          (((H + 1 : ℕ) : ℝ) ^ 2)) ^ (1 / 16 : ℝ) +
      ((6 ^ 15 * ((b - a : ℕ) : ℝ) ^ 16) /
          ((H + 1 : ℕ) : ℝ)) ^ (1 / 16 : ℝ) +
      (((6 * ((b - a : ℕ) : ℝ)) ^ 15 /
          ((Nat.factorial 5 : ℝ) *
            (reciprocalPhaseScale N M j X * q / 10) /
              (2 * X) ^ 5)) ^ (1 / 16 : ℝ)) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeylLagRootMajorant_regularScale
    N M orders a b H hX hF hq hqOne hj hLength hHL haIcc hevalY hevalTop
      hregular hrFive hrSix hupperSmall).trans_eq ?_
  exact weylLagFourRootMajorant_eq_rpow H (b - a) (by positivity)

/-- The source-facing four-round bound at the canonical floor-rounded
differencing range.  Its terminal upper-smallness condition is discharged
internally; only interval admissibility of the chosen range remains. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagRootMajorant_canonicalRange
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hLength : 1 ≤ b - a)
    (hHL : reciprocalPhaseFourStepRange N M j X ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepRange N M j X : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepRange N M j X : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) +
          (4 * reciprocalPhaseFourStepRange N M j X : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylLagFourRootMajorant
        (reciprocalPhaseFourStepRange N M j X) (b - a)
        (reciprocalPhaseFourStepLowerScale N M j X q) := by
  apply norm_reciprocalPhaseSum_le_fourStepWeylLagRootMajorant_regularScale
    N M orders a b (reciprocalPhaseFourStepRange N M j X)
      hX hF hq hqOne hj hLength hHL haIcc hevalY hevalTop hregular
      hrFive hrSix
  simpa [reciprocalPhaseFourStepUpperScale,
    reciprocalPhaseFourStepLowerScale] using
      (reciprocalPhaseFourStepRange_upperSmall N M hX hF hqOne)

/-- Canonical floor-rounded source estimate with the sharp harmonic scale
term. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagSharpRootMajorant_canonicalRange
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hLength : 1 ≤ b - a)
    (hHL : reciprocalPhaseFourStepRange N M j X ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepRange N M j X : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepRange N M j X : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) +
          (4 * reciprocalPhaseFourStepRange N M j X : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      weylLagFourSharpRootMajorant
        (reciprocalPhaseFourStepRange N M j X) (b - a)
        (reciprocalPhaseFourStepLowerScale N M j X q) := by
  apply norm_reciprocalPhaseSum_le_fourStepWeylLagSharpRootMajorant_regularScale
    N M orders a b (reciprocalPhaseFourStepRange N M j X)
      hX hF hq hqOne hj hLength hHL haIcc hevalY hevalTop hregular
      hrFive hrSix
  simpa [reciprocalPhaseFourStepUpperScale,
    reciprocalPhaseFourStepLowerScale] using
      (reciprocalPhaseFourStepRange_upperSmall N M hX hF hqOne)

/-- Canonical-range source estimate in explicit real `1/16`-power notation. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeylLagRpowMajorant_canonicalRange
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hj : 1 ≤ j)
    (hLength : 1 ≤ b - a)
    (hHL : reciprocalPhaseFourStepRange N M j X ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepRange N M j X : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepRange N M j X : ℕ) ≤ 2 * X)
    (hregular : ∀ y ∈ Set.Icc (a : ℝ)
        ((a : ℝ) + (b - a : ℕ) +
          (4 * reciprocalPhaseFourStepRange N M j X : ℕ)),
      y ∉ reciprocalDerivativeCriticalUnion N M j orders X Y q)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((6 ^ 8 * ((b - a : ℕ) : ℝ) ^ 16) /
          ((((reciprocalPhaseFourStepRange N M j X) + 1 : ℕ) : ℝ) ^ 8)) ^
        (1 / 16 : ℝ) +
      ((6 ^ 12 * ((b - a : ℕ) : ℝ) ^ 16) /
          ((((reciprocalPhaseFourStepRange N M j X) + 1 : ℕ) : ℝ) ^ 4)) ^
        (1 / 16 : ℝ) +
      ((6 ^ 14 * ((b - a : ℕ) : ℝ) ^ 16) /
          ((((reciprocalPhaseFourStepRange N M j X) + 1 : ℕ) : ℝ) ^ 2)) ^
        (1 / 16 : ℝ) +
      ((6 ^ 15 * ((b - a : ℕ) : ℝ) ^ 16) /
          (((reciprocalPhaseFourStepRange N M j X) + 1 : ℕ) : ℝ)) ^
        (1 / 16 : ℝ) +
      (((6 * ((b - a : ℕ) : ℝ)) ^ 15 /
          reciprocalPhaseFourStepLowerScale N M j X q) ^ (1 / 16 : ℝ)) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeylLagRootMajorant_canonicalRange
    N M orders a b hX hF hq hqOne hj hLength hHL haIcc hevalY hevalTop
      hregular hrFive hrSix).trans_eq ?_
  exact weylLagFourRootMajorant_eq_rpow
    (reciprocalPhaseFourStepRange N M j X) (b - a)
      (by unfold reciprocalPhaseFourStepLowerScale; positivity)

/-- Global four-round reciprocal-phase estimate after replacing each order's
expanded bad starts by its interval hull.  The hull endpoints create at most
two cuts per order; each remaining component is handled at the chosen regular
range, while components shorter than `H` use the trivial bound. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b H : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (hupperSmall :
      ((H ^ 4 : ℕ) : ℝ) * reciprocalPhaseFourStepUpperScale N M j X ≤
        1 - ((H ^ 4 : ℕ) : ℝ) *
          reciprocalPhaseFourStepLowerScale N M j X q)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * H : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * H : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        ((H : ℝ) +
          weylLagFourSharpRootMajorant
            H (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X q)) +
        (orders.card : ℝ) *
          (16 * X * q +
            (4 * H + 1 : ℕ) + 1) := by
  let scale := reciprocalPhaseFourStepLowerScale N M j X q
  let B := (H : ℝ) + weylLagFourSharpRootMajorant H (b - a) scale
  have hscale : 0 < scale := by
    unfold scale reciprocalPhaseFourStepLowerScale
    positivity
  have hB : 0 ≤ B := by
    unfold B
    exact add_nonneg (by positivity)
      (weylLagFourSharpRootMajorant_nonneg H (b - a) hscale)
  have hglobal := norm_reciprocalPhaseSum_le_expandedHullComponentEnvelope
    N M j orders a b (4 * H + 1) hB hX hq.le hM hj hpow
      (B := B) (X := X) (Y := Y) fun c d hac hdb hwindow => by
        by_cases hcd : c < d
        · have hlenGlobal : d - c ≤ b - a := by omega
          by_cases hHlen : H ≤ d - c
          · have hcIcc : (c : ℝ) ∈ Set.Icc X Y := by
              have hcastAC : (a : ℝ) ≤ c := by exact_mod_cast hac
              have hcastDB : (d : ℝ) ≤ b := by exact_mod_cast hdb
              have hcastCD : (c : ℝ) ≤ d := by exact_mod_cast hcd.le
              constructor
              · exact haIcc.1.trans hcastAC
              · have hbY : (b : ℝ) ≤ Y := by
                  have hab : a ≤ b := by omega
                  norm_num only [Nat.cast_add, Nat.cast_mul,
                    Nat.cast_sub hab] at hevalY
                  linarith
                exact hcastCD.trans (hcastDB.trans hbY)
            have hevalYLocal : (c : ℝ) + (d - c : ℕ) + (4 * H : ℕ) ≤ Y := by
              have hab : a ≤ b := by omega
              have hcdle : c ≤ d := hcd.le
              norm_num only [Nat.cast_add, Nat.cast_mul,
                Nat.cast_sub hab] at hevalY
              norm_num only [Nat.cast_add, Nat.cast_mul,
                Nat.cast_sub hcdle]
              have hcastDB : (d : ℝ) ≤ b := by exact_mod_cast hdb
              linarith
            have hevalTopLocal :
                (c : ℝ) + (d - c : ℕ) + (4 * H : ℕ) ≤ 2 * X := by
              have hab : a ≤ b := by omega
              have hcdle : c ≤ d := hcd.le
              norm_num only [Nat.cast_add, Nat.cast_mul,
                Nat.cast_sub hab] at hevalTop
              norm_num only [Nat.cast_add, Nat.cast_mul,
                Nat.cast_sub hcdle]
              have hcastDB : (d : ℝ) ≤ b := by exact_mod_cast hdb
              linarith
            have hregular := regular_on_fourStepExpandedIcc_of_forwardWindows
              N M j orders hcd hwindow
            have hweyl :=
              norm_reciprocalPhaseSum_le_fourStepWeylLagSharpRootMajorant_regularScale
                N M orders c d H hX hF hq hqOne (by omega) (by omega) hHlen hcIcc
                  hevalYLocal hevalTopLocal hregular hrFive hrSix (by
                    simpa [reciprocalPhaseFourStepUpperScale,
                      reciprocalPhaseFourStepLowerScale] using hupperSmall)
            have hmono :=
              weylLagFourSharpRootMajorant_mono_length H hlenGlobal hscale
            exact hweyl.trans (hmono.trans (le_add_of_nonneg_left (by positivity)))
          · have hshort := norm_reciprocalPhaseSum_le_card N M j c d
            have hcard : ((Finset.Ico c d).card : ℝ) ≤ H := by
              rw [Nat.card_Ico]
              exact_mod_cast (Nat.lt_of_not_ge hHlen).le
            exact hshort.trans (hcard.trans (le_add_of_nonneg_right
              (weylLagFourSharpRootMajorant_nonneg H (b - a) hscale)))
        · have hempty : Finset.Ico c d = ∅ := by
              exact Finset.Ico_eq_empty hcd
          simp [reciprocalPhaseSum, hempty, B, hB]
  simpa [scale, B] using hglobal

/-- The previous canonical-range global estimate, recovered from the
arbitrary-range component theorem. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_canonicalRange
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepRange N M j X : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepRange N M j X : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (((reciprocalPhaseFourStepRange N M j X : ℕ) : ℝ) +
          weylLagFourSharpRootMajorant
            (reciprocalPhaseFourStepRange N M j X) (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X q)) +
        (orders.card : ℝ) *
          (16 * X * q +
            (4 * reciprocalPhaseFourStepRange N M j X + 1 : ℕ) + 1) := by
  apply norm_reciprocalPhaseSum_le_fourStepWeyl_components
    N M orders a b (reciprocalPhaseFourStepRange N M j X)
      hX hF hq hqOne hM hj hLength
      (reciprocalPhaseFourStepRange_upperSmall N M hX hF hqOne)
      haIcc hevalY hevalTop hpow hrFive hrSix

/-- The canonical four-step range, truncated only when the ambient interval
is shorter.  This range always fits the interval. -/
noncomputable def reciprocalPhaseFourStepAdaptiveRange
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) : ℕ :=
  min L (reciprocalPhaseFourStepRange N M j X)

theorem reciprocalPhaseFourStepAdaptiveRange_le_length
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) :
    reciprocalPhaseFourStepAdaptiveRange N M j X L ≤ L := by
  unfold reciprocalPhaseFourStepAdaptiveRange
  exact min_le_left _ _

theorem reciprocalPhaseFourStepAdaptiveRange_le_canonical
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) :
    reciprocalPhaseFourStepAdaptiveRange N M j X L ≤
      reciprocalPhaseFourStepRange N M j X := by
  unfold reciprocalPhaseFourStepAdaptiveRange
  exact min_le_right _ _

/-- A single denominator inequality covers both branches of the adaptive
range: either the interval length truncates the range, or the fourth-root
floor supplies the derivative-scale gain. -/
theorem one_div_reciprocalPhaseFourStepAdaptiveRange_succ_pow_four_le
    (N M : ℝ) (j : ℕ) {X : ℝ} (L : ℕ)
    (hU : 0 < reciprocalPhaseFourStepUpperScale N M j X) :
    1 / ((((reciprocalPhaseFourStepAdaptiveRange N M j X L) + 1 : ℕ) : ℝ) ^ 4) ≤
      2 * reciprocalPhaseFourStepUpperScale N M j X +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) := by
  let U := reciprocalPhaseFourStepUpperScale N M j X
  let C := reciprocalPhaseFourStepRange N M j X
  by_cases hLC : L ≤ C
  · have hmin : reciprocalPhaseFourStepAdaptiveRange N M j X L = L := by
      simp [reciprocalPhaseFourStepAdaptiveRange, C, hLC]
    rw [hmin]
    exact le_add_of_nonneg_left (by positivity)
  · have hCL : C ≤ L := by omega
    have hmin : reciprocalPhaseFourStepAdaptiveRange N M j X L = C := by
      simp [reciprocalPhaseFourStepAdaptiveRange, C, hCL]
    rw [hmin]
    have hroot := fourthRootFloor_add_one_gt (u := U)
    have hrootNonneg :
        0 ≤ Real.sqrt (Real.sqrt (1 / (2 * U))) := Real.sqrt_nonneg _
    have hpow := pow_lt_pow_left₀ hroot hrootNonneg (by omega : (4 : ℕ) ≠ 0)
    have hs : 0 ≤ Real.sqrt (1 / (2 * U)) := Real.sqrt_nonneg _
    have hx : 0 ≤ 1 / (2 * U) := by positivity
    have hrootPow :
        (Real.sqrt (Real.sqrt (1 / (2 * U)))) ^ 4 = 1 / (2 * U) := by
      calc
        (Real.sqrt (Real.sqrt (1 / (2 * U)))) ^ 4 =
            (Real.sqrt (Real.sqrt (1 / (2 * U))) ^ 2) ^ 2 := by ring
        _ = (Real.sqrt (1 / (2 * U))) ^ 2 := by rw [Real.sq_sqrt hs]
        _ = 1 / (2 * U) := Real.sq_sqrt hx
    rw [hrootPow] at hpow
    have hproduct : 1 ≤ 2 * U * (((C + 1 : ℕ) : ℝ) ^ 4) := by
      have := (div_lt_iff₀ (by positivity : 0 < 2 * U)).1 hpow
      have hCU : C = fourthRootFloor U := rfl
      rw [hCU]
      nlinarith
    have hinv : 1 / (((C + 1 : ℕ) : ℝ) ^ 4) ≤ 2 * U := by
      exact (div_le_iff₀ (by positivity : 0 < (((C + 1 : ℕ) : ℝ) ^ 4))).2
        (by nlinarith)
    exact hinv.trans (le_add_of_nonneg_right (by positivity))

/-- Truncating the canonical range preserves its terminal upper-smallness
inequality. -/
theorem reciprocalPhaseFourStepAdaptiveRange_upperSmall
    (N M : ℝ) {j L : ℕ} {X q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) :
    (((reciprocalPhaseFourStepAdaptiveRange N M j X L) ^ 4 : ℕ) : ℝ) *
        reciprocalPhaseFourStepUpperScale N M j X ≤
      1 - (((reciprocalPhaseFourStepAdaptiveRange N M j X L) ^ 4 : ℕ) : ℝ) *
        reciprocalPhaseFourStepLowerScale N M j X q := by
  have hpowNat :
      (reciprocalPhaseFourStepAdaptiveRange N M j X L) ^ 4 ≤
        (reciprocalPhaseFourStepRange N M j X) ^ 4 :=
    Nat.pow_le_pow_left
      (reciprocalPhaseFourStepAdaptiveRange_le_canonical N M j X L) 4
  have hpowReal :
      (((reciprocalPhaseFourStepAdaptiveRange N M j X L) ^ 4 : ℕ) : ℝ) ≤
        (((reciprocalPhaseFourStepRange N M j X) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hupperNonneg :
      0 ≤ reciprocalPhaseFourStepUpperScale N M j X :=
    (reciprocalPhaseFourStepUpperScale_pos N M hX hF).le
  have hlowerNonneg :
      0 ≤ reciprocalPhaseFourStepLowerScale N M j X q := by
    unfold reciprocalPhaseFourStepLowerScale
    positivity
  have hupperMul := mul_le_mul_of_nonneg_right hpowReal hupperNonneg
  have hlowerMul := mul_le_mul_of_nonneg_right hpowReal hlowerNonneg
  have hcanonical := reciprocalPhaseFourStepRange_upperSmall
    N M hX hF hqOne
  linarith

theorem reciprocalPhaseFourStepAdaptiveRange_pos
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L)
    (hsmall : 2 * reciprocalPhaseFourStepUpperScale N M j X ≤ 1) :
    0 < reciprocalPhaseFourStepAdaptiveRange N M j X L := by
  unfold reciprocalPhaseFourStepAdaptiveRange
  exact lt_min hLength
    (reciprocalPhaseFourStepRange_pos N M hX hF hsmall)

/-- The adaptive denominator converts the sharp logarithmic terminal
radicand into the sum of the normalized derivative scale and the unavoidable
short-interval endpoint term. -/
theorem weylLagFourLogScaleRadicand_adaptive_le
    (N M : ℝ) (j : ℕ) {X scale : ℝ} (L : ℕ)
    (hU : 0 < reciprocalPhaseFourStepUpperScale N M j X)
    (hscale : 0 < scale) :
    (6 * (L : ℝ)) ^ 15 *
          (1 + Real.log (reciprocalPhaseFourStepAdaptiveRange N M j X L)) ^ 4 /
        (((((reciprocalPhaseFourStepAdaptiveRange N M j X L) + 1 : ℕ) : ℝ) ^ 4) *
          scale) ≤
      ((6 * (L : ℝ)) ^ 15 *
          (1 + Real.log (reciprocalPhaseFourStepAdaptiveRange N M j X L)) ^ 4 *
        (2 * reciprocalPhaseFourStepUpperScale N M j X +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4))) / scale := by
  let H := reciprocalPhaseFourStepAdaptiveRange N M j X L
  let A := (6 * (L : ℝ)) ^ 15 * (1 + Real.log H) ^ 4
  let D := 2 * reciprocalPhaseFourStepUpperScale N M j X +
    1 / (((L + 1 : ℕ) : ℝ) ^ 4)
  have hden := one_div_reciprocalPhaseFourStepAdaptiveRange_succ_pow_four_le
    N M j L hU
  have hA : 0 ≤ A := by
    unfold A
    positivity
  calc
    A / ((((H + 1 : ℕ) : ℝ) ^ 4) * scale) =
        (A * (1 / (((H + 1 : ℕ) : ℝ) ^ 4))) / scale := by
      field_simp
    _ ≤ (A * D) / scale := by
      apply div_le_div_of_nonneg_right _ hscale.le
      exact mul_le_mul_of_nonneg_left hden hA

/-- Optimization-ready adaptive majorant.  Its terminal term depends on the
single effective quantity `2U + (L+1)⁻⁴`, so the canonical and short-interval
branches no longer need a case split downstream. -/
noncomputable def weylLagFourAdaptiveEffectiveRootMajorant
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) (scale : ℝ) : ℝ :=
  let H := reciprocalPhaseFourStepAdaptiveRange N M j X L
  let D := 2 * reciprocalPhaseFourStepUpperScale N M j X +
    1 / (((L + 1 : ℕ) : ℝ) ^ 4)
  iteratedSqrt 4
      ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) +
    iteratedSqrt 4
      ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) +
    iteratedSqrt 4
      ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) +
    iteratedSqrt 4
      ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) +
    iteratedSqrt 4
      (((6 * (L : ℝ)) ^ 15 * (1 + Real.log H) ^ 4 * D) / scale)

theorem weylLagFourLogRootMajorant_adaptive_le_effective
    (N M : ℝ) (j : ℕ) {X scale : ℝ} (L : ℕ)
    (hU : 0 < reciprocalPhaseFourStepUpperScale N M j X)
    (hscale : 0 < scale) :
    weylLagFourLogRootMajorant
        (reciprocalPhaseFourStepAdaptiveRange N M j X L) L scale ≤
      weylLagFourAdaptiveEffectiveRootMajorant N M j X L scale := by
  unfold weylLagFourLogRootMajorant weylLagFourAdaptiveEffectiveRootMajorant
  dsimp only
  apply add_le_add_right
  apply iteratedSqrt_mono
  exact weylLagFourLogScaleRadicand_adaptive_le N M j L hU hscale

/-- Dimensionless error scale used to balance critical-set deletion against
the adaptive four-step Weyl estimate. -/
noncomputable def reciprocalPhaseFourStepEffectiveErrorScale
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) : ℝ :=
  2 * reciprocalPhaseFourStepUpperScale N M j X +
    1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
    1 / reciprocalPhaseScale N M j X

/-- The two source terms in the low-frequency degree-five Weyl estimate. -/
noncomputable def reciprocalPhaseFourStepTwoTermError
    (N M : ℝ) (j : ℕ) (X : ℝ) : ℝ :=
  reciprocalPhaseScale N M j X / X ^ 5 +
    1 / reciprocalPhaseScale N M j X

/-- A fixed smaller power used to remove the auxiliary interval-length term
by a long/short interval dichotomy. -/
noncomputable def reciprocalPhaseFourStepTwoTermWidth
    (N M : ℝ) (j : ℕ) (X : ℝ) : ℝ :=
  reciprocalPhaseFourStepTwoTermError N M j X ^ (1 / 1024 : ℝ)

/-- A deliberately small fixed power is enough for the source's existential
Weyl exponent and leaves room for all subsequent root extractions. -/
noncomputable def reciprocalPhaseFourStepCriticalWidth
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) : ℝ :=
  reciprocalPhaseFourStepEffectiveErrorScale N M j X L ^ (1 / 128 : ℝ)

theorem reciprocalPhaseFourStepEffectiveErrorScale_pos
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    0 < reciprocalPhaseFourStepEffectiveErrorScale N M j X L := by
  unfold reciprocalPhaseFourStepEffectiveErrorScale
  have hU := reciprocalPhaseFourStepUpperScale_pos N M hX hF
  positivity

theorem reciprocalPhaseFourStepTwoTermError_pos
    (N M : ℝ) {j : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    0 < reciprocalPhaseFourStepTwoTermError N M j X := by
  unfold reciprocalPhaseFourStepTwoTermError
  positivity

theorem reciprocalPhaseFourStepTwoTermWidth_pos
    (N M : ℝ) {j : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    0 < reciprocalPhaseFourStepTwoTermWidth N M j X := by
  unfold reciprocalPhaseFourStepTwoTermWidth
  exact Real.rpow_pos_of_pos
    (reciprocalPhaseFourStepTwoTermError_pos N M hX hF) _

theorem reciprocalPhaseFourStepTwoTermWidth_pow
    (N M : ℝ) {j : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    (reciprocalPhaseFourStepTwoTermWidth N M j X) ^ 1024 =
      reciprocalPhaseFourStepTwoTermError N M j X := by
  unfold reciprocalPhaseFourStepTwoTermWidth
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul
    (reciprocalPhaseFourStepTwoTermError_pos N M hX hF).le]
  norm_num

/-- Abstract distance-kernel domination for the two-term Weyl width.  An
upper bound on the `F/X^5` term becomes an additive error, while a lower bound
for the transformed scale becomes the source's Type II decay kernel. -/
theorem reciprocalPhaseFourStepTwoTermWidth_le_typeIIDecayKernel_add_error
    (N M : ℝ) {j d : ℕ} {X R F A E : ℝ}
    (hX : 0 < X) (hscale : 0 < reciprocalPhaseScale N M j X)
    (hR : 0 < R) (hF : 0 ≤ F) (hA : 0 < A)
    (hupper : reciprocalPhaseScale N M j X / X ^ 5 ≤ E)
    (hlower :
      (1 + (d : ℝ) * F / R) / A ≤ reciprocalPhaseScale N M j X) :
    reciprocalPhaseFourStepTwoTermWidth N M j X ≤
      E ^ (1 / 1024 : ℝ) +
        A ^ (1 / 1024 : ℝ) *
          typeIIDecayKernel R F (1 / 1024 : ℝ) d := by
  let S := reciprocalPhaseScale N M j X
  let B := 1 + (d : ℝ) * F / R
  let δ : ℝ := 1 / 1024
  have hδ0 : 0 ≤ δ := by unfold δ; norm_num
  have hδ1 : δ ≤ 1 := by unfold δ; norm_num
  have hB : 0 < B := by
    unfold B
    have hterm : 0 ≤ (d : ℝ) * F / R :=
      div_nonneg (mul_nonneg (by positivity) hF) hR.le
    linarith
  have hu : 0 ≤ S / X ^ 5 := by
    unfold S
    positivity
  have hv : 0 ≤ 1 / S := by unfold S; positivity
  have hinv : 1 / S ≤ A / B := by
    calc
      1 / S ≤ 1 / (B / A) :=
        one_div_le_one_div_of_le (div_pos hB hA) (by simpa [S, B] using hlower)
      _ = A / B := by field_simp
  have huPow : (S / X ^ 5) ^ δ ≤ E ^ δ :=
    Real.rpow_le_rpow hu (by simpa [S] using hupper) hδ0
  have hvPow : (1 / S) ^ δ ≤ (A / B) ^ δ :=
    Real.rpow_le_rpow hv hinv hδ0
  have hdivPow : (A / B) ^ δ = A ^ δ * B ^ (-δ) := by
    rw [Real.div_rpow hA.le hB.le]
    rw [Real.rpow_neg hB.le]
    simp only [div_eq_mul_inv]
  calc
    reciprocalPhaseFourStepTwoTermWidth N M j X =
        (S / X ^ 5 + 1 / S) ^ δ := by
      simp only [reciprocalPhaseFourStepTwoTermWidth,
        reciprocalPhaseFourStepTwoTermError, S, δ]
    _ ≤ (S / X ^ 5) ^ δ + (1 / S) ^ δ :=
      Real.rpow_add_le_add_rpow hu hv hδ0 hδ1
    _ ≤ E ^ δ + (A / B) ^ δ := add_le_add huPow hvPow
    _ = E ^ δ + A ^ δ * typeIIDecayKernel R F δ d := by
      rw [hdivPow]
      rfl
    _ = E ^ (1 / 1024 : ℝ) +
        A ^ (1 / 1024 : ℝ) *
          typeIIDecayKernel R F (1 / 1024 : ℝ) d := by rfl

/-- Distance-kernel domination specialized to the equal-parameter phase used
by the final Tao application.  Large normalized separations use the exact
scale lower bound; small separations use the fact that the Weyl width is at
most one. -/
theorem reciprocalPhaseFourStepTwoTermWidth_typeIICorrelation_equalParameters_le
    (N K B E : ℝ) {j n n' : ℕ}
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hj : 2 ≤ j) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hwidthOne :
      reciprocalPhaseFourStepTwoTermWidth
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N j n n') j K ≤ 1)
    (hupper :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N j n n') j K / K ^ 5 ≤ E) :
    reciprocalPhaseFourStepTwoTermWidth
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N j n n') j K ≤
      E ^ (1 / 1024 : ℝ) +
        4 * typeIIDecayKernel B (reciprocalPhaseScale N N j (K * B))
          (1 / 1024 : ℝ) (Nat.dist n' n) := by
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter N j n n'
  let F := reciprocalPhaseScale N N j (K * B)
  let d := Nat.dist n' n
  let x := (d : ℝ) * F / B
  let δ : ℝ := 1 / 1024
  have hδ0 : 0 ≤ δ := by unfold δ; norm_num
  have hδ1 : δ ≤ 1 := by unfold δ; norm_num
  have hM' : M' ≠ 0 := by
    unfold M' typeIICorrelationHigherParameter
    exact typeIICorrelationHigherParameter_ne_zero hN (by omega)
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hscale : 0 < reciprocalPhaseScale N' M' j K := by
    unfold reciprocalPhaseScale
    have hMabs : 0 < |M'| := abs_pos.mpr hM'
    have hKpow : 0 < K ^ j := pow_pos hK j
    have hterm : 0 < |M'| / K ^ j := div_pos hMabs hKpow
    positivity
  have hF : 0 < F := by
    unfold F reciprocalPhaseScale
    have hNabs : 0 < |N| := abs_pos.mpr hN
    have hKBpos : 0 < K * B := mul_pos hK hB
    have hterm : 0 < |N| / (K * B) := div_pos hNabs hKBpos
    positivity
  have hx0 : 0 ≤ x := by unfold x; positivity
  have hlower : x / 2 ≤ reciprocalPhaseScale N' M' j K := by
    have hraw := typeIICorrelationScale_lower_of_equalParameters
      N K B hK hB hKB (by omega : 1 ≤ j) hn hn' hnB hn'B
    calc
      x / 2 = (d : ℝ) / B * (F / 2) := by
        unfold x
        ring
      _ ≤ reciprocalPhaseScale N' M' j K := by
        simpa only [N', M', F, d] using hraw
  by_cases hx : 1 ≤ x
  · have hbaseLower : (1 + (d : ℝ) * F / B) / 4 ≤
        reciprocalPhaseScale N' M' j K := by
      have hxeq : (d : ℝ) * F / B = x := by rfl
      rw [hxeq]
      calc
        (1 + x) / 4 ≤ x / 2 := by linarith
        _ ≤ reciprocalPhaseScale N' M' j K := hlower
    have hgeneric :=
      reciprocalPhaseFourStepTwoTermWidth_le_typeIIDecayKernel_add_error
        N' M' hK hscale hB hF.le (by norm_num : (0 : ℝ) < 4)
          (by simpa only [N', M'] using hupper) hbaseLower
    have hfour : (4 : ℝ) ^ δ ≤ 4 :=
      Real.rpow_le_self_of_one_le (by norm_num) hδ1
    have hkernelNonneg :
        0 ≤ typeIIDecayKernel B F δ d :=
      typeIIDecayKernel_nonneg δ d hB hF.le
    calc
      reciprocalPhaseFourStepTwoTermWidth N' M' j K ≤
          E ^ δ + 4 ^ δ * typeIIDecayKernel B F δ d := by
        simpa only [δ] using hgeneric
      _ ≤ E ^ δ + 4 * typeIIDecayKernel B F δ d := by gcongr
      _ = E ^ (1 / 1024 : ℝ) +
          4 * typeIIDecayKernel B F (1 / 1024 : ℝ) d := by rfl
  · have hxlt : x < 1 := lt_of_not_ge hx
    have hbasePos : 0 < 1 + (d : ℝ) * F / B := by positivity
    have hbaseTwo : 1 + (d : ℝ) * F / B ≤ 2 := by
      have hxeq : (d : ℝ) * F / B = x := by rfl
      rw [hxeq]
      linarith
    have htwoKernel : (2 : ℝ) ^ (-δ) ≤
        typeIIDecayKernel B F δ d := by
      unfold typeIIDecayKernel
      exact Real.rpow_le_rpow_of_nonpos hbasePos hbaseTwo
        (neg_nonpos.mpr hδ0)
    have hhalfPow : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-δ) := by
      calc
        (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (-δ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hkernelHalf : (1 / 2 : ℝ) ≤
        typeIIDecayKernel B F δ d := hhalfPow.trans htwoKernel
    have hwidthOne' : reciprocalPhaseFourStepTwoTermWidth N' M' j K ≤ 1 := by
      simpa only [N', M'] using hwidthOne
    have hEnonneg : 0 ≤ E := by
      have hu : 0 ≤ reciprocalPhaseScale N' M' j K / K ^ 5 := by positivity
      exact hu.trans (by simpa only [N', M'] using hupper)
    calc
      reciprocalPhaseFourStepTwoTermWidth N' M' j K ≤ 1 := hwidthOne'
      _ ≤ E ^ δ + 4 * typeIIDecayKernel B F δ d := by
        have hEpow : 0 ≤ E ^ δ := Real.rpow_nonneg hEnonneg δ
        nlinarith
      _ = E ^ (1 / 1024 : ℝ) +
          4 * typeIIDecayKernel B F (1 / 1024 : ℝ) d := by rfl

theorem reciprocalPhaseFourStepCriticalWidth_pos
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    0 < reciprocalPhaseFourStepCriticalWidth N M j X L := by
  unfold reciprocalPhaseFourStepCriticalWidth
  exact Real.rpow_pos_of_pos
    (reciprocalPhaseFourStepEffectiveErrorScale_pos N M hX hF) _

theorem reciprocalPhaseFourStepCriticalWidth_pow
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    (reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 128 =
      reciprocalPhaseFourStepEffectiveErrorScale N M j X L := by
  unfold reciprocalPhaseFourStepCriticalWidth
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul
    (reciprocalPhaseFourStepEffectiveErrorScale_pos N M hX hF).le]
  norm_num

theorem reciprocalPhaseFourStepCriticalWidth_le_one
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hsmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    reciprocalPhaseFourStepCriticalWidth N M j X L ≤ 1 := by
  unfold reciprocalPhaseFourStepCriticalWidth
  exact Real.rpow_le_one
    (reciprocalPhaseFourStepEffectiveErrorScale_pos N M hX hF).le
    hsmall (by norm_num)

theorem reciprocalPhaseFourStepAdaptiveEffectiveScale_le_errorScale
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hF : 0 < reciprocalPhaseScale N M j X) :
    2 * reciprocalPhaseFourStepUpperScale N M j X +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤
      reciprocalPhaseFourStepEffectiveErrorScale N M j X L := by
  unfold reciprocalPhaseFourStepEffectiveErrorScale
  exact le_add_of_nonneg_right (by positivity)

/-- Exact source normalization of the complete effective error scale. -/
theorem reciprocalPhaseFourStepEffectiveErrorScale_eq
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) :
    reciprocalPhaseFourStepEffectiveErrorScale N M j X L =
      240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          reciprocalPhaseScale N M j X / X ^ 5 +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X := by
  rw [reciprocalPhaseFourStepEffectiveErrorScale,
    reciprocalPhaseFourStepUpperScale_eq]
  ring

theorem reciprocalPhaseFourStepTwoTermError_le_effectiveErrorScale
    (N M : ℝ) (j : ℕ) {X : ℝ} (L : ℕ)
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    reciprocalPhaseFourStepTwoTermError N M j X ≤
      reciprocalPhaseFourStepEffectiveErrorScale N M j X L := by
  rw [reciprocalPhaseFourStepEffectiveErrorScale_eq]
  unfold reciprocalPhaseFourStepTwoTermError
  let K : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  have hK : 1 ≤ K := by
    unfold K
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 5 + j))
  have hterm : 0 ≤ reciprocalPhaseScale N M j X / X ^ 5 := by positivity
  have hmul : reciprocalPhaseScale N M j X / X ^ 5 ≤
      240 * K * reciprocalPhaseScale N M j X / X ^ 5 := by
    have hcoefficient : 1 ≤ 240 * K := by nlinarith
    calc
      reciprocalPhaseScale N M j X / X ^ 5 ≤
          240 * K * (reciprocalPhaseScale N M j X / X ^ 5) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoefficient) hterm]
      _ = 240 * K * reciprocalPhaseScale N M j X / X ^ 5 := by ring
  have hlength : 0 ≤ 1 / (((L + 1 : ℕ) : ℝ) ^ 4) := by positivity
  linarith

theorem reciprocalPhaseFourStepTwoTermWidth_le_one
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    reciprocalPhaseFourStepTwoTermWidth N M j X ≤ 1 := by
  unfold reciprocalPhaseFourStepTwoTermWidth
  apply Real.rpow_le_one
  · exact (reciprocalPhaseFourStepTwoTermError_pos N M hX hF).le
  · exact (reciprocalPhaseFourStepTwoTermError_le_effectiveErrorScale
      N M j L hX hF).trans herrorSmall
  · norm_num

theorem reciprocalPhaseFourStepCriticalWidth_eq
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) :
    reciprocalPhaseFourStepCriticalWidth N M j X L =
      (240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          reciprocalPhaseScale N M j X / X ^ 5 +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X) ^ (1 / 128 : ℝ) := by
  rw [reciprocalPhaseFourStepCriticalWidth,
    reciprocalPhaseFourStepEffectiveErrorScale_eq]

/-- Up to the explicit derivative-order factor, the effective error scale is
the source Weyl quantity plus the short-interval endpoint term. -/
theorem reciprocalPhaseFourStepEffectiveErrorScale_le_source
    (N M : ℝ) (j : ℕ) {X : ℝ} (L : ℕ)
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤
      (240 * ((((5 + j) ^ 5 : ℕ) : ℝ))) *
        (reciprocalPhaseScale N M j X / X ^ 5 +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
          1 / reciprocalPhaseScale N M j X) := by
  rw [reciprocalPhaseFourStepEffectiveErrorScale_eq]
  let A : ℝ := 240 * ((((5 + j) ^ 5 : ℕ) : ℝ))
  have hjNat : 1 ≤ (5 + j) ^ 5 := one_le_pow₀ (by omega)
  have hj : (1 : ℝ) ≤ ((((5 + j) ^ 5 : ℕ) : ℝ)) := by
    exact_mod_cast hjNat
  have hA : 1 ≤ A := by
    unfold A
    nlinarith
  have hfirst : 0 ≤ reciprocalPhaseScale N M j X / X ^ 5 := by positivity
  have hlength : 0 ≤ 1 / (((L + 1 : ℕ) : ℝ) ^ 4) := by positivity
  have hinv : 0 ≤ 1 / reciprocalPhaseScale N M j X := by positivity
  have hlengthMul :
      1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤
        A * (1 / (((L + 1 : ℕ) : ℝ) ^ 4)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) hlength]
  have hinvMul :
      1 / reciprocalPhaseScale N M j X ≤
        A * (1 / reciprocalPhaseScale N M j X) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) hinv]
  calc
    240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          reciprocalPhaseScale N M j X / X ^ 5 +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
          1 / reciprocalPhaseScale N M j X =
        A * (reciprocalPhaseScale N M j X / X ^ 5) +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
          1 / reciprocalPhaseScale N M j X := by
      unfold A
      ring
    _ ≤
        A * (reciprocalPhaseScale N M j X / X ^ 5) +
          A * (1 / (((L + 1 : ℕ) : ℝ) ^ 4)) +
          A * (1 / reciprocalPhaseScale N M j X) := by
      exact add_le_add (add_le_add le_rfl hlengthMul) hinvMul
    _ = A * (reciprocalPhaseScale N M j X / X ^ 5 +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
          1 / reciprocalPhaseScale N M j X) := by ring

theorem reciprocalPhaseFourStepCriticalWidth_le_source
    (N M : ℝ) (j : ℕ) {X : ℝ} (L : ℕ)
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    reciprocalPhaseFourStepCriticalWidth N M j X L ≤
      ((240 * ((((5 + j) ^ 5 : ℕ) : ℝ))) *
        (reciprocalPhaseScale N M j X / X ^ 5 +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
          1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ) := by
  unfold reciprocalPhaseFourStepCriticalWidth
  apply Real.rpow_le_rpow
    (reciprocalPhaseFourStepEffectiveErrorScale_pos N M hX hF).le
    (reciprocalPhaseFourStepEffectiveErrorScale_le_source N M j L hX hF)
  norm_num

theorem one_div_length_pow_four_le_sixteen_mul_effectiveErrorScale
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L) :
    1 / ((L : ℝ) ^ 4) ≤
      16 * reciprocalPhaseFourStepEffectiveErrorScale N M j X L := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hLp : 0 < ((L + 1 : ℕ) : ℝ) := by positivity
  have hplus : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by
    exact_mod_cast (by omega : L + 1 ≤ 2 * L)
  have hpow : (((L + 1 : ℕ) : ℝ) ^ 4) ≤ 16 * (L : ℝ) ^ 4 := by
    calc
      (((L + 1 : ℕ) : ℝ) ^ 4) ≤ (2 * (L : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hplus 4
      _ = 16 * (L : ℝ) ^ 4 := by ring
  have hinv : 1 / ((L : ℝ) ^ 4) ≤
      16 * (1 / (((L + 1 : ℕ) : ℝ) ^ 4)) := by
    rw [show 16 * (1 / (((L + 1 : ℕ) : ℝ) ^ 4)) =
        16 / (((L + 1 : ℕ) : ℝ) ^ 4) by ring]
    exact (div_le_div_iff₀ (pow_pos hL 4) (pow_pos hLp 4)).2 (by
      simpa using hpow)
  have hterm : 1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤
      reciprocalPhaseFourStepEffectiveErrorScale N M j X L := by
    unfold reciprocalPhaseFourStepEffectiveErrorScale
    have hU := reciprocalPhaseFourStepUpperScale_pos N M hX hF
    have hinvF : 0 ≤ 1 / reciprocalPhaseScale N M j X := by positivity
    linarith
  exact hinv.trans (mul_le_mul_of_nonneg_left hterm (by norm_num))

theorem one_div_length_mul_criticalWidth_pow_four_le
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L) :
    1 / (((L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 4) ≤
      16 * (reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 124 := by
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let E := reciprocalPhaseFourStepEffectiveErrorScale N M j X L
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hL : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hbase := one_div_length_pow_four_le_sixteen_mul_effectiveErrorScale
    N M hX hF hLength
  have hqpow : q ^ 128 = E :=
    reciprocalPhaseFourStepCriticalWidth_pow N M hX hF
  calc
    1 / (((L : ℝ) * q) ^ 4) = (1 / ((L : ℝ) ^ 4)) / q ^ 4 := by
      field_simp
    _ ≤ (16 * E) / q ^ 4 := by
      exact div_le_div_of_nonneg_right hbase (by positivity)
    _ = 16 * q ^ 124 := by
      rw [← hqpow]
      field_simp

/-- The differencing range used for the final optimization: the canonical
derivative range is additionally capped by `floor(L*q)`, making every short
component cost at most the chosen critical-width proportion of the interval.
-/
noncomputable def reciprocalPhaseFourStepOptimizedRange
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) : ℕ :=
  min (Nat.floor ((L : ℝ) *
      reciprocalPhaseFourStepCriticalWidth N M j X L))
    (reciprocalPhaseFourStepRange N M j X)

theorem reciprocalPhaseFourStepOptimizedRange_le_canonical
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) :
    reciprocalPhaseFourStepOptimizedRange N M j X L ≤
      reciprocalPhaseFourStepRange N M j X := by
  unfold reciprocalPhaseFourStepOptimizedRange
  exact min_le_right _ _

theorem reciprocalPhaseFourStepOptimizedRange_cast_le
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    (reciprocalPhaseFourStepOptimizedRange N M j X L : ℝ) ≤
      (L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L := by
  calc
    (reciprocalPhaseFourStepOptimizedRange N M j X L : ℝ) ≤
        (Nat.floor ((L : ℝ) *
          reciprocalPhaseFourStepCriticalWidth N M j X L) : ℝ) := by
      exact_mod_cast (min_le_left
        (Nat.floor ((L : ℝ) *
          reciprocalPhaseFourStepCriticalWidth N M j X L))
        (reciprocalPhaseFourStepRange N M j X))
    _ ≤ (L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L := by
      exact Nat.floor_le (mul_nonneg (by positivity)
        (reciprocalPhaseFourStepCriticalWidth_pos N M hX hF).le)

theorem reciprocalPhaseFourStepOptimizedRange_margin_cast_le
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X) :
    (((4 * reciprocalPhaseFourStepOptimizedRange N M j X L + 1 : ℕ) : ℝ)) ≤
      4 * (L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L + 1 := by
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hH := reciprocalPhaseFourStepOptimizedRange_cast_le N M hX hF
    (j := j) (L := L)
  nlinarith

theorem log_reciprocalPhaseFourStepOptimizedRange_le_log_length
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    Real.log (reciprocalPhaseFourStepOptimizedRange N M j X L) ≤
      Real.log L := by
  have hq := reciprocalPhaseFourStepCriticalWidth_le_one
    N M hX hF herrorSmall
  have hHcast := reciprocalPhaseFourStepOptimizedRange_cast_le N M hX hF
    (j := j) (L := L)
  have hLq :
      (L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L ≤ (L : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (Nat.cast_nonneg L)]
  have hHLcast :
      (reciprocalPhaseFourStepOptimizedRange N M j X L : ℝ) ≤ (L : ℝ) :=
    hHcast.trans hLq
  by_cases hzero : reciprocalPhaseFourStepOptimizedRange N M j X L = 0
  · rw [hzero]
    simpa using Real.log_nonneg (by exact_mod_cast hLength)
  · apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hzero
    · exact hHLcast

/-- Denominator gain for the optimized range.  Its two branches contribute
the derivative scale `2U` and the explicit `1/(L*q)^4` term. -/
theorem one_div_reciprocalPhaseFourStepOptimizedRange_succ_pow_four_le
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L) :
    1 / ((((reciprocalPhaseFourStepOptimizedRange N M j X L) + 1 : ℕ) : ℝ) ^ 4) ≤
      2 * reciprocalPhaseFourStepUpperScale N M j X +
        1 / (((L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 4) := by
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let R := Nat.floor ((L : ℝ) * q)
  let U := reciprocalPhaseFourStepUpperScale N M j X
  let C := reciprocalPhaseFourStepRange N M j X
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hL : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hU : 0 < U := reciprocalPhaseFourStepUpperScale_pos N M hX hF
  by_cases hRC : R ≤ C
  · have hmin : reciprocalPhaseFourStepOptimizedRange N M j X L = R := by
      simp [reciprocalPhaseFourStepOptimizedRange, R, C, q, hRC]
    rw [hmin]
    have hfloor := Nat.lt_floor_add_one ((L : ℝ) * q)
    have hbase : 0 ≤ (L : ℝ) * q := by positivity
    have hpow := pow_lt_pow_left₀ hfloor hbase (by omega : (4 : ℕ) ≠ 0)
    have hinv : 1 / (((R + 1 : ℕ) : ℝ) ^ 4) ≤
        1 / (((L : ℝ) * q) ^ 4) := by
      apply one_div_le_one_div_of_le (by positivity)
      simpa [R] using hpow.le
    exact hinv.trans (le_add_of_nonneg_left (by positivity))
  · have hCR : C ≤ R := by omega
    have hmin : reciprocalPhaseFourStepOptimizedRange N M j X L = C := by
      simp [reciprocalPhaseFourStepOptimizedRange, R, C, q, hCR]
    rw [hmin]
    have hcanonical : 1 / (((C + 1 : ℕ) : ℝ) ^ 4) ≤ 2 * U := by
      simpa [C, U, reciprocalPhaseFourStepRange] using
        (one_div_fourthRootFloor_add_one_pow_four_le hU)
    exact hcanonical.trans (le_add_of_nonneg_right (by positivity))

/-- Once the effective error is at most one, the complete optimized-range
denominator is a fixed power of the critical width. -/
theorem one_div_reciprocalPhaseFourStepOptimizedRange_succ_pow_four_le_criticalWidth
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    1 / ((((reciprocalPhaseFourStepOptimizedRange N M j X L) + 1 : ℕ) : ℝ) ^ 4) ≤
      17 * (reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 124 := by
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let E := reciprocalPhaseFourStepEffectiveErrorScale N M j X L
  let U := reciprocalPhaseFourStepUpperScale N M j X
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hqone : q ≤ 1 :=
    reciprocalPhaseFourStepCriticalWidth_le_one N M hX hF herrorSmall
  have hqpow : q ^ 128 = E :=
    reciprocalPhaseFourStepCriticalWidth_pow N M hX hF
  have hqfour : q ^ 4 ≤ 1 := pow_le_one₀ hq.le hqone
  have hqmono : q ^ 128 ≤ q ^ 124 := by
    calc
      q ^ 128 = q ^ 124 * q ^ 4 := by ring
      _ ≤ q ^ 124 * 1 := mul_le_mul_of_nonneg_left hqfour (by positivity)
      _ = q ^ 124 := by ring
  have hUerror : 2 * U ≤ E := by
    calc
      2 * U ≤ 2 * U + 1 / (((L + 1 : ℕ) : ℝ) ^ 4) :=
        le_add_of_nonneg_right (by positivity)
      _ ≤ E := reciprocalPhaseFourStepAdaptiveEffectiveScale_le_errorScale
        N M hF
  have hUq : 2 * U ≤ q ^ 124 := by
    rw [← hqpow] at hUerror
    exact hUerror.trans hqmono
  have hlengthq : 1 / (((L : ℝ) * q) ^ 4) ≤ 16 * q ^ 124 :=
    one_div_length_mul_criticalWidth_pow_four_le N M hX hF hLength
  have hden := one_div_reciprocalPhaseFourStepOptimizedRange_succ_pow_four_le
    N M hX hF hLength
  exact hden.trans (by linarith)

/-- Fourth-root extraction of the optimized denominator estimate.  The
integer constant `3` absorbs the fourth root of `17`. -/
theorem one_div_reciprocalPhaseFourStepOptimizedRange_succ_le_criticalWidth
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    1 / (((reciprocalPhaseFourStepOptimizedRange N M j X L) + 1 : ℕ) : ℝ) ≤
      3 * (reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 31 := by
  let H := reciprocalPhaseFourStepOptimizedRange N M j X L
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hden :=
    one_div_reciprocalPhaseFourStepOptimizedRange_succ_pow_four_le_criticalWidth
      N M hX hF hLength herrorSmall
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
  calc
    (1 / (((H + 1 : ℕ) : ℝ))) ^ 4 =
        1 / (((H + 1 : ℕ) : ℝ) ^ 4) := by ring
    _ ≤ 17 * q ^ 124 := hden
    _ ≤ 81 * q ^ 124 := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (3 * q ^ 31) ^ 4 := by ring

/-- The weakest of the four diagonal Weyl roots already saves one full
critical-width factor. -/
theorem optimizedRange_lastDiagonalRoot_le_criticalWidth
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    iteratedSqrt 4
        ((6 ^ 15 * (L : ℝ) ^ 16) /
          (((reciprocalPhaseFourStepOptimizedRange N M j X L) + 1 : ℕ) : ℝ)) ≤
      18 * (L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L := by
  let H := reciprocalPhaseFourStepOptimizedRange N M j X L
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hqone : q ≤ 1 :=
    reciprocalPhaseFourStepCriticalWidth_le_one N M hX hF herrorSmall
  have hinv : 1 / (((H + 1 : ℕ) : ℝ)) ≤ 3 * q ^ 31 :=
    one_div_reciprocalPhaseFourStepOptimizedRange_succ_le_criticalWidth
      N M hX hF hLength herrorSmall
  have hqpow : q ^ 31 ≤ q ^ 16 := by
    calc
      q ^ 31 = q ^ 16 * q ^ 15 := by ring
      _ ≤ q ^ 16 * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hq.le hqone) (by positivity)
      _ = q ^ 16 := by ring
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0) (by positivity)
  rw [iteratedSqrt_four_pow_sixteen (by positivity)]
  calc
    (6 ^ 15 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ)) =
        6 ^ 15 * (L : ℝ) ^ 16 * (1 / (((H + 1 : ℕ) : ℝ))) := by ring
    _ ≤ 6 ^ 15 * (L : ℝ) ^ 16 * (3 * q ^ 31) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ 6 ^ 15 * (L : ℝ) ^ 16 * (3 * q ^ 16) := by gcongr
    _ = (3 * 6 ^ 15) * ((L : ℝ) ^ 16 * q ^ 16) := by ring
    _ ≤ 18 ^ 16 * ((L : ℝ) ^ 16 * q ^ 16) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (18 * (L : ℝ) * q) ^ 16 := by ring

/-- Every earlier diagonal radicand is bounded by the last one once its
numerical coefficient is at most `6^15`. -/
theorem weylDiagonalRadicand_le_last
    (H L k : ℕ) (hk : 1 ≤ k) {C : ℝ}
    (hCmax : C ≤ 6 ^ 15) :
    (C * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ k) ≤
      (6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ) := by
  let d : ℝ := ((H + 1 : ℕ) : ℝ)
  have hd : 1 ≤ d := by
    unfold d
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le H))
  have hdpow : d ≤ d ^ k := by
    simpa using (pow_le_pow_right₀ hd hk : d ^ 1 ≤ d ^ k)
  have hinv : 1 / d ^ k ≤ 1 / d :=
    one_div_le_one_div_of_le (by positivity) hdpow
  calc
    (C * (L : ℝ) ^ 16) / d ^ k =
        (C * (L : ℝ) ^ 16) * (1 / d ^ k) := by ring
    _ ≤ (6 ^ 15 * (L : ℝ) ^ 16) * (1 / d ^ k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hCmax (by positivity)
    _ ≤ (6 ^ 15 * (L : ℝ) ^ 16) * (1 / d) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (6 ^ 15 * (L : ℝ) ^ 16) / d := by ring

/-- The sum of all four optimized-range diagonal roots is absorbed by
`72 * L * q`. -/
theorem optimizedRange_diagonalRootSum_le_criticalWidth
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    let H := reciprocalPhaseFourStepOptimizedRange N M j X L
    iteratedSqrt 4
        ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) +
      iteratedSqrt 4
        ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) +
      iteratedSqrt 4
        ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) +
      iteratedSqrt 4
        ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) ≤
      72 * (L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L := by
  dsimp only
  let H := reciprocalPhaseFourStepOptimizedRange N M j X L
  let T := iteratedSqrt 4
    ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ))
  have hzero : iteratedSqrt 4
      ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) ≤ T := by
    apply iteratedSqrt_mono
    exact weylDiagonalRadicand_le_last H L 8 (by norm_num)
      (by norm_num)
  have hone : iteratedSqrt 4
      ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) ≤ T := by
    apply iteratedSqrt_mono
    exact weylDiagonalRadicand_le_last H L 4 (by norm_num)
      (by norm_num)
  have htwo : iteratedSqrt 4
      ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) ≤ T := by
    apply iteratedSqrt_mono
    exact weylDiagonalRadicand_le_last H L 2 (by norm_num)
      (by norm_num)
  have hlast : T ≤ 18 * (L : ℝ) *
      reciprocalPhaseFourStepCriticalWidth N M j X L :=
    optimizedRange_lastDiagonalRoot_le_criticalWidth
      N M hX hF hLength herrorSmall
  dsimp only [T] at hzero hone htwo hlast ⊢
  linarith

/-- The endpoint term in the effective error forces `L*q^32` to be bounded
below by an absolute constant. -/
theorem one_le_two_mul_length_mul_criticalWidth_pow_thirtyTwo
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L) :
    1 ≤ 2 * (L : ℝ) *
      (reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 32 := by
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hL : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hbase := one_div_length_pow_four_le_sixteen_mul_effectiveErrorScale
    N M hX hF hLength
  have hqpow : q ^ 128 = reciprocalPhaseFourStepEffectiveErrorScale N M j X L :=
    reciprocalPhaseFourStepCriticalWidth_pow N M hX hF
  rw [← hqpow] at hbase
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
  have hcross : 1 ≤ 16 * q ^ 128 * (L : ℝ) ^ 4 := by
    have := (div_le_iff₀ (pow_pos hL 4)).1 hbase
    nlinarith
  calc
    (1 : ℝ) ^ 4 = 1 := by norm_num
    _ ≤ 16 * q ^ 128 * (L : ℝ) ^ 4 := hcross
    _ = (2 * (L : ℝ) * q ^ 32) ^ 4 := by ring

/-- On an interval no longer than the ambient dyadic scale, the preceding
endpoint estimate also supplies the power needed by the terminal root. -/
theorem one_le_two_mul_ambient_mul_criticalWidth_pow_seventeen
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L) (hLX : (L : ℝ) ≤ X)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    1 ≤ 2 * X *
      (reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 17 := by
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hqone : q ≤ 1 :=
    reciprocalPhaseFourStepCriticalWidth_le_one N M hX hF herrorSmall
  have hqpow : q ^ 32 ≤ q ^ 17 := by
    calc
      q ^ 32 = q ^ 17 * q ^ 15 := by ring
      _ ≤ q ^ 17 * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hq.le hqone) (by positivity)
      _ = q ^ 17 := by ring
  calc
    1 ≤ 2 * (L : ℝ) * q ^ 32 :=
      one_le_two_mul_length_mul_criticalWidth_pow_thirtyTwo
        N M hX hF hLength
    _ ≤ 2 * X * q ^ 17 := by gcongr

/-- Optimization-ready terminal radicand at the `floor(L*q)`-capped range.
Both the harmonic logarithm and the fourth-power denominator have now been
eliminated in favor of `log L`, `U`, and `q`. -/
theorem weylLagFourLogScaleRadicand_optimized_le
    (N M : ℝ) {j L : ℕ} {X scale : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1)
    (hscale : 0 < scale) :
    (6 * (L : ℝ)) ^ 15 *
          (1 + Real.log (reciprocalPhaseFourStepOptimizedRange N M j X L)) ^ 4 /
        (((((reciprocalPhaseFourStepOptimizedRange N M j X L) + 1 : ℕ) : ℝ) ^ 4) *
          scale) ≤
      ((6 * (L : ℝ)) ^ 15 * (1 + Real.log L) ^ 4 *
        (2 * reciprocalPhaseFourStepUpperScale N M j X +
          1 / (((L : ℝ) *
            reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 4))) / scale := by
  let H := reciprocalPhaseFourStepOptimizedRange N M j X L
  let A := (6 * (L : ℝ)) ^ 15
  let D := 2 * reciprocalPhaseFourStepUpperScale N M j X +
    1 / (((L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L) ^ 4)
  have hlog := log_reciprocalPhaseFourStepOptimizedRange_le_log_length
    N M hX hF hLength herrorSmall
  have hlogH : 0 ≤ 1 + Real.log H := by
    by_cases hzero : H = 0
    · simp [hzero]
    · have hHone : 1 ≤ H := (Nat.one_le_iff_ne_zero).2 hzero
      exact add_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hHone))
  have hlogPow : (1 + Real.log H) ^ 4 ≤ (1 + Real.log L) ^ 4 :=
    pow_le_pow_left₀ hlogH (add_le_add_right hlog 1) 4
  have hden := one_div_reciprocalPhaseFourStepOptimizedRange_succ_pow_four_le
    N M hX hF hLength
  have hA : 0 ≤ A := by unfold A; positivity
  have hproduct :
      A * (1 + Real.log H) ^ 4 *
          (1 / (((H + 1 : ℕ) : ℝ) ^ 4)) ≤
        A * (1 + Real.log L) ^ 4 * D := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hlogPow hA) hden
      (by positivity) (mul_nonneg hA (by positivity))
  calc
    A * (1 + Real.log H) ^ 4 /
          (((((H + 1 : ℕ) : ℝ) ^ 4) * scale)) =
        (A * (1 + Real.log H) ^ 4 *
          (1 / (((H + 1 : ℕ) : ℝ) ^ 4))) / scale := by
      field_simp
    _ ≤ (A * (1 + Real.log L) ^ 4 * D) / scale := by
      exact div_le_div_of_nonneg_right hproduct hscale.le

noncomputable def weylLagFourOptimizedEffectiveRootMajorant
    (N M : ℝ) (j : ℕ) (X : ℝ) (L : ℕ) (scale : ℝ) : ℝ :=
  let H := reciprocalPhaseFourStepOptimizedRange N M j X L
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let D := 2 * reciprocalPhaseFourStepUpperScale N M j X +
    1 / (((L : ℝ) * q) ^ 4)
  iteratedSqrt 4
      ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) +
    iteratedSqrt 4
      ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) +
    iteratedSqrt 4
      ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) +
    iteratedSqrt 4
      ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) +
    iteratedSqrt 4
      (((6 * (L : ℝ)) ^ 15 * (1 + Real.log L) ^ 4 * D) / scale)

/-- The optimized terminal radicand is a sixteenth power with a positive
critical-width saving.  The deliberately round constant leaves all
derivative-order and logarithmic factors explicit. -/
theorem optimizedEffectiveTerminalRadicand_le_pow
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L) (hLX : (L : ℝ) ≤ X)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    let q := reciprocalPhaseFourStepCriticalWidth N M j X L
    let D := 2 * reciprocalPhaseFourStepUpperScale N M j X +
      1 / (((L : ℝ) * q) ^ 4)
    (((6 * (L : ℝ)) ^ 15 * (1 + Real.log L) ^ 4 * D) /
        reciprocalPhaseFourStepLowerScale N M j X q) ≤
      (100 * (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log L) * X * q) ^ 16 := by
  dsimp only
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let F := reciprocalPhaseScale N M j X
  let K : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let R := 1 + Real.log L
  let U := reciprocalPhaseFourStepUpperScale N M j X
  let scale := reciprocalPhaseFourStepLowerScale N M j X q
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hqone : q ≤ 1 :=
    reciprocalPhaseFourStepCriticalWidth_le_one N M hX hF herrorSmall
  have hL : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hR : 1 ≤ R := by
    unfold R
    have : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hLength)
    linarith
  have hK : 1 ≤ K := by
    unfold K
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 5 + j))
  have hscale : 0 < scale := by
    unfold scale reciprocalPhaseFourStepLowerScale
    positivity
  have hLpow : (L : ℝ) ^ 15 ≤ X ^ 15 :=
    pow_le_pow_left₀ hL.le hLX 15
  have hLpowEleven : (L : ℝ) ^ 11 * X ^ 5 ≤ X ^ 16 := by
    have h := pow_le_pow_left₀ hL.le hLX 11
    calc
      (L : ℝ) ^ 11 * X ^ 5 ≤ X ^ 11 * X ^ 5 :=
        mul_le_mul_of_nonneg_right h (by positivity)
      _ = X ^ 16 := by ring
  have hLpowTimesX : (L : ℝ) ^ 15 * X ≤ X ^ 16 := by
    calc
      (L : ℝ) ^ 15 * X ≤ X ^ 15 * X :=
        mul_le_mul_of_nonneg_right hLpow hX.le
      _ = X ^ 16 := by ring
  have hambient := one_le_two_mul_ambient_mul_criticalWidth_pow_seventeen
    N M hX hF hLength hLX herrorSmall
  have hinvq : 1 / q ≤ 2 * X * q ^ 16 := by
    apply (div_le_iff₀ hq).2
    nlinarith [hambient]
  have hqpow : q ^ 128 = reciprocalPhaseFourStepEffectiveErrorScale N M j X L :=
    reciprocalPhaseFourStepCriticalWidth_pow N M hX hF
  have hinvFerror : 1 / F ≤ reciprocalPhaseFourStepEffectiveErrorScale N M j X L := by
    unfold F reciprocalPhaseFourStepEffectiveErrorScale
    have hU := reciprocalPhaseFourStepUpperScale_pos N M hX hF
    have hlength : 0 ≤ 1 / (((L + 1 : ℕ) : ℝ) ^ 4) := by positivity
    linarith
  have hinvFq : (1 / F) * (1 / q ^ 5) ≤ q ^ 123 := by
    rw [← hqpow] at hinvFerror
    calc
      (1 / F) * (1 / q ^ 5) ≤ q ^ 128 * (1 / q ^ 5) :=
        mul_le_mul_of_nonneg_right hinvFerror (by positivity)
      _ = q ^ 123 := by field_simp
  have hqmono : q ^ 123 ≤ q ^ 16 := by
    calc
      q ^ 123 = q ^ 16 * q ^ 107 := by ring
      _ ≤ q ^ 16 * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hq.le hqone) (by positivity)
      _ = q ^ 16 := by ring
  let A := (6 * (L : ℝ)) ^ 15 * R ^ 4
  have hupperEq : A * (2 * U) / scale =
      640 * K * (6 * (L : ℝ)) ^ 15 * R ^ 4 * (1 / q) := by
    unfold A U scale K
    rw [reciprocalPhaseFourStepUpperScale_eq,
      reciprocalPhaseFourStepLowerScale_eq N M j hX.ne']
    field_simp
    ring
  have hupper : A * (2 * U) / scale ≤
      1280 * 6 ^ 15 * K * R ^ 4 * X ^ 16 * q ^ 16 := by
    rw [hupperEq]
    calc
      640 * K * (6 * (L : ℝ)) ^ 15 * R ^ 4 * (1 / q) ≤
          640 * K * (6 * (L : ℝ)) ^ 15 * R ^ 4 *
            (2 * X * q ^ 16) := by gcongr
      _ = 1280 * 6 ^ 15 * K * R ^ 4 *
          ((L : ℝ) ^ 15 * X) * q ^ 16 := by ring
      _ ≤ 1280 * 6 ^ 15 * K * R ^ 4 * X ^ 16 * q ^ 16 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLpowTimesX (by positivity)) (by positivity)
  have hlowerEq : A * (1 / (((L : ℝ) * q) ^ 4)) / scale =
      (8 / 3 : ℝ) * 6 ^ 15 * R ^ 4 * ((L : ℝ) ^ 11 * X ^ 5) *
        ((1 / F) * (1 / q ^ 5)) := by
    unfold A scale F
    rw [reciprocalPhaseFourStepLowerScale_eq N M j hX.ne']
    field_simp
  have hlower : A * (1 / (((L : ℝ) * q) ^ 4)) / scale ≤
      (8 / 3 : ℝ) * 6 ^ 15 * R ^ 4 * X ^ 16 * q ^ 16 := by
    rw [hlowerEq]
    gcongr
    exact hinvFq.trans hqmono
  have hsplit : A * (2 * U + 1 / (((L : ℝ) * q) ^ 4)) / scale =
      A * (2 * U) / scale + A * (1 / (((L : ℝ) * q) ^ 4)) / scale := by ring
  rw [show (6 * (L : ℝ)) ^ 15 * R ^ 4 *
      (2 * U + 1 / (((L : ℝ) * q) ^ 4)) / scale =
        A * (2 * U + 1 / (((L : ℝ) * q) ^ 4)) / scale by rfl,
    hsplit]
  calc
    A * (2 * U) / scale + A * (1 / (((L : ℝ) * q) ^ 4)) / scale ≤
        1280 * 6 ^ 15 * K * R ^ 4 * X ^ 16 * q ^ 16 +
          (8 / 3 : ℝ) * 6 ^ 15 * R ^ 4 * X ^ 16 * q ^ 16 :=
      add_le_add hupper hlower
    _ ≤ 1283 * 6 ^ 15 * (K + 1) * R ^ 4 * X ^ 16 * q ^ 16 := by
      rw [show 1280 * 6 ^ 15 * K * R ^ 4 * X ^ 16 * q ^ 16 +
          (8 / 3 : ℝ) * 6 ^ 15 * R ^ 4 * X ^ 16 * q ^ 16 =
        (1280 * K + 8 / 3) * (6 ^ 15 * R ^ 4 * X ^ 16 * q ^ 16) by ring,
        show 1283 * 6 ^ 15 * (K + 1) * R ^ 4 * X ^ 16 * q ^ 16 =
        (1283 * (K + 1)) * (6 ^ 15 * R ^ 4 * X ^ 16 * q ^ 16) by ring]
      exact mul_le_mul_of_nonneg_right (by linarith [hK]) (by positivity)
    _ ≤ 100 ^ 16 * (K + 1) ^ 16 * R ^ 16 * X ^ 16 * q ^ 16 := by
      have hKpow : K + 1 ≤ (K + 1) ^ 16 := by
        simpa using (pow_le_pow_right₀ (by linarith : 1 ≤ K + 1)
          (by norm_num : 1 ≤ (16 : ℕ)))
      have hRpow : R ^ 4 ≤ R ^ 16 :=
        pow_le_pow_right₀ hR (by norm_num)
      calc
        1283 * 6 ^ 15 * (K + 1) * R ^ 4 * X ^ 16 * q ^ 16 ≤
            1283 * 6 ^ 15 * (K + 1) ^ 16 * R ^ 16 * X ^ 16 * q ^ 16 := by
          gcongr
        _ ≤ 100 ^ 16 * (K + 1) ^ 16 * R ^ 16 * X ^ 16 * q ^ 16 := by
          gcongr
          norm_num
    _ = (100 * (K + 1) * R * X * q) ^ 16 := by ring

theorem optimizedEffectiveTerminalRoot_le_criticalWidth
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L) (hLX : (L : ℝ) ≤ X)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    let q := reciprocalPhaseFourStepCriticalWidth N M j X L
    let D := 2 * reciprocalPhaseFourStepUpperScale N M j X +
      1 / (((L : ℝ) * q) ^ 4)
    iteratedSqrt 4
        ((((6 * (L : ℝ)) ^ 15 * (1 + Real.log L) ^ 4 * D) /
          reciprocalPhaseFourStepLowerScale N M j X q)) ≤
      100 * (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log L) * X * q := by
  dsimp only
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hlog : 0 ≤ 1 + Real.log (L : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hLength : (1 : ℝ) ≤ L)
    linarith
  have hscale : 0 < reciprocalPhaseFourStepLowerScale N M j X q := by
    unfold reciprocalPhaseFourStepLowerScale
    positivity
  have hU : 0 < reciprocalPhaseFourStepUpperScale N M j X :=
    reciprocalPhaseFourStepUpperScale_pos N M hX hF
  have hnum : 0 ≤ (6 * (L : ℝ)) ^ 15 * (1 + Real.log L) ^ 4 *
      (2 * reciprocalPhaseFourStepUpperScale N M j X +
        1 / (((L : ℝ) * q) ^ 4)) := by
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hlog 4))
      (add_nonneg (by positivity) (by positivity))
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0) (by positivity)
  rw [iteratedSqrt_four_pow_sixteen (div_nonneg hnum hscale.le)]
  exact optimizedEffectiveTerminalRadicand_le_pow
    N M hX hF hLength hLX herrorSmall

/-- The complete optimized Weyl majorant has one fixed critical-width power. -/
theorem weylLagFourOptimizedEffectiveRootMajorant_le_fixedPower
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L) (hLX : (L : ℝ) ≤ X)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    weylLagFourOptimizedEffectiveRootMajorant N M j X L
        (reciprocalPhaseFourStepLowerScale N M j X
          (reciprocalPhaseFourStepCriticalWidth N M j X L)) ≤
      172 * (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log L) * X *
          reciprocalPhaseFourStepCriticalWidth N M j X L := by
  let H := reciprocalPhaseFourStepOptimizedRange N M j X L
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let K : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let R := 1 + Real.log L
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hR : 1 ≤ R := by
    unfold R
    have := Real.log_nonneg (by exact_mod_cast hLength : (1 : ℝ) ≤ L)
    linarith
  have hK : 1 ≤ K := by
    unfold K
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 5 + j))
  have hdiag := optimizedRange_diagonalRootSum_le_criticalWidth
    N M hX hF hLength herrorSmall
  have hterminal := optimizedEffectiveTerminalRoot_le_criticalWidth
    N M hX hF hLength hLX herrorSmall
  unfold weylLagFourOptimizedEffectiveRootMajorant
  dsimp only
  change
    iteratedSqrt 4 ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) +
      iteratedSqrt 4 ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) +
      iteratedSqrt 4 ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) +
      iteratedSqrt 4 ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) +
      iteratedSqrt 4 (((6 * (L : ℝ)) ^ 15 * R ^ 4 *
        (2 * reciprocalPhaseFourStepUpperScale N M j X +
          1 / (((L : ℝ) * q) ^ 4))) /
        reciprocalPhaseFourStepLowerScale N M j X q) ≤
      172 * (K + 1) * R * X * q
  have hdiag' :
      iteratedSqrt 4 ((6 ^ 8 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 8)) +
        iteratedSqrt 4 ((6 ^ 12 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 4)) +
        iteratedSqrt 4 ((6 ^ 14 * (L : ℝ) ^ 16) / (((H + 1 : ℕ) : ℝ) ^ 2)) +
        iteratedSqrt 4 ((6 ^ 15 * (L : ℝ) ^ 16) / ((H + 1 : ℕ) : ℝ)) ≤
      72 * (L : ℝ) * q := hdiag
  have hterminal' :
      iteratedSqrt 4 (((6 * (L : ℝ)) ^ 15 * R ^ 4 *
        (2 * reciprocalPhaseFourStepUpperScale N M j X +
          1 / (((L : ℝ) * q) ^ 4))) /
        reciprocalPhaseFourStepLowerScale N M j X q) ≤
      100 * (K + 1) * R * X * q := hterminal
  calc
    _ ≤ 72 * (L : ℝ) * q + 100 * (K + 1) * R * X * q :=
      add_le_add hdiag' hterminal'
    _ ≤ 172 * (K + 1) * R * X * q := by
      have hfactor : (L : ℝ) ≤ (K + 1) * R * X := by
        have hmult : 1 ≤ (K + 1) * R := by
          have hKplus : 1 ≤ K + 1 :=
            hK.trans (le_add_of_nonneg_right (by norm_num))
          have hRzero : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
          calc
            1 ≤ R := hR
            _ ≤ (K + 1) * R := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right hKplus hRzero
        calc
          (L : ℝ) ≤ X := hLX
          _ ≤ (K + 1) * R * X := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hmult hX.le
      nlinarith [mul_le_mul_of_nonneg_right hfactor hq.le]

theorem weylLagFourLogRootMajorant_optimized_le_effective
    (N M : ℝ) {j L : ℕ} {X scale : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hLength : 1 ≤ L)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1)
    (hscale : 0 < scale) :
    weylLagFourLogRootMajorant
        (reciprocalPhaseFourStepOptimizedRange N M j X L) L scale ≤
      weylLagFourOptimizedEffectiveRootMajorant N M j X L scale := by
  unfold weylLagFourLogRootMajorant weylLagFourOptimizedEffectiveRootMajorant
  dsimp only
  apply add_le_add_right
  apply iteratedSqrt_mono
  exact weylLagFourLogScaleRadicand_optimized_le
    N M hX hF hLength herrorSmall hscale

/-- Any range below the canonical fourth-root floor inherits the terminal
upper-smallness inequality. -/
theorem reciprocalPhaseFourStep_upperSmall_of_le_canonical
    (N M : ℝ) {j H : ℕ} {X q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1)
    (hH : H ≤ reciprocalPhaseFourStepRange N M j X) :
    ((H ^ 4 : ℕ) : ℝ) * reciprocalPhaseFourStepUpperScale N M j X ≤
      1 - ((H ^ 4 : ℕ) : ℝ) *
        reciprocalPhaseFourStepLowerScale N M j X q := by
  have hpowNat : H ^ 4 ≤
      (reciprocalPhaseFourStepRange N M j X) ^ 4 :=
    Nat.pow_le_pow_left hH 4
  have hpowReal : ((H ^ 4 : ℕ) : ℝ) ≤
      (((reciprocalPhaseFourStepRange N M j X) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hupperNonneg : 0 ≤ reciprocalPhaseFourStepUpperScale N M j X :=
    (reciprocalPhaseFourStepUpperScale_pos N M hX hF).le
  have hlowerNonneg :
      0 ≤ reciprocalPhaseFourStepLowerScale N M j X q := by
    unfold reciprocalPhaseFourStepLowerScale
    positivity
  have hupperMul := mul_le_mul_of_nonneg_right hpowReal hupperNonneg
  have hlowerMul := mul_le_mul_of_nonneg_right hpowReal hlowerNonneg
  have hcanonical := reciprocalPhaseFourStepRange_upperSmall
    N M hX hF hqOne
  linarith

theorem reciprocalPhaseFourStepOptimizedRange_upperSmall
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    (((reciprocalPhaseFourStepOptimizedRange N M j X L) ^ 4 : ℕ) : ℝ) *
        reciprocalPhaseFourStepUpperScale N M j X ≤
      1 - (((reciprocalPhaseFourStepOptimizedRange N M j X L) ^ 4 : ℕ) : ℝ) *
        reciprocalPhaseFourStepLowerScale N M j X
          (reciprocalPhaseFourStepCriticalWidth N M j X L) := by
  exact reciprocalPhaseFourStep_upperSmall_of_le_canonical N M hX hF
    (reciprocalPhaseFourStepCriticalWidth_pos N M hX hF)
    (reciprocalPhaseFourStepCriticalWidth_le_one N M hX hF herrorSmall)
    (reciprocalPhaseFourStepOptimizedRange_le_canonical N M j X L)

/-- Global four-round estimate at the interval-adaptive range.  The range
automatically fits the interval and retains the canonical upper-smallness
needed by the regular components. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_adaptiveRange
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (((reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) : ℝ) +
          weylLagFourSharpRootMajorant
            (reciprocalPhaseFourStepAdaptiveRange N M j X (b - a)) (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X q)) +
        (orders.card : ℝ) *
          (16 * X * q +
            (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) + 1 : ℕ) +
              1) := by
  apply norm_reciprocalPhaseSum_le_fourStepWeyl_components
    N M orders a b (reciprocalPhaseFourStepAdaptiveRange N M j X (b - a))
      hX hF hq hqOne hM hj hLength
      (reciprocalPhaseFourStepAdaptiveRange_upperSmall N M hX hF hq hqOne)
      haIcc hevalY hevalTop hpow hrFive hrSix

/-- Source-readable adaptive global estimate, with the residual harmonic
factor bounded by `1 + log H`. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_adaptiveRange_log
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (((reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) : ℝ) +
          weylLagFourLogRootMajorant
            (reciprocalPhaseFourStepAdaptiveRange N M j X (b - a)) (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X q)) +
        (orders.card : ℝ) *
          (16 * X * q +
            (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) + 1 : ℕ) +
              1) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeyl_components_adaptiveRange
    N M orders a b hX hF hq hqOne hM hj hLength haIcc hevalY hevalTop
      hpow hrFive hrSix).trans ?_
  gcongr
  exact weylLagFourSharpRootMajorant_le_logRootMajorant
    (reciprocalPhaseFourStepAdaptiveRange N M j X (b - a)) (b - a)
      (by unfold reciprocalPhaseFourStepLowerScale; positivity)

/-- Optimization-ready global component estimate.  The terminal Weyl term
uses only the effective adaptive quantity `2U + (L+1)⁻⁴`. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_adaptiveEffective
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y q : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hq : 0 < q) (hqOne : q ≤ 1) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (((reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) : ℝ) +
          weylLagFourAdaptiveEffectiveRootMajorant N M j X (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X q)) +
        (orders.card : ℝ) *
          (16 * X * q +
            (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) + 1 : ℕ) +
              1) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeyl_components_adaptiveRange_log
    N M orders a b hX hF hq hqOne hM hj hLength haIcc hevalY hevalTop
      hpow hrFive hrSix).trans ?_
  gcongr
  exact weylLagFourLogRootMajorant_adaptive_le_effective N M j (b - a)
    (reciprocalPhaseFourStepUpperScale_pos N M hX hF)
    (by unfold reciprocalPhaseFourStepLowerScale; positivity)

/-- The optimization-ready global estimate with the critical-set width fixed
to a small power of the complete effective error scale. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_balanced
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (((reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) : ℕ) : ℝ) +
          weylLagFourAdaptiveEffectiveRootMajorant N M j X (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X
              (reciprocalPhaseFourStepCriticalWidth N M j X (b - a)))) +
        (orders.card : ℝ) *
          (16 * X * reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
            (4 * reciprocalPhaseFourStepAdaptiveRange N M j X (b - a) + 1 : ℕ) +
              1) := by
  apply norm_reciprocalPhaseSum_le_fourStepWeyl_components_adaptiveEffective
    N M orders a b hX hF
      (reciprocalPhaseFourStepCriticalWidth_pos N M hX hF)
      (reciprocalPhaseFourStepCriticalWidth_le_one N M hX hF herrorSmall)
      hM hj hLength haIcc hevalY hevalTop hpow hrFive hrSix

/-- Global logarithmic Weyl estimate at the genuinely optimized range
`min(floor(L*q), canonicalRange)`.  In particular, its explicit short-piece
penalty is bounded by `L*q`. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_optimizedRange_log
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (((reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) : ℝ) +
          weylLagFourLogRootMajorant
            (reciprocalPhaseFourStepOptimizedRange N M j X (b - a)) (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X
              (reciprocalPhaseFourStepCriticalWidth N M j X (b - a)))) +
        (orders.card : ℝ) *
          (16 * X * reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
            (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) + 1 : ℕ) +
              1) := by
  have hbase := norm_reciprocalPhaseSum_le_fourStepWeyl_components
    N M orders a b (reciprocalPhaseFourStepOptimizedRange N M j X (b - a))
      hX hF
      (reciprocalPhaseFourStepCriticalWidth_pos N M hX hF)
      (reciprocalPhaseFourStepCriticalWidth_le_one N M hX hF herrorSmall)
      hM hj hLength
      (reciprocalPhaseFourStepOptimizedRange_upperSmall N M hX hF herrorSmall)
      haIcc hevalY hevalTop hpow hrFive hrSix
  refine hbase.trans ?_
  gcongr
  exact weylLagFourSharpRootMajorant_le_logRootMajorant
    (reciprocalPhaseFourStepOptimizedRange N M j X (b - a)) (b - a)
      (by
        have hqpos := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
          (L := b - a)
        unfold reciprocalPhaseFourStepLowerScale
        positivity)

/-- The same optimized-range theorem with both occurrences of the range
penalty replaced by their explicit `L*q` bounds. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_optimizedPenalty
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (((b - a : ℕ) : ℝ) *
            reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
          weylLagFourLogRootMajorant
            (reciprocalPhaseFourStepOptimizedRange N M j X (b - a)) (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X
              (reciprocalPhaseFourStepCriticalWidth N M j X (b - a)))) +
        (orders.card : ℝ) *
          (16 * X * reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
            4 * ((b - a : ℕ) : ℝ) *
              reciprocalPhaseFourStepCriticalWidth N M j X (b - a) + 2) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeyl_components_optimizedRange_log
    N M orders a b hX hF herrorSmall hM hj hLength haIcc hevalY hevalTop
      hpow hrFive hrSix).trans ?_
  have hH := reciprocalPhaseFourStepOptimizedRange_cast_le N M hX hF
    (j := j) (L := b - a)
  have hmargin := reciprocalPhaseFourStepOptimizedRange_margin_cast_le
    N M hX hF (j := j) (L := b - a)
  have hregular :
      (reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℝ) +
          weylLagFourLogRootMajorant
            (reciprocalPhaseFourStepOptimizedRange N M j X (b - a)) (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X
              (reciprocalPhaseFourStepCriticalWidth N M j X (b - a))) ≤
        ((b - a : ℕ) : ℝ) *
            reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
          weylLagFourLogRootMajorant
            (reciprocalPhaseFourStepOptimizedRange N M j X (b - a)) (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X
              (reciprocalPhaseFourStepCriticalWidth N M j X (b - a))) :=
    add_le_add_left hH _
  have herror :
      16 * X * reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
          (((4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) + 1 : ℕ) : ℝ)) +
          1 ≤
        16 * X * reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
          4 * ((b - a : ℕ) : ℝ) *
            reciprocalPhaseFourStepCriticalWidth N M j X (b - a) + 2 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hmargin ⊢
    linarith
  exact add_le_add
    (mul_le_mul_of_nonneg_left hregular (by positivity))
    (mul_le_mul_of_nonneg_left herror (by positivity))

/-- Fully optimization-ready component theorem: the short penalties are
`L*q`, and the terminal root contains only `log L`, `U`, `q`, and the explicit
lower derivative scale. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_optimizedEffective
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (((b - a : ℕ) : ℝ) *
            reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
          weylLagFourOptimizedEffectiveRootMajorant N M j X (b - a)
            (reciprocalPhaseFourStepLowerScale N M j X
              (reciprocalPhaseFourStepCriticalWidth N M j X (b - a)))) +
        (orders.card : ℝ) *
          (16 * X * reciprocalPhaseFourStepCriticalWidth N M j X (b - a) +
            4 * ((b - a : ℕ) : ℝ) *
              reciprocalPhaseFourStepCriticalWidth N M j X (b - a) + 2) := by
  refine (norm_reciprocalPhaseSum_le_fourStepWeyl_components_optimizedPenalty
    N M orders a b hX hF herrorSmall hM hj hLength haIcc hevalY hevalTop
      hpow hrFive hrSix).trans ?_
  gcongr
  apply weylLagFourLogRootMajorant_optimized_le_effective
    N M hX hF hLength herrorSmall
  have hqpos := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
    (L := b - a)
  unfold reciprocalPhaseFourStepLowerScale
  positivity

/-- Fixed-power global degree-five Weyl envelope.  All four diagonal roots,
the optimized terminal root, and both range penalties now carry the single
critical-width factor `q = E^(1/128)`. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_fixedPower
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let q := reciprocalPhaseFourStepCriticalWidth N M j X (b - a)
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (173 * (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * q) +
        (orders.card : ℝ) * (20 * X * q + 2) := by
  dsimp only
  let L := b - a
  let H := reciprocalPhaseFourStepOptimizedRange N M j X L
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let K : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let R := 1 + Real.log L
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hR : 1 ≤ R := by
    have hLengthNat : 1 ≤ L := hLength
    have hLengthReal : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLengthNat
    unfold R
    have := Real.log_nonneg hLengthReal
    linarith
  have hK : 1 ≤ K := by
    unfold K
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 5 + j))
  have hLX : (L : ℝ) ≤ X := by
    have htop := hevalTop
    change (a : ℝ) + (L : ℝ) + ((4 * H : ℕ) : ℝ) ≤ 2 * X at htop
    have hmargin : 0 ≤ ((4 * H : ℕ) : ℝ) := by positivity
    linarith [haIcc.1]
  have hmajor := weylLagFourOptimizedEffectiveRootMajorant_le_fixedPower
    N M hX hF hLength hLX herrorSmall
  have hbase := norm_reciprocalPhaseSum_le_fourStepWeyl_components_optimizedEffective
    N M orders a b hX hF herrorSmall hM hj hLength haIcc hevalY hevalTop
      hpow hrFive hrSix
  have hmult : 1 ≤ (K + 1) * R := by
    have hKplus : 1 ≤ K + 1 :=
      hK.trans (le_add_of_nonneg_right (by norm_num))
    have hRzero : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
    calc
      1 ≤ R := hR
      _ ≤ (K + 1) * R := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hKplus hRzero
  have hfactor : (L : ℝ) ≤ (K + 1) * R * X := by
    calc
      (L : ℝ) ≤ X := hLX
      _ ≤ (K + 1) * R * X := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hmult hX.le
  have hfactorq : (L : ℝ) * q ≤ (K + 1) * R * X * q :=
    mul_le_mul_of_nonneg_right hfactor hq.le
  have hregular : (L : ℝ) * q +
      weylLagFourOptimizedEffectiveRootMajorant N M j X L
        (reciprocalPhaseFourStepLowerScale N M j X q) ≤
      173 * (K + 1) * R * X * q := by
    linarith [hfactorq, hmajor]
  have hdeletion : 16 * X * q + 4 * (L : ℝ) * q + 2 ≤
      20 * X * q + 2 := by
    have := mul_le_mul_of_nonneg_right hLX hq.le
    nlinarith
  refine hbase.trans ?_
  exact add_le_add
    (mul_le_mul_of_nonneg_left hregular (by positivity))
    (mul_le_mul_of_nonneg_left hdeletion (by positivity))

/-- Source-normalized form of the fixed-power global Weyl envelope. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_components_fixedPower_source
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let S := ((240 * ((((5 + j) ^ 5 : ℕ) : ℝ))) *
      (reciprocalPhaseScale N M j X / X ^ 5 +
        1 / ((((b - a) + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ)
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) *
        (173 * (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * S) +
        (orders.card : ℝ) * (20 * X * S + 2) := by
  dsimp only
  let L := b - a
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let S := ((240 * ((((5 + j) ^ 5 : ℕ) : ℝ))) *
    (reciprocalPhaseScale N M j X / X ^ 5 +
      1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
      1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ)
  have hbase := norm_reciprocalPhaseSum_le_fourStepWeyl_components_fixedPower
    N M orders a b hX hF herrorSmall hM hj hLength haIcc hevalY hevalTop
      hpow hrFive hrSix
  have hqS : q ≤ S := reciprocalPhaseFourStepCriticalWidth_le_source
    N M j L hX hF
  have hlog : 0 ≤ 1 + Real.log (L : ℝ) := by
    have hLengthNat : 1 ≤ L := hLength
    have hLengthReal : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLengthNat
    have := Real.log_nonneg hLengthReal
    linarith
  have hregular :
      173 * (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (L : ℝ)) * X * q ≤
        173 * (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (L : ℝ)) * X * S := by
    exact mul_le_mul_of_nonneg_left hqS (by positivity)
  have hdeletion : 20 * X * q + 2 ≤ 20 * X * S + 2 := by
    have := mul_le_mul_of_nonneg_left hqS (by positivity : 0 ≤ 20 * X)
    linarith
  refine hbase.trans ?_
  exact add_le_add
    (mul_le_mul_of_nonneg_left hregular (by positivity))
    (mul_le_mul_of_nonneg_left hdeletion (by positivity))

/-- Endpoint-absorbed source Weyl estimate.  The entire component envelope is
a single explicit coefficient times `X` and the `1/128` power of the
source-normalized error. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_fixedPower_source
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let S := ((240 * ((((5 + j) ^ 5 : ℕ) : ℝ))) *
      (reciprocalPhaseScale N M j X / X ^ 5 +
        1 / ((((b - a) + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ)
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        ((((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * S) := by
  dsimp only
  let L := b - a
  let q := reciprocalPhaseFourStepCriticalWidth N M j X L
  let K : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let R := 1 + Real.log L
  let S := ((240 * K) *
    (reciprocalPhaseScale N M j X / X ^ 5 +
      1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
      1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ)
  have hbase :=
    norm_reciprocalPhaseSum_le_fourStepWeyl_components_fixedPower_source
      N M orders a b hX hF herrorSmall hM hj hLength haIcc hevalY hevalTop
        hpow hrFive hrSix
  have hq : 0 < q := reciprocalPhaseFourStepCriticalWidth_pos N M hX hF
  have hqone : q ≤ 1 :=
    reciprocalPhaseFourStepCriticalWidth_le_one N M hX hF herrorSmall
  have hqS : q ≤ S := reciprocalPhaseFourStepCriticalWidth_le_source
    N M j L hX hF
  have hS : 0 < S := hq.trans_le hqS
  have hLX : (L : ℝ) ≤ X := by
    let H := reciprocalPhaseFourStepOptimizedRange N M j X L
    have htop := hevalTop
    change (a : ℝ) + (L : ℝ) + ((4 * H : ℕ) : ℝ) ≤ 2 * X at htop
    have hmargin : 0 ≤ ((4 * H : ℕ) : ℝ) := by positivity
    linarith [haIcc.1]
  have hambient := one_le_two_mul_ambient_mul_criticalWidth_pow_seventeen
    N M hX hF hLength hLX herrorSmall
  have hqseventeen : q ^ 17 ≤ q := by
    calc
      q ^ 17 = q * q ^ 16 := by ring
      _ ≤ q * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hq.le hqone) hq.le
      _ = q := by ring
  have hone : 1 ≤ 2 * X * q := by
    exact hambient.trans (mul_le_mul_of_nonneg_left hqseventeen (by positivity))
  have htwo : 2 ≤ 4 * X * S := by
    have hqSscaled := mul_le_mul_of_nonneg_left hqS (by positivity : 0 ≤ 4 * X)
    nlinarith
  have hR : 1 ≤ R := by
    have hLengthNat : 1 ≤ L := hLength
    have hLengthReal : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLengthNat
    unfold R
    have := Real.log_nonneg hLengthReal
    linarith
  have hK : 1 ≤ K := by
    unfold K
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 5 + j))
  let Z := (K + 1) * R * X * S
  have hmult : 1 ≤ (K + 1) * R := by
    have hKplus : 1 ≤ K + 1 :=
      hK.trans (le_add_of_nonneg_right (by norm_num))
    have hRzero : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
    calc
      1 ≤ R := hR
      _ ≤ (K + 1) * R := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hKplus hRzero
  have hXSZ : X * S ≤ Z := by
    unfold Z
    have := mul_le_mul_of_nonneg_right hmult (mul_nonneg hX.le hS.le)
    nlinarith
  have hdelete : 20 * X * S + 2 ≤ 24 * Z := by
    nlinarith [hXSZ]
  have hregular :
      173 * (K + 1) * R * X * S ≤ 173 * Z := by
    unfold Z
    ring_nf
    exact le_rfl
  refine hbase.trans ?_
  rw [show (((370 * orders.card + 173 : ℕ) : ℝ)) =
      173 * (((2 * orders.card + 1 : ℕ) : ℝ)) +
        24 * (orders.card : ℝ) by norm_num; ring]
  calc
    ((2 * orders.card + 1 : ℕ) : ℝ) *
          (173 * (K + 1) * R * X * S) +
        (orders.card : ℝ) * (20 * X * S + 2) ≤
      ((2 * orders.card + 1 : ℕ) : ℝ) * (173 * Z) +
        (orders.card : ℝ) * (24 * Z) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hregular (by positivity))
        (mul_le_mul_of_nonneg_left hdelete (by positivity))
    _ = (173 * (((2 * orders.card + 1 : ℕ) : ℝ)) +
        24 * (orders.card : ℝ)) * Z := by ring

/-- In the low-frequency range `F ≤ X^4`, any interval with `X ≤ L+1`
absorbs its endpoint term into the two source terms. -/
theorem one_div_length_succ_pow_four_le_reciprocalPhaseTwoTermError
    (N M : ℝ) (j L : ℕ) {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hFlow : reciprocalPhaseScale N M j X ≤ X ^ 4)
    (hXL : X ≤ ((L + 1 : ℕ) : ℝ)) :
    1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤
      reciprocalPhaseScale N M j X / X ^ 5 +
        1 / reciprocalPhaseScale N M j X := by
  let F := reciprocalPhaseScale N M j X
  have hXpow : X ^ 4 ≤ (((L + 1 : ℕ) : ℝ) ^ 4) :=
    pow_le_pow_left₀ hX.le hXL 4
  have hlengthX : 1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤ 1 / X ^ 4 :=
    one_div_le_one_div_of_le (pow_pos hX 4) hXpow
  have hXF : 1 / X ^ 4 ≤ 1 / F :=
    one_div_le_one_div_of_le hF hFlow
  exact hlengthX.trans (hXF.trans (le_add_of_nonneg_left (by positivity)))

/-- At the weaker `1/1024` target width, a long interval forces its endpoint
term below the `1020`-th power of that width. -/
theorem one_div_length_succ_pow_four_le_twoTermWidth_pow
    (N M : ℝ) (j L : ℕ) {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hFlow : reciprocalPhaseScale N M j X ≤ X ^ 4)
    (hlong : X * reciprocalPhaseFourStepTwoTermWidth N M j X ≤
      ((L + 1 : ℕ) : ℝ)) :
    1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤
      (reciprocalPhaseFourStepTwoTermWidth N M j X) ^ 1020 := by
  let F := reciprocalPhaseScale N M j X
  let A := reciprocalPhaseFourStepTwoTermError N M j X
  let p := reciprocalPhaseFourStepTwoTermWidth N M j X
  have hp : 0 < p := reciprocalPhaseFourStepTwoTermWidth_pos N M hX hF
  have hA : 0 < A := reciprocalPhaseFourStepTwoTermError_pos N M hX hF
  have hpPower : p ^ 1024 = A :=
    reciprocalPhaseFourStepTwoTermWidth_pow N M hX hF
  have hXF : 1 / X ^ 4 ≤ 1 / F :=
    one_div_le_one_div_of_le hF hFlow
  have hXA : 1 / X ^ 4 ≤ A := by
    unfold A reciprocalPhaseFourStepTwoTermError
    exact hXF.trans (le_add_of_nonneg_left (by positivity))
  have hpow : (X * p) ^ 4 ≤ (((L + 1 : ℕ) : ℝ) ^ 4) :=
    pow_le_pow_left₀ (by positivity) hlong 4
  have hinv : 1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤ 1 / ((X * p) ^ 4) :=
    one_div_le_one_div_of_le (by positivity) hpow
  calc
    1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤ 1 / ((X * p) ^ 4) := hinv
    _ = (1 / X ^ 4) * (1 / p ^ 4) := by ring
    _ ≤ A * (1 / p ^ 4) :=
      mul_le_mul_of_nonneg_right hXA (by positivity)
    _ = p ^ 1020 := by
      rw [← hpPower]
      field_simp

/-- On the long branch, the original three-term `1/128` source power is
bounded by an explicit coefficient times the two-term `1/1024` width. -/
theorem reciprocalPhaseFourStepSourceWidth_le_twoTermWidth
    (N M : ℝ) (j L : ℕ) {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hFlow : reciprocalPhaseScale N M j X ≤ X ^ 4)
    (herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1)
    (hlong : X * reciprocalPhaseFourStepTwoTermWidth N M j X ≤
      ((L + 1 : ℕ) : ℝ)) :
    ((240 * ((((5 + j) ^ 5 : ℕ) : ℝ))) *
      (reciprocalPhaseScale N M j X / X ^ 5 +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ) ≤
      480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        reciprocalPhaseFourStepTwoTermWidth N M j X := by
  let K : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let A := reciprocalPhaseFourStepTwoTermError N M j X
  let p := reciprocalPhaseFourStepTwoTermWidth N M j X
  let B := (240 * K) *
    (reciprocalPhaseScale N M j X / X ^ 5 +
      1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
      1 / reciprocalPhaseScale N M j X)
  have hK : 1 ≤ K := by
    unfold K
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 5 + j))
  have hp : 0 < p := reciprocalPhaseFourStepTwoTermWidth_pos N M hX hF
  have hpOne : p ≤ 1 :=
    reciprocalPhaseFourStepTwoTermWidth_le_one N M hX hF herrorSmall
  have hpPower : p ^ 1024 = A :=
    reciprocalPhaseFourStepTwoTermWidth_pow N M hX hF
  have hlength : 1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤ p ^ 1020 :=
    one_div_length_succ_pow_four_le_twoTermWidth_pow
      N M j L hX hF hFlow hlong
  have hApow : A ≤ p ^ 1020 := by
    rw [← hpPower]
    calc
      p ^ 1024 = p ^ 1020 * p ^ 4 := by ring
      _ ≤ p ^ 1020 * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hp.le hpOne) (by positivity)
      _ = p ^ 1020 := by ring
  have hBpos : 0 < B := by
    unfold B
    positivity
  have hBpow : (B ^ (1 / 128 : ℝ)) ^ 128 = B := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hBpos.le]
    norm_num
  have hBbound : B ≤ 480 * K * p ^ 1020 := by
    have hsum : reciprocalPhaseScale N M j X / X ^ 5 +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X ≤ 2 * p ^ 1020 := by
      have hAeq : reciprocalPhaseScale N M j X / X ^ 5 +
          1 / reciprocalPhaseScale N M j X = A := by
        rfl
      rw [show reciprocalPhaseScale N M j X / X ^ 5 +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
          1 / reciprocalPhaseScale N M j X =
        (reciprocalPhaseScale N M j X / X ^ 5 +
          1 / reciprocalPhaseScale N M j X) +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) by ring, hAeq]
      linarith
    unfold B
    calc
      (240 * K) * (reciprocalPhaseScale N M j X / X ^ 5 +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
          1 / reciprocalPhaseScale N M j X) ≤
          (240 * K) * (2 * p ^ 1020) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 480 * K * p ^ 1020 := by ring
  have hpMono : p ^ 1020 ≤ p ^ 128 := by
    calc
      p ^ 1020 = p ^ 128 * p ^ 892 := by ring
      _ ≤ p ^ 128 * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hp.le hpOne) (by positivity)
      _ = p ^ 128 := by ring
  have hCpow : 480 * K ≤ (480 * K) ^ 128 := by
    simpa using (pow_le_pow_right₀ (by nlinarith [hK] : 1 ≤ 480 * K)
      (by norm_num : 1 ≤ (128 : ℕ)))
  apply le_of_pow_le_pow_left₀ (by norm_num : (128 : ℕ) ≠ 0) (by positivity)
  rw [show ((240 * K) *
      (reciprocalPhaseScale N M j X / X ^ 5 +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ) =
      B ^ (1 / 128 : ℝ) by rfl, hBpow]
  calc
    B ≤ 480 * K * p ^ 1020 := hBbound
    _ ≤ 480 * K * p ^ 128 := mul_le_mul_of_nonneg_left hpMono (by positivity)
    _ ≤ (480 * K) ^ 128 * p ^ 128 :=
      mul_le_mul_of_nonneg_right hCpow (by positivity)
    _ = (480 * K * p) ^ 128 := by ring

/-- Two-term source normalization once the interval endpoint term is no
larger than `F/X^5 + 1/F`. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_fixedPower_twoTerm_of_lengthTerm_le
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (hlengthTerm : 1 / ((((b - a) + 1 : ℕ) : ℝ) ^ 4) ≤
      reciprocalPhaseScale N M j X / X ^ 5 +
        1 / reciprocalPhaseScale N M j X)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let T := ((480 * ((((5 + j) ^ 5 : ℕ) : ℝ))) *
      (reciprocalPhaseScale N M j X / X ^ 5 +
        1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ)
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        ((((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * T) := by
  dsimp only
  let L := b - a
  let K : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let A := reciprocalPhaseScale N M j X / X ^ 5 +
    1 / reciprocalPhaseScale N M j X
  let S := ((240 * K) *
    (reciprocalPhaseScale N M j X / X ^ 5 +
      1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
      1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ)
  let T := ((480 * K) * A) ^ (1 / 128 : ℝ)
  have hbase := norm_reciprocalPhaseSum_le_fourStepWeyl_fixedPower_source
    N M orders a b hX hF herrorSmall hM hj hLength haIcc hevalY hevalTop
      hpow hrFive hrSix
  have hK : 0 ≤ K := by unfold K; positivity
  have hA : 0 ≤ A := by unfold A; positivity
  have hinside : (240 * K) *
      (reciprocalPhaseScale N M j X / X ^ 5 +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X) ≤ (480 * K) * A := by
    have hsum : reciprocalPhaseScale N M j X / X ^ 5 +
        1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
        1 / reciprocalPhaseScale N M j X ≤ 2 * A := by
      have hlengthTerm' : 1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤ A := hlengthTerm
      unfold A at hlengthTerm' ⊢
      linarith
    calc
      (240 * K) * (reciprocalPhaseScale N M j X / X ^ 5 +
          1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
          1 / reciprocalPhaseScale N M j X) ≤
          (240 * K) * (2 * A) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (480 * K) * A := by ring
  have hST : S ≤ T := by
    unfold S T
    exact Real.rpow_le_rpow (by positivity) hinside (by norm_num)
  refine hbase.trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hST (by positivity)) (by positivity)

/-- Long-interval low-frequency specialization of the preceding two-term
Weyl estimate. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_fixedPower_twoTerm_long
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hFlow : reciprocalPhaseScale N M j X ≤ X ^ 4)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (hXL : X ≤ (((b - a) + 1 : ℕ) : ℝ))
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let T := ((480 * ((((5 + j) ^ 5 : ℕ) : ℝ))) *
      (reciprocalPhaseScale N M j X / X ^ 5 +
        1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ)
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        ((((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * T) := by
  apply norm_reciprocalPhaseSum_le_fourStepWeyl_fixedPower_twoTerm_of_lengthTerm_le
    N M orders a b hX hF herrorSmall hM hj hLength
  · exact one_div_length_succ_pow_four_le_reciprocalPhaseTwoTermError
      N M j (b - a) hX hF hFlow hXL
  · exact haIcc
  · exact hevalY
  · exact hevalTop
  · exact hpow
  · exact hrFive
  · exact hrSix

/-- Source-facing low-frequency degree-five Weyl estimate on an arbitrary
subinterval.  Short intervals are bounded trivially; long intervals absorb
the endpoint term and use the optimized four-round estimate. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_twoTerm
    (N M : ℝ) {j : ℕ} (orders : Finset ℕ) (a b : ℕ)
    {X Y : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (hFlow : reciprocalPhaseScale N M j X ≤ X ^ 4)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X (b - a) ≤ 1)
    (hM : M ≠ 0) (hj : 2 ≤ j)
    (hLength : 1 ≤ b - a)
    (haIcc : (a : ℝ) ∈ Set.Icc X Y)
    (hevalY : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ Y)
    (hevalTop : (a : ℝ) + (b - a : ℕ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N M j X (b - a) : ℕ) ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let p := reciprocalPhaseFourStepTwoTermWidth N M j X
    ‖reciprocalPhaseSum N M j a b‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * p) := by
  dsimp only
  let L := b - a
  let K : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let R := 1 + Real.log L
  let p := reciprocalPhaseFourStepTwoTermWidth N M j X
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  have hp : 0 < p := reciprocalPhaseFourStepTwoTermWidth_pos N M hX hF
  have hK : 1 ≤ K := by
    unfold K
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 5 + j))
  have hR : 1 ≤ R := by
    have hLengthNat : 1 ≤ L := hLength
    have hLengthReal : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLengthNat
    unfold R
    have := Real.log_nonneg hLengthReal
    linarith
  have hC : 1 ≤ C := by
    unfold C
    exact_mod_cast (by omega : 1 ≤ 370 * orders.card + 173)
  by_cases hlong : X * p ≤ ((L + 1 : ℕ) : ℝ)
  · have hsource := norm_reciprocalPhaseSum_le_fourStepWeyl_fixedPower_source
      N M orders a b hX hF herrorSmall hM hj hLength haIcc hevalY hevalTop
        hpow hrFive hrSix
    have hwidth := reciprocalPhaseFourStepSourceWidth_le_twoTermWidth
      N M j L hX hF hFlow herrorSmall hlong
    refine hsource.trans ?_
    have hinnerLocal :
      (K + 1) * R * X *
          ((240 * K) *
            (reciprocalPhaseScale N M j X / X ^ 5 +
              1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
              1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ) ≤
        480 * K * ((K + 1) * R * X * p) := by
      calc
        (K + 1) * R * X *
            ((240 * K) *
              (reciprocalPhaseScale N M j X / X ^ 5 +
                1 / (((L + 1 : ℕ) : ℝ) ^ 4) +
                1 / reciprocalPhaseScale N M j X)) ^ (1 / 128 : ℝ) ≤
          (K + 1) * R * X * (480 * K * p) :=
            mul_le_mul_of_nonneg_left hwidth (by positivity)
        _ = 480 * K * ((K + 1) * R * X * p) := by ring
    apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) hC)
    simpa only [K, R, p, L, mul_assoc] using hinnerLocal
  · have hshort : ((L + 1 : ℕ) : ℝ) < X * p := lt_of_not_ge hlong
    have hLXp : (L : ℝ) ≤ X * p := by
      have hsucc : (L : ℝ) < ((L + 1 : ℕ) : ℝ) := by norm_num
      exact (hsucc.trans hshort).le
    have htrivial := norm_reciprocalPhaseSum_le_card N M j a b
    have hab : a ≤ b := by omega
    rw [Nat.card_Ico] at htrivial
    have h480K : 1 ≤ 480 * K := by nlinarith [hK]
    have hKplus : 1 ≤ K + 1 :=
      hK.trans (le_add_of_nonneg_right (by norm_num))
    have hfactor : 1 ≤ C * (480 * K * ((K + 1) * R)) :=
      one_le_mul_of_one_le_of_one_le hC
        (one_le_mul_of_one_le_of_one_le h480K
          (one_le_mul_of_one_le_of_one_le hKplus hR))
    have htarget : X * p ≤
        C * (480 * K * ((K + 1) * R * X * p)) := by
      have hnonneg : 0 ≤ X * p := mul_nonneg hX.le hp.le
      have := mul_le_mul_of_nonneg_right hfactor hnonneg
      nlinarith
    apply htrivial.trans
    apply hLXp.trans
    simpa only [C, K, R, p, L, mul_assoc] using htarget

/-- The exact product-restricted correlation has the trivial outer-block
length bound, independently of its transformed phase scale. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_blockLength
    (a b K₀ K₁ q k : ℕ) (N M : ℝ) (j : ℕ) {n n' : ℕ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') :
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M j n n'‖ ≤ (q : ℝ) := by
  rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    a b K₀ K₁ q k N M j hq hn hn']
  have htrivial := norm_reciprocalPhaseSum_le_card
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter M j n n') j
    (typeIIProductRestrictedBlockLower a K₀ q k n n')
    (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n')
  rw [Nat.card_Ico] at htrivial
  exact htrivial.trans (by
    exact_mod_cast typeIIProductRestrictedBlock_length_le
      a b K₀ K₁ q k n n')

/-- The low-frequency degree-five Weyl estimate applied to the exact
product-restricted Type II correlation interval.  Empty intersections are
handled without analytic hypotheses; on a nonempty intersection, the bundled
hypothesis records precisely the scale, critical-interval, and evaluation
conditions required by the reciprocal-phase theorem. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_twoTerm
    (a b K₀ K₁ q k : ℕ) (N M : ℝ) {j : ℕ} (orders : Finset ℕ)
    {n n' : ℕ} {X Y : ℝ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hX : 0 < X) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hanalytic :
      let N' := typeIICorrelationLinearParameter N n n'
      let M' := typeIICorrelationHigherParameter M j n n'
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      1 ≤ hi - lo →
        reciprocalPhaseScale N' M' j X ≤ X ^ 4 ∧
        reciprocalPhaseFourStepEffectiveErrorScale N' M' j X (hi - lo) ≤ 1 ∧
        (lo : ℝ) ∈ Set.Icc X Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' j X (hi - lo) : ℕ) ≤ Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' j X (hi - lo) : ℕ) ≤
          2 * X ∧
        ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    let N' := typeIICorrelationLinearParameter N n n'
    let M' := typeIICorrelationHigherParameter M j n n'
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let p := reciprocalPhaseFourStepTwoTermWidth N' M' j X
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M j n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * X * p) := by
  dsimp only
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter M j n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  have hrewrite := typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    a b K₀ K₁ q k N M j hq hn hn'
  have hM'eq : M' =
      M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j) := by rfl
  rw [hrewrite]
  change ‖reciprocalPhaseSum N' M' j lo hi‖ ≤ _
  have hM' : M' ≠ 0 := by
    rw [hM'eq]
    exact typeIICorrelationHigherParameter_ne_zero hM (by omega)
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hF' : 0 < reciprocalPhaseScale N' M' j X := by
    unfold reciprocalPhaseScale
    have hMabs : 0 < |M'| := abs_pos.mpr hM'
    have hXpow : 0 < X ^ j := pow_pos hX j
    have hterm : 0 < |M'| / X ^ j := div_pos hMabs hXpow
    positivity
  by_cases hLength : 1 ≤ hi - lo
  · rcases hanalytic hLength with
      ⟨hFlow, herrorSmall, haIcc, hevalY, hevalTop, hpow⟩
    exact norm_reciprocalPhaseSum_le_fourStepWeyl_twoTerm
      N' M' orders lo hi hX hF' hFlow herrorSmall hM' hj hLength
        haIcc hevalY hevalTop hpow hrFive hrSix
  · have hhi : hi ≤ lo := by omega
    have hzero : hi - lo = 0 := Nat.sub_eq_zero_of_le hhi
    have hIco : Finset.Ico lo hi = ∅ :=
      Finset.Ico_eq_empty_of_le hhi
    rw [reciprocalPhaseSum, hIco, hzero]
    simp only [Finset.sum_empty, norm_zero, Nat.cast_zero, Real.log_zero,
      add_zero]
    have hpnonneg :
        0 ≤ reciprocalPhaseFourStepTwoTermWidth N' M' j X :=
      (reciprocalPhaseFourStepTwoTermWidth_pos N' M' hX hF').le
    positivity

/-- Source-shaped pointwise Type II correlation bound in the equal-parameter
case.  The Weyl width is replaced by the existing distance kernel plus the
explicit high-scale error `E^(1/1024)`, so this conclusion can be fed directly
to the finite Type II summation layer. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_equalParameters
    (a b K₀ K₁ q k : ℕ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    {n n' : ℕ} {K B Y E : ℝ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hj : 2 ≤ j) (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N j n n') j K / K ^ 5 ≤ E)
    (hanalytic :
      let N' := typeIICorrelationLinearParameter N n n'
      let M' := typeIICorrelationHigherParameter N j n n'
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      1 ≤ hi - lo →
        reciprocalPhaseScale N' M' j K ≤ K ^ 4 ∧
        reciprocalPhaseFourStepEffectiveErrorScale N' M' j K (hi - lo) ≤ 1 ∧
        (lo : ℝ) ∈ Set.Icc K Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤ Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤
          2 * K ∧
        ∀ t ∈ Set.Icc K Y, t ^ (j - 1) ≤ 2 * K ^ (j - 1)) :
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let F := reciprocalPhaseScale N N j (K * B)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
            (E ^ (1 / 1024 : ℝ) +
              4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n))) := by
  dsimp only
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter N j n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  let F := reciprocalPhaseScale N N j (K * B)
  let p := reciprocalPhaseFourStepTwoTermWidth N' M' j K
  let δ : ℝ := 1 / 1024
  let J : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  have hM' : M' ≠ 0 := by
    unfold M' typeIICorrelationHigherParameter
    exact typeIICorrelationHigherParameter_ne_zero hN (by omega)
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hscale : 0 < reciprocalPhaseScale N' M' j K := by
    unfold reciprocalPhaseScale
    have hMabs : 0 < |M'| := abs_pos.mpr hM'
    have hKpow : 0 < K ^ j := pow_pos hK j
    have hterm : 0 < |M'| / K ^ j := div_pos hMabs hKpow
    positivity
  have hEnonneg : 0 ≤ E := by
    have hu : 0 ≤ reciprocalPhaseScale N' M' j K / K ^ 5 := by positivity
    exact hu.trans (by simpa only [N', M'] using hupper)
  by_cases hLength : 1 ≤ hi - lo
  · rcases hanalytic hLength with
      ⟨hFlow, herrorSmall, haIcc, hevalY, hevalTop, hpow⟩
    have hpoint :=
      norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_twoTerm
        a b K₀ K₁ q k N N orders hq hn hn' hne hK hN hj hrFive hrSix
          hanalytic
    have hwidthOne : p ≤ 1 := by
      exact reciprocalPhaseFourStepTwoTermWidth_le_one N' M' hK hscale
        (by simpa only [N', M', p] using herrorSmall)
    have hwidth : p ≤ E ^ δ + 4 * typeIIDecayKernel B F δ (Nat.dist n' n) := by
      simpa only [N', M', F, p, δ] using
        (reciprocalPhaseFourStepTwoTermWidth_typeIICorrelation_equalParameters_le
          N K B E hN hK hB hKB hj hn hn' hne hnB hn'B hwidthOne hupper)
    let Q : ℝ := C * (480 * J * ((J + 1) *
      (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K))
    have hlog : 0 ≤ Real.log ((hi - lo : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hLength
    have hQ : 0 ≤ Q := by unfold Q C J; positivity
    have hpoint' :
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤ Q * p := by
      refine hpoint.trans_eq ?_
      unfold Q C J p N' M' lo hi
      ring
    have hfinal :
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤
          Q * (E ^ δ + 4 * typeIIDecayKernel B F δ (Nat.dist n' n)) :=
      hpoint'.trans (mul_le_mul_of_nonneg_left hwidth hQ)
    convert hfinal using 1
    all_goals
      unfold Q C J F δ lo hi
      ring
  · have hhi : hi ≤ lo := by omega
    have hzero : hi - lo = 0 := Nat.sub_eq_zero_of_le hhi
    have hIco : Finset.Ico lo hi = ∅ := Finset.Ico_eq_empty_of_le hhi
    rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
      a b K₀ K₁ q k N N j hq hn hn', reciprocalPhaseSum, hIco, hzero]
    simp only [Finset.sum_empty, norm_zero, Nat.cast_zero, Real.log_zero,
      add_zero]
    have hFnonneg : 0 ≤ F := by unfold F reciprocalPhaseScale; positivity
    have hkernel : 0 ≤ typeIIDecayKernel B F δ (Nat.dist n' n) :=
      typeIIDecayKernel_nonneg δ (Nat.dist n' n) hB hFnonneg
    have hEpow : 0 ≤ E ^ δ := Real.rpow_nonneg hEnonneg δ
    have hsum : 0 ≤ E ^ δ + 4 * typeIIDecayKernel B F δ (Nat.dist n' n) := by
      positivity
    have hsumRaw : 0 ≤ E ^ (1 / 1024 : ℝ) +
        4 * typeIIDecayKernel B (reciprocalPhaseScale N N j (K * B))
          (1 / 1024 : ℝ) (Nat.dist n' n) := by
      simpa only [F, δ] using hsum
    positivity

/-- Replace the correlation-dependent logarithm in the pointwise Weyl bound
by the fixed outer block length.  This is the literal `Q * (A * kernel + E)`
shape consumed by `TypeIIKernel`. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength
    (a b K₀ K₁ q k : ℕ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    {n n' : ℕ} {K B E : ℝ}
    (hq : 0 < q) (hK : 0 ≤ K) (hB : 0 < B) (hE : 0 ≤ E)
    (hpoint :
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      let F := reciprocalPhaseScale N N j (K * B)
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤
        ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
            (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
              (E ^ (1 / 1024 : ℝ) +
                4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n)))) :
    let F := reciprocalPhaseScale N N j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (q : ℝ)) * K)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤
      Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
        E ^ (1 / 1024 : ℝ)) := by
  dsimp only at hpoint ⊢
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  let F := reciprocalPhaseScale N N j (K * B)
  let J : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  let W := E ^ (1 / 1024 : ℝ) +
    4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n)
  have hlen : hi - lo ≤ q := by
    exact typeIIProductRestrictedBlock_length_le a b K₀ K₁ q k n n'
  have hqReal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqReal
  have hloglen : 0 ≤ Real.log ((hi - lo : ℕ) : ℝ) := by
    by_cases hz : hi - lo = 0
    · simp [hz]
    · exact Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hz)
  have hlogLe : Real.log ((hi - lo : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    by_cases hz : hi - lo = 0
    · simpa [hz] using hlogq
    · apply Real.log_le_log
      · exact_mod_cast Nat.pos_of_ne_zero hz
      · exact_mod_cast hlen
  have hFnonneg : 0 ≤ F := by unfold F reciprocalPhaseScale; positivity
  have hkernel :
      0 ≤ typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) := by
    exact typeIIDecayKernel_nonneg _ _ hB hFnonneg
  have hEnonneg : 0 ≤ E ^ (1 / 1024 : ℝ) := Real.rpow_nonneg hE _
  have hW : 0 ≤ W := by unfold W; positivity
  have hfactor :
      C * (480 * J * ((J + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K)) ≤
        C * (480 * J * ((J + 1) * (1 + Real.log (q : ℝ)) * K)) := by
    gcongr
  have hpoint' :
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤
        (C * (480 * J * ((J + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K))) * W := by
    refine hpoint.trans_eq ?_
    unfold C J W F lo hi
    ring
  calc
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤
      (C * (480 * J * ((J + 1) *
        (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K))) * W := hpoint'
    _ ≤ (C * (480 * J * ((J + 1) * (1 + Real.log (q : ℝ)) * K))) * W :=
      mul_le_mul_of_nonneg_right hfactor hW
    _ = ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log (q : ℝ)) * K) *
        (4 * typeIIDecayKernel B
            (reciprocalPhaseScale N N j (K * B))
            (1 / 1024 : ℝ) (Nat.dist n' n) + E ^ (1 / 1024 : ℝ)) := by
      unfold C J W F
      ring

/-- Nearby pairs need no transformed-scale lower bound: the trivial
correlation estimate is absorbed by the source decay kernel itself. -/
theorem norm_typeIIProductRestrictedCorrelationSum_near_le_decayKernel_blockLength
    (a b K₀ K₁ q k : ℕ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    {n n' : ℕ} {K B E : ℝ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n')
    (hK : 0 < K) (hB : 0 < B) (hE : 0 ≤ E)
    (hqK : (q : ℝ) ≤ K)
    (hnear : (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N N j (K * B) / B ≤ 3) :
    let F := reciprocalPhaseScale N N j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (q : ℝ)) * K)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤
      Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
        E ^ (1 / 1024 : ℝ)) := by
  dsimp only
  let F := reciprocalPhaseScale N N j (K * B)
  let J : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  let Q : ℝ := C * (480 * J * ((J + 1) *
    (1 + Real.log (q : ℝ)) * K))
  let W : ℝ := 4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
    E ^ (1 / 1024 : ℝ)
  have htrivial := norm_typeIIProductRestrictedCorrelationSum_le_blockLength
    a b K₀ K₁ q k N N j hq hn hn'
  have hqOne : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  have hF0 : 0 ≤ F := by unfold F reciprocalPhaseScale; positivity
  have hkernel : 1 / 4 ≤
      typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) := by
    apply one_div_four_le_typeIIDecayKernel_of_scaledDistance_le_three
      (Nat.dist n' n) hB hF0
    simpa only [F] using hnear
  have hEpow : 0 ≤ E ^ (1 / 1024 : ℝ) := Real.rpow_nonneg hE _
  have hWOne : 1 ≤ W := by unfold W; nlinarith
  have hC : 1 ≤ C := by
    unfold C
    exact_mod_cast (by omega : 1 ≤ 370 * orders.card + 173)
  have hJ : 1 ≤ J := by
    unfold J
    exact_mod_cast (one_le_pow₀ (by omega : 0 < 5 + j) : 1 ≤ (5 + j) ^ 5)
  have h480J : 1 ≤ 480 * J :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hJ
  have hJplus : 1 ≤ J + 1 := by linarith
  have hlogFactor : 1 ≤ 1 + Real.log (q : ℝ) := by linarith
  have htail : 1 ≤ (J + 1) * (1 + Real.log (q : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hJplus hlogFactor
  have hmiddle : 1 ≤ 480 * J *
      ((J + 1) * (1 + Real.log (q : ℝ))) :=
    one_le_mul_of_one_le_of_one_le h480J htail
  have hcoefficient : 1 ≤ C *
      (480 * J * ((J + 1) * (1 + Real.log (q : ℝ)))) :=
    one_le_mul_of_one_le_of_one_le hC hmiddle
  have hQ0 : 0 ≤ Q := by unfold Q; positivity
  have hKQ : K ≤ Q := by
    have hmul := mul_le_mul_of_nonneg_right hcoefficient hK.le
    calc
      K = 1 * K := by ring
      _ ≤ (C * (480 * J * ((J + 1) *
          (1 + Real.log (q : ℝ))))) * K := hmul
      _ = Q := by unfold Q; ring
  have hQW : Q ≤ Q * W := by
    have hprod := mul_nonneg hQ0 (sub_nonneg.mpr hWOne)
    nlinarith
  calc
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N j n n'‖ ≤ (q : ℝ) := htrivial
    _ ≤ K := hqK
    _ ≤ Q := hKQ
    _ ≤ Q * W := hQW
    _ = ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log (q : ℝ)) * K) *
        (4 * typeIIDecayKernel B
            (reciprocalPhaseScale N N j (K * B))
            (1 / 1024 : ℝ) (Nat.dist n' n) + E ^ (1 / 1024 : ℝ)) := by
      unfold Q W C J F
      ring

/-- The equal-parameter four-step Weyl estimate propagated through the exact
Vaughan double-block Type II reduction.  All pointwise correlations are now
supplied by the analytic Weyl theorem; the conclusion is the endpoint-free
source-scale kernel sum with explicit exponent `1/1024`. -/
theorem sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_fourStepWeyl_equalParameters
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    (Bouter Binner qouter qinner kouter kinner : ℕ)
    {L K B Y E : ℝ}
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hBinner : (Binner : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N j (K * B)) (hE : 0 ≤ E)
    (hj : 2 ≤ j) (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N j n n') j K / K ^ 5 ≤ E)
    (hanalytic : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
        let N' := typeIICorrelationLinearParameter N n n'
        let M' := typeIICorrelationHigherParameter N j n n'
        let lo := typeIIProductRestrictedBlockLower a 1 qouter kouter n n'
        let hi := typeIIProductRestrictedBlockUpper b 1 (Bouter + 1)
          qouter kouter n n'
        1 ≤ hi - lo →
          reciprocalPhaseScale N' M' j K ≤ K ^ 4 ∧
          reciprocalPhaseFourStepEffectiveErrorScale N' M' j K (hi - lo) ≤ 1 ∧
          (lo : ℝ) ∈ Set.Icc K Y ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤ Y ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤
            2 * K ∧
          ∀ t ∈ Set.Icc K Y, t ^ (j - 1) ≤ 2 * K ^ (j - 1)) :
    let F := reciprocalPhaseScale N N j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock 1 (Bouter + 1) qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock 1 (Binner + 1) qinner kinner)
          γ N N j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  dsimp only
  let F := reciprocalPhaseScale N N j (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
      (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hpoint : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock 1 (Bouter + 1) qouter kouter)
          N N j n n'‖ ≤
        Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + E ^ δ) := by
    intro n hnmem n' hn'mem hne
    have hnData := (mem_shortIntervalBlock.mp hnmem)
    have hn'Data := (mem_shortIntervalBlock.mp hn'mem)
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnUpper : n ≤ Binner := by omega
    have hn'Upper : n' ≤ Binner := by omega
    have hnCast : (n : ℝ) ≤ (Binner : ℝ) := by exact_mod_cast hnUpper
    have hn'Cast : (n' : ℝ) ≤ (Binner : ℝ) := by exact_mod_cast hn'Upper
    have hnB : (n : ℝ) ≤ B := hnCast.trans hBinner
    have hn'B : (n' : ℝ) ≤ B := hn'Cast.trans hBinner
    have hraw :=
      norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_equalParameters
        a b 1 (Bouter + 1) qouter kouter N orders hqouter hnpos hn'pos hne
          hN hK hB hKB hj hnB hn'B hrFive hrSix
          (hupper n hnmem n' hn'mem hne)
          (hanalytic n hnmem n' hn'mem hne)
    have huniform :=
      norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength
        a b 1 (Bouter + 1) qouter kouter N orders hqouter hK.le hB hE hraw
    simpa only [F, Q, δ] using huniform
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_sourceScale_blockLengths
      (Finset.Ico a b) γ N N j Bouter Binner qouter qinner kouter kinner
      hqouter hqinner hL hγ hQ (by norm_num : (0 : ℝ) ≤ 4)
      (Real.rpow_nonneg hE _) hB hF (by norm_num : (0 : ℝ) ≤ 1 / 1024)
      (by norm_num : (1 / 1024 : ℝ) < 1) hqinnerB hpoint
  simpa only [F, Q, δ] using hresult

/-- Equal-parameter four-step Weyl estimate propagated through two arbitrary
positive short blocks.  Unlike the earlier `[1,B]` convenience wrapper, this
statement applies directly to the dyadic blocks in the canonical Vaughan
family. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_fourStepWeyl_equalParameters
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B Y E : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hS₁ : (S₁ : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N j (K * B)) (hE : 0 ≤ E)
    (hj : 2 ≤ j) (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N j n n') j K / K ^ 5 ≤ E)
    (hanalytic : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        let N' := typeIICorrelationLinearParameter N n n'
        let M' := typeIICorrelationHigherParameter N j n n'
        let lo := typeIIProductRestrictedBlockLower a K₀ qouter kouter n n'
        let hi := typeIIProductRestrictedBlockUpper b K₀ K₁
          qouter kouter n n'
        1 ≤ hi - lo →
          reciprocalPhaseScale N' M' j K ≤ K ^ 4 ∧
          reciprocalPhaseFourStepEffectiveErrorScale N' M' j K (hi - lo) ≤ 1 ∧
          (lo : ℝ) ∈ Set.Icc K Y ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤ Y ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤
            2 * K ∧
          ∀ t ∈ Set.Icc K Y, t ^ (j - 1) ≤ 2 * K ^ (j - 1)) :
    let F := reciprocalPhaseScale N N j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N N j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  dsimp only
  let F := reciprocalPhaseScale N N j (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
      (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hpoint : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ qouter kouter)
          N N j n n'‖ ≤
        Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + E ^ δ) := by
    intro n hnmem n' hn'mem hne
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnUpper : n ≤ S₁ := by omega
    have hn'Upper : n' ≤ S₁ := by omega
    have hnCast : (n : ℝ) ≤ (S₁ : ℝ) := by exact_mod_cast hnUpper
    have hn'Cast : (n' : ℝ) ≤ (S₁ : ℝ) := by exact_mod_cast hn'Upper
    have hnB : (n : ℝ) ≤ B := hnCast.trans hS₁
    have hn'B : (n' : ℝ) ≤ B := hn'Cast.trans hS₁
    have hraw :=
      norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_equalParameters
        a b K₀ K₁ qouter kouter N orders hqouter hnpos hn'pos hne
          hN hK hB hKB hj hnB hn'B hrFive hrSix
          (hupper n hnmem n' hn'mem hne)
          (hanalytic n hnmem n' hn'mem hne)
    have huniform :=
      norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength
        a b K₀ K₁ qouter kouter N orders hqouter hK.le hB hE hraw
    simpa only [F, Q, δ] using huniform
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_sourceScale_blockLengths
      (Finset.Ico a b) γ N N j K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hQ (by norm_num : (0 : ℝ) ≤ 4)
      (Real.rpow_nonneg hE _) hB hF (by norm_num : (0 : ℝ) ≤ 1 / 1024)
      (by norm_num : (1 / 1024 : ℝ) < 1) hqinnerB hpoint
  simpa only [F, Q, δ] using hresult

/-- Equal-parameter Type II propagation after the far-pair estimate has been
proved by any analytic method. Nearby pairs are bounded trivially and absorbed
by the decay kernel. This is the common aggregation layer for the source's
pairwise Weyl/Vinogradov split. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_nearFar_of_farBound
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B E : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hK : 0 < K) (hB : 0 < B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N j (K * B)) (hE : 0 ≤ E)
    (hqouterK : (qouter : ℝ) ≤ K)
    (hfarBound : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N j (K * B) / B →
        let F := reciprocalPhaseScale N N j (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
            (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N N j n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            E ^ (1 / 1024 : ℝ))) :
    let F := reciprocalPhaseScale N N j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N N j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  dsimp only
  let F := reciprocalPhaseScale N N j (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
      (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hpoint : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ qouter kouter)
          N N j n n'‖ ≤
        Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + E ^ δ) := by
    intro n hnmem n' hn'mem hne
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    by_cases hnear : (Nat.dist n' n : ℝ) *
        reciprocalPhaseScale N N j (K * B) / B ≤ 3
    · have hnearBound :=
        norm_typeIIProductRestrictedCorrelationSum_near_le_decayKernel_blockLength
          a b K₀ K₁ qouter kouter N orders hqouter hnpos hn'pos
            hK hB hE hqouterK hnear
      simpa only [F, Q, δ] using hnearBound
    · have hfar : 3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N j (K * B) / B :=
        (lt_of_not_ge hnear).le
      simpa only [F, Q, δ] using hfarBound n hnmem n' hn'mem hne hfar
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_sourceScale_blockLengths
      (Finset.Ico a b) γ N N j K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hQ (by norm_num : (0 : ℝ) ≤ 4)
      (Real.rpow_nonneg hE _) hB hF (by norm_num : (0 : ℝ) ≤ 1 / 1024)
      (by norm_num : (1 / 1024 : ℝ) < 1) hqinnerB hpoint
  simpa only [F, Q, δ] using hresult

/-- Additive-error form of the common near/far aggregation theorem.  This is
the natural endpoint when different analytic branches contribute different
errors, such as the Weyl `E^(1/1024)` term and a Vinogradov logarithmic term. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_nearFar_of_farBound_additiveError
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B Z : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hK : 0 < K) (hB : 0 < B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N j (K * B)) (hZ : 0 ≤ Z)
    (hqouterK : (qouter : ℝ) ≤ K)
    (hfarBound : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N j (K * B) / B →
        let F := reciprocalPhaseScale N N j (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
            (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N N j n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + Z)) :
    let F := reciprocalPhaseScale N N j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N N j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * Z))) := by
  dsimp only
  let F := reciprocalPhaseScale N N j (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
      (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hpoint : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ qouter kouter)
          N N j n n'‖ ≤
        Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + Z) := by
    intro n hnmem n' hn'mem hne
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    by_cases hnear : (Nat.dist n' n : ℝ) *
        reciprocalPhaseScale N N j (K * B) / B ≤ 3
    · have hnearZero :=
        norm_typeIIProductRestrictedCorrelationSum_near_le_decayKernel_blockLength
          a b K₀ K₁ qouter kouter N orders (E := (0 : ℝ))
            hqouter hnpos hn'pos hK hB (by norm_num) hqouterK hnear
      have hbase :
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (shortIntervalBlock K₀ K₁ qouter kouter) N N j n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n)) := by
        simpa only [F, Q, δ, Real.zero_rpow (by norm_num : (1 / 1024 : ℝ) ≠ 0),
          add_zero] using hnearZero
      exact hbase.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right hZ) hQ)
    · have hfar : 3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N j (K * B) / B :=
        (lt_of_not_ge hnear).le
      simpa only [F, Q, δ] using hfarBound n hnmem n' hn'mem hne hfar
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_sourceScale_blockLengths
      (Finset.Ico a b) γ N N j K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hQ (by norm_num : (0 : ℝ) ≤ 4)
      hZ hB hF (by norm_num : (0 : ℝ) ≤ 1 / 1024)
      (by norm_num : (1 / 1024 : ℝ) < 1) hqinnerB hpoint
  simpa only [F, Q, δ] using hresult

/-- Equal-parameter Type II propagation with the source-faithful distance
split.  Nearby pairs are bounded trivially and absorbed by the decay kernel;
only pairs with scaled distance at least three must satisfy the Weyl analytic
hypotheses. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_fourStepWeyl_nearFar
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B Y E : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hS₁ : (S₁ : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N j (K * B)) (hE : 0 ≤ E)
    (hqouterK : (qouter : ℝ) ≤ K)
    (hj : 2 ≤ j) (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N j n n') j K / K ^ 5 ≤ E)
    (hanalyticFar : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N j (K * B) / B →
        let N' := typeIICorrelationLinearParameter N n n'
        let M' := typeIICorrelationHigherParameter N j n n'
        let lo := typeIIProductRestrictedBlockLower a K₀ qouter kouter n n'
        let hi := typeIIProductRestrictedBlockUpper b K₀ K₁
          qouter kouter n n'
        1 ≤ hi - lo →
          reciprocalPhaseScale N' M' j K ≤ K ^ 4 ∧
          reciprocalPhaseFourStepEffectiveErrorScale N' M' j K (hi - lo) ≤ 1 ∧
          (lo : ℝ) ∈ Set.Icc K Y ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤ Y ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤
            2 * K ∧
          ∀ t ∈ Set.Icc K Y, t ^ (j - 1) ≤ 2 * K ^ (j - 1)) :
    let F := reciprocalPhaseScale N N j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N N j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  dsimp only
  let F := reciprocalPhaseScale N N j (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
      (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hpoint : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ qouter kouter)
          N N j n n'‖ ≤
        Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + E ^ δ) := by
    intro n hnmem n' hn'mem hne
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    by_cases hnear : (Nat.dist n' n : ℝ) *
        reciprocalPhaseScale N N j (K * B) / B ≤ 3
    · have hnearBound :=
        norm_typeIIProductRestrictedCorrelationSum_near_le_decayKernel_blockLength
          a b K₀ K₁ qouter kouter N orders hqouter hnpos hn'pos
            hK hB hE hqouterK hnear
      simpa only [F, Q, δ] using hnearBound
    · have hfar : 3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N j (K * B) / B :=
        (lt_of_not_ge hnear).le
      have hnUpper : n ≤ S₁ := by omega
      have hn'Upper : n' ≤ S₁ := by omega
      have hnCast : (n : ℝ) ≤ (S₁ : ℝ) := by exact_mod_cast hnUpper
      have hn'Cast : (n' : ℝ) ≤ (S₁ : ℝ) := by exact_mod_cast hn'Upper
      have hnB : (n : ℝ) ≤ B := hnCast.trans hS₁
      have hn'B : (n' : ℝ) ≤ B := hn'Cast.trans hS₁
      have hraw :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_equalParameters
          a b K₀ K₁ qouter kouter N orders hqouter hnpos hn'pos hne
            hN hK hB hKB hj hnB hn'B hrFive hrSix
            (hupper n hnmem n' hn'mem hne)
            (hanalyticFar n hnmem n' hn'mem hne hfar)
      have huniform :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength
          a b K₀ K₁ qouter kouter N orders hqouter hK.le hB hE hraw
      simpa only [F, Q, δ] using huniform
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_sourceScale_blockLengths
      (Finset.Ico a b) γ N N j K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hQ (by norm_num : (0 : ℝ) ≤ 4)
      (Real.rpow_nonneg hE _) hB hF (by norm_num : (0 : ℝ) ≤ 1 / 1024)
      (by norm_num : (1 / 1024 : ℝ) < 1) hqinnerB hpoint
  simpa only [F, Q, δ] using hresult

/-- The degree-five normalization converts `F/K^5 ≤ 1/K` into the low-scale
condition `F ≤ K^4`. -/
theorem le_pow_four_of_div_pow_five_le_one_div
    {F K : ℝ} (hK : 0 < K) (hFK : F / K ^ 5 ≤ 1 / K) :
    F ≤ K ^ 4 := by
  have hmul := mul_le_mul_of_nonneg_right hFK (pow_nonneg hK.le 5)
  calc
    F = (F / K ^ 5) * K ^ 5 := by field_simp
    _ ≤ (1 / K) * K ^ 5 := hmul
    _ = K ^ 4 := by field_simp

/-- The converse degree-five normalization: a transformed scale in the
four-step Weyl range contributes at most `1/K` to its high-scale error. -/
theorem div_pow_five_le_one_div_of_le_pow_four
    {F K : ℝ} (hK : 0 < K) (hFK : F ≤ K ^ 4) :
    F / K ^ 5 ≤ 1 / K := by
  calc
    F / K ^ 5 ≤ K ^ 4 / K ^ 5 :=
      div_le_div_of_nonneg_right hFK (pow_nonneg hK.le 5)
    _ = 1 / K := by field_simp

/-- Uniformly bound the complete four-step effective error from bounds for its
high-scale and inverse-scale terms.  A nonempty interval contributes at most
`1/16` through the remaining length term. -/
theorem reciprocalPhaseFourStepEffectiveErrorScale_le_of_scale_bounds
    (N M K E R : ℝ) (j L : ℕ)
    (hupper : reciprocalPhaseScale N M j K / K ^ 5 ≤ E)
    (hinv : 1 / reciprocalPhaseScale N M j K ≤ R)
    (hLength : 1 ≤ L) :
    reciprocalPhaseFourStepEffectiveErrorScale N M j K L ≤
      240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) * E + 1 / 16 + R := by
  let C : ℝ := 240 * ((((5 + j) ^ 5 : ℕ) : ℝ))
  have hC : 0 ≤ C := by unfold C; positivity
  have hfirstRaw := mul_le_mul_of_nonneg_left hupper hC
  have hfirst : C * reciprocalPhaseScale N M j K / K ^ 5 ≤ C * E := by
    calc
      C * reciprocalPhaseScale N M j K / K ^ 5 =
          C * (reciprocalPhaseScale N M j K / K ^ 5) := by ring
      _ ≤ C * E := hfirstRaw
  have htwoNat : 2 ≤ L + 1 := by omega
  have htwo : (2 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast htwoNat
  have hpowRaw := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 4
  have hpow : (16 : ℝ) ≤ (((L + 1 : ℕ) : ℝ) ^ 4) := by
    norm_num at hpowRaw ⊢
    exact hpowRaw
  have hlength : 1 / (((L + 1 : ℕ) : ℝ) ^ 4) ≤ (1 : ℝ) / 16 :=
    one_div_le_one_div_of_le (by norm_num) hpow
  rw [reciprocalPhaseFourStepEffectiveErrorScale_eq]
  unfold C at hfirst
  linarith

/-- A uniform upper bound for the effective error gives the corresponding
uniform upper bound for the floor-rounded optimized differencing range. -/
theorem reciprocalPhaseFourStepOptimizedRange_cast_le_of_error_bound
    (N M : ℝ) {j L : ℕ} {X E : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herror : reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ E) :
    (reciprocalPhaseFourStepOptimizedRange N M j X L : ℝ) ≤
      (L : ℝ) * E ^ (1 / 128 : ℝ) := by
  have hwidth : reciprocalPhaseFourStepCriticalWidth N M j X L ≤
      E ^ (1 / 128 : ℝ) := by
    unfold reciprocalPhaseFourStepCriticalWidth
    exact Real.rpow_le_rpow
      (reciprocalPhaseFourStepEffectiveErrorScale_pos N M hX hF).le
      herror (by norm_num)
  exact (reciprocalPhaseFourStepOptimizedRange_cast_le N M hX hF).trans
    (mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg L))

/-- Pair-independent effective-error majorant for an equal-parameter Type II
short block. -/
noncomputable def typeIIShortIntervalEffectiveErrorBound
    (N K B : ℝ) (j q k : ℕ) : ℝ :=
  240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
      typeIIShortIntervalScaleError N N K B j q k + 1 / 16 +
    2 * B / reciprocalPhaseScale N N j (K * B)

/-- Pair-independent effective-error majorant for an equal-parameter short
block with arbitrary initial endpoint. -/
noncomputable def typeIIShortIntervalEffectiveErrorBoundAt
    (N K B : ℝ) (j S₀ q k : ℕ) : ℝ :=
  240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
      typeIIShortIntervalScaleErrorAt N N K B j S₀ q k + 1 / 16 +
    2 * B / reciprocalPhaseScale N N j (K * B)

/-- Split the scalar effective-error condition into independent upper-scale
and inverse-scale budgets.  The fixed interval-length contribution occupies
the remaining `1/16`. -/
theorem typeIIShortIntervalEffectiveErrorBoundAt_le_one_of_terms
    (N K B : ℝ) (j S₀ q k : ℕ)
    (hscale : 240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        typeIIShortIntervalScaleErrorAt N N K B j S₀ q k ≤ 7 / 16)
    (hinv : 2 * B / reciprocalPhaseScale N N j (K * B) ≤ 1 / 2) :
    typeIIShortIntervalEffectiveErrorBoundAt N K B j S₀ q k ≤ 1 := by
  unfold typeIIShortIntervalEffectiveErrorBoundAt
  linarith

/-- Far Type II pairs have a small inverse transformed-scale term directly
from their source-scaled distance.  Thus a `1/4` budget for the uniform
upper-scale error suffices for the complete four-step effective error. -/
theorem reciprocalPhaseFourStepEffectiveErrorScale_typeIICorrelation_le_one_of_far
    (N K B E : ℝ) {j L n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B) (hj : 1 ≤ j)
    (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hupper : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N j n n') j K / K ^ 5 ≤ E)
    (hscaleBudget : 240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) * E ≤ 1 / 4)
    (hLength : 1 ≤ L)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N N j (K * B) / B) :
    reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N j n n') j K L ≤ 1 := by
  have hinv :=
    one_div_typeIICorrelationScale_le_two_thirds_of_three_le_scaledDistance
      N K B hK hB hKB hj hn hn' hnB hn'B hfar
  have hraw := reciprocalPhaseFourStepEffectiveErrorScale_le_of_scale_bounds
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter N j n n') K E (2 / 3) j L
    hupper hinv hLength
  calc
    reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N j n n') j K L ≤
      240 * ((((5 + j) ^ 5 : ℕ) : ℝ)) * E + 1 / 16 + 2 / 3 := hraw
    _ ≤ 1 := by linarith

/-- A `1/K` upper-scale error automatically receives a `1/4` budget once
the outer scale dominates four times its fixed Weyl coefficient. -/
theorem mul_error_le_one_div_four_of_error_le_one_div
    {C E K : ℝ} (hC : 0 ≤ C) (hK : 0 < K)
    (hE : E ≤ 1 / K) (hCK : 4 * C ≤ K) :
    C * E ≤ 1 / 4 := by
  have hmul : C * E ≤ C * (1 / K) :=
    mul_le_mul_of_nonneg_left hE hC
  have hdiv : C / K ≤ 1 / 4 := by
    rw [div_le_iff₀ hK]
    nlinarith
  calc
    C * E ≤ C * (1 / K) := hmul
    _ = C / K := by ring
    _ ≤ 1 / 4 := hdiv

/-- If an effective error is at most one, the elementary relative-width
condition `5q ≤ K` leaves room for the four-step expansion. -/
theorem fourStepExpansionMargin_le_of_five_mul_le
    {q K E : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hq0 : 0 ≤ q)
    (hqK : 5 * q ≤ K) :
    q + 4 * q * E ^ (1 / 128 : ℝ) ≤ K := by
  have hpow : E ^ (1 / 128 : ℝ) ≤ 1 :=
    Real.rpow_le_one hE0 hE1 (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4 * q)
  nlinarith

/-- For the quadratic phase used in Tao's final specialization, all interval
evaluation conditions follow from fitting the four-step expansion inside the
outer short block. -/
theorem typeIIProductRestrictedBlock_quadratic_fourStep_geometry
    (a b Bouter q k n n' : ℕ) (N' M' K : ℝ)
    (hK : K = ((1 + k * q : ℕ) : ℝ))
    (hLength : 1 ≤ typeIIProductRestrictedBlockUpper b 1 (Bouter + 1)
        q k n n' - typeIIProductRestrictedBlockLower a 1 q k n n')
    (hmargin : (q : ℝ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K
          (typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) q k n n' -
            typeIIProductRestrictedBlockLower a 1 q k n n') : ℕ) ≤ K) :
    let lo := typeIIProductRestrictedBlockLower a 1 q k n n'
    let hi := typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) q k n n'
    (lo : ℝ) ∈ Set.Icc K (2 * K) ∧
      (lo : ℝ) + (hi - lo : ℕ) +
          (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
        2 * K ∧
      ∀ t ∈ Set.Icc K (2 * K), t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
  dsimp only
  let lo := typeIIProductRestrictedBlockLower a 1 q k n n'
  let hi := typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) q k n n'
  let H := reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo)
  have hloNat : 1 + k * q ≤ lo := by
    unfold lo typeIIProductRestrictedBlockLower
    exact le_max_left _ _
  have hiNat : hi ≤ 1 + k * q + q := by
    unfold hi typeIIProductRestrictedBlockUpper
    calc
      min (min (Bouter + 1) (1 + (k + 1) * q))
          (min (b ⌈/⌉ n) (b ⌈/⌉ n')) ≤ 1 + (k + 1) * q :=
        (min_le_left _ _).trans (min_le_right _ _)
      _ = 1 + k * q + q := by rw [Nat.add_mul]; simp only [one_mul, Nat.add_assoc]
  have hlohi : lo ≤ hi := by omega
  have hjoinNat : lo + (hi - lo) = hi := by omega
  have hlo : K ≤ (lo : ℝ) := by
    rw [hK]
    exact_mod_cast hloNat
  have hiUpper : (hi : ℝ) ≤ K + q := by
    rw [hK]
    exact_mod_cast hiNat
  have hjoin : (lo : ℝ) + (hi - lo : ℕ) = (hi : ℝ) := by
    exact_mod_cast hjoinNat
  have hend : (lo : ℝ) + (hi - lo : ℕ) + (4 * H : ℕ) ≤ 2 * K := by
    have hmargin' : (q : ℝ) + (4 * H : ℕ) ≤ K := by
      simpa only [lo, hi, H] using hmargin
    rw [hjoin]
    have hstep : (hi : ℝ) + (4 * H : ℕ) ≤
        (K + (q : ℝ)) + (4 * H : ℕ) :=
      add_le_add hiUpper le_rfl
    exact hstep.trans (by linarith)
  have hloUpper : (lo : ℝ) ≤ 2 * K := by
    calc
      (lo : ℝ) ≤ (lo : ℝ) + (hi - lo : ℕ) + (4 * H : ℕ) := by
        have h₁ : (0 : ℝ) ≤ (hi - lo : ℕ) := by positivity
        have h₂ : (0 : ℝ) ≤ (4 * H : ℕ) := by positivity
        linarith
      _ ≤ 2 * K := hend
  refine ⟨⟨hlo, hloUpper⟩, ?_, ?_⟩
  · simpa only [lo, hi, H] using hend
  · intro t ht
    norm_num
    exact ht.2

/-- Arbitrary-endpoint version of the quadratic outer-block geometry lemma.
This is the literal form needed by a dyadic Vaughan block. -/
theorem typeIIProductRestrictedBlock_quadratic_fourStep_geometryAt
    (a b K₀ K₁ q k n n' : ℕ) (N' M' K : ℝ)
    (hK : K = ((K₀ + k * q : ℕ) : ℝ))
    (hLength : 1 ≤ typeIIProductRestrictedBlockUpper b K₀ K₁
        q k n n' - typeIIProductRestrictedBlockLower a K₀ q k n n')
    (hmargin : (q : ℝ) +
        (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n') : ℕ) ≤ K) :
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    (lo : ℝ) ∈ Set.Icc K (2 * K) ∧
      (lo : ℝ) + (hi - lo : ℕ) +
          (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
        2 * K ∧
      ∀ t ∈ Set.Icc K (2 * K), t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
  dsimp only
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  let H := reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo)
  have hloNat : K₀ + k * q ≤ lo := by
    unfold lo typeIIProductRestrictedBlockLower
    exact le_max_left _ _
  have hiNat : hi ≤ K₀ + k * q + q := by
    unfold hi typeIIProductRestrictedBlockUpper
    calc
      min (min K₁ (K₀ + (k + 1) * q))
          (min (b ⌈/⌉ n) (b ⌈/⌉ n')) ≤ K₀ + (k + 1) * q :=
        (min_le_left _ _).trans (min_le_right _ _)
      _ = K₀ + k * q + q := by rw [Nat.add_mul]; simp only [one_mul, Nat.add_assoc]
  have hlohi : lo ≤ hi := by omega
  have hjoinNat : lo + (hi - lo) = hi := by omega
  have hlo : K ≤ (lo : ℝ) := by
    rw [hK]
    exact_mod_cast hloNat
  have hiUpper : (hi : ℝ) ≤ K + q := by
    rw [hK]
    exact_mod_cast hiNat
  have hjoin : (lo : ℝ) + (hi - lo : ℕ) = (hi : ℝ) := by
    exact_mod_cast hjoinNat
  have hend : (lo : ℝ) + (hi - lo : ℕ) + (4 * H : ℕ) ≤ 2 * K := by
    have hmargin' : (q : ℝ) + (4 * H : ℕ) ≤ K := by
      simpa only [lo, hi, H] using hmargin
    rw [hjoin]
    have hstep : (hi : ℝ) + (4 * H : ℕ) ≤
        (K + (q : ℝ)) + (4 * H : ℕ) :=
      add_le_add hiUpper le_rfl
    exact hstep.trans (by linarith)
  have hloUpper : (lo : ℝ) ≤ 2 * K := by
    calc
      (lo : ℝ) ≤ (lo : ℝ) + (hi - lo : ℕ) + (4 * H : ℕ) := by
        have h₁ : (0 : ℝ) ≤ (hi - lo : ℕ) := by positivity
        have h₂ : (0 : ℝ) ≤ (4 * H : ℕ) := by positivity
        linarith
      _ ≤ 2 * K := hend
  refine ⟨⟨hlo, hloUpper⟩, ?_, ?_⟩
  · simpa only [lo, hi, H] using hend
  · intro t ht
    norm_num
    exact ht.2

/-- The full equal-parameter Type II estimate with the high-scale error
discharged uniformly from the inner short block's support and diameter.  The
remaining hypotheses are precisely the analytic critical-interval and
evaluation conditions needed by the four-step Weyl estimate. -/
theorem sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_fourStepWeyl_productScale
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) {j : ℕ} (orders : Finset ℕ)
    (Bouter Binner qouter qinner kouter kinner : ℕ)
    {L K B Y : ℝ}
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hBinner : (Binner : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N j (K * B))
    (hj : 2 ≤ j) (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hanalytic : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
        let N' := typeIICorrelationLinearParameter N n n'
        let M' := typeIICorrelationHigherParameter N j n n'
        let lo := typeIIProductRestrictedBlockLower a 1 qouter kouter n n'
        let hi := typeIIProductRestrictedBlockUpper b 1 (Bouter + 1)
          qouter kouter n n'
        1 ≤ hi - lo →
          reciprocalPhaseScale N' M' j K ≤ K ^ 4 ∧
          reciprocalPhaseFourStepEffectiveErrorScale N' M' j K (hi - lo) ≤ 1 ∧
          (lo : ℝ) ∈ Set.Icc K Y ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤ Y ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' j K (hi - lo) : ℕ) ≤
            2 * K ∧
          ∀ t ∈ Set.Icc K Y, t ^ (j - 1) ≤ 2 * K ^ (j - 1)) :
    let E := typeIIShortIntervalScaleError N N K B j qinner kinner
    let F := reciprocalPhaseScale N N j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock 1 (Bouter + 1) qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock 1 (Binner + 1) qinner kinner)
          γ N N j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  dsimp only
  let E := typeIIShortIntervalScaleError N N K B j qinner kinner
  have hE : 0 ≤ E := by
    unfold E typeIIShortIntervalScaleError
    positivity
  have hupper : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N j n n') j K / K ^ 5 ≤ E := by
    intro n hnmem n' hn'mem _
    simpa only [E] using
      (reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_shortInterval
        N N K B (by omega : 1 ≤ j) hK hqinner hBinner hnmem hn'mem)
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_fourStepWeyl_equalParameters
      a b γ N orders Bouter Binner qouter qinner kouter kinner
      hqouter hqinner hL hγ hN hK hB hKB hBinner hqinnerB hF hE
      hj hrFive hrSix hupper hanalytic
  simpa only [E] using hresult

/-- Source-oriented quadratic Type II wrapper.  Naming `K` as the literal
outer-block left endpoint and fitting the optimized four-step expansion in
that block automatically discharges every endpoint and power-evaluation
condition from the analytic bundle. -/
theorem sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_fourStepWeyl_quadratic
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (Bouter Binner qouter qinner kouter kinner : ℕ)
    {L K B : ℝ}
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hKouter : K = ((1 + kouter * qouter : ℕ) : ℝ))
    (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hBinner : (Binner : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hscaleError : typeIIShortIntervalScaleError N N K B 2 qinner kinner ≤ 1 / K)
    (herrorScale : typeIIShortIntervalEffectiveErrorBound
      N K B 2 qinner kinner ≤ 1)
    (hqouterK : 5 * (qouter : ℝ) ≤ K) :
    let E := typeIIShortIntervalScaleError N N K B 2 qinner kinner
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock 1 (Bouter + 1) qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock 1 (Binner + 1) qinner kinner)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  have hK : 0 < K := by rw [hKouter]; positivity
  have hG0 : 0 ≤ typeIIShortIntervalEffectiveErrorBound
      N K B 2 qinner kinner := by
    unfold typeIIShortIntervalEffectiveErrorBound typeIIShortIntervalScaleError
    have hsource : 0 < reciprocalPhaseScale N N 2 (K * B) :=
      zero_lt_one.trans_le hF
    positivity
  have hmarginScale : (qouter : ℝ) + 4 * (qouter : ℝ) *
      typeIIShortIntervalEffectiveErrorBound N K B 2 qinner kinner ^
        (1 / 128 : ℝ) ≤ K :=
    fourStepExpansionMargin_le_of_five_mul_le hG0 herrorScale
      (Nat.cast_nonneg qouter) hqouterK
  have hanalytic : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
        let N' := typeIICorrelationLinearParameter N n n'
        let M' := typeIICorrelationHigherParameter N 2 n n'
        let lo := typeIIProductRestrictedBlockLower a 1 qouter kouter n n'
        let hi := typeIIProductRestrictedBlockUpper b 1 (Bouter + 1)
          qouter kouter n n'
        1 ≤ hi - lo →
          reciprocalPhaseScale N' M' 2 K ≤ K ^ 4 ∧
          reciprocalPhaseFourStepEffectiveErrorScale N' M' 2 K (hi - lo) ≤ 1 ∧
          (lo : ℝ) ∈ Set.Icc K (2 * K) ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
            2 * K ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
            2 * K ∧
          ∀ t ∈ Set.Icc K (2 * K), t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
    intro n hnmem n' hn'mem hne
    dsimp only
    intro hLength
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnUpper : n ≤ Binner := by omega
    have hn'Upper : n' ≤ Binner := by omega
    have hnUpperReal : (n : ℝ) ≤ (Binner : ℝ) := by exact_mod_cast hnUpper
    have hn'UpperReal : (n' : ℝ) ≤ (Binner : ℝ) := by exact_mod_cast hn'Upper
    have hnB : (n : ℝ) ≤ B := by
      exact hnUpperReal.trans hBinner
    have hn'B : (n' : ℝ) ≤ B := by
      exact hn'UpperReal.trans hBinner
    have hpairScale : reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K / K ^ 5 ≤
        typeIIShortIntervalScaleError N N K B 2 qinner kinner :=
      reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_shortInterval
        N N K B (by norm_num) hK hqinner hBinner hnmem hn'mem
    have hscale' : reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K ≤ K ^ 4 :=
      le_pow_four_of_div_pow_five_le_one_div hK (hpairScale.trans hscaleError)
    have hinv : 1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K ≤
        2 * B / reciprocalPhaseScale N N 2 (K * B) :=
      one_div_typeIICorrelationScale_le_two_mul_B_div_sourceScale
        N K B hK hB hKB (by norm_num) hnpos hn'pos hne hnB hn'B
          (zero_lt_one.trans_le hF)
    have herrorBound : reciprocalPhaseFourStepEffectiveErrorScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) qouter kouter n n' -
            typeIIProductRestrictedBlockLower a 1 qouter kouter n n') ≤
        typeIIShortIntervalEffectiveErrorBound N K B 2 qinner kinner := by
      simpa only [typeIIShortIntervalEffectiveErrorBound] using
        (reciprocalPhaseFourStepEffectiveErrorScale_le_of_scale_bounds
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') K
        (typeIIShortIntervalScaleError N N K B 2 qinner kinner)
        (2 * B / reciprocalPhaseScale N N 2 (K * B)) 2 _
        hpairScale hinv hLength)
    have herror' : reciprocalPhaseFourStepEffectiveErrorScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) qouter kouter n n' -
            typeIIProductRestrictedBlockLower a 1 qouter kouter n n') ≤ 1 :=
      herrorBound.trans herrorScale
    have hM' : typeIICorrelationHigherParameter N 2 n n' ≠ 0 :=
      typeIICorrelationHigherParameter_ne_zero hN (by norm_num)
        (Nat.ne_of_gt hnpos) (Nat.ne_of_gt hn'pos) hne
    have hF' : 0 < reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K := by
      unfold reciprocalPhaseScale
      have hterm : 0 < |typeIICorrelationHigherParameter N 2 n n'| / K ^ 2 :=
        div_pos (abs_pos.mpr hM') (pow_pos hK 2)
      positivity
    have hlenNat :
        typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) qouter kouter n n' -
          typeIIProductRestrictedBlockLower a 1 qouter kouter n n' ≤ qouter :=
      typeIIProductRestrictedBlock_length_le
        a b 1 (Bouter + 1) qouter kouter n n'
    have hlen :
        ((typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) qouter kouter n n' -
          typeIIProductRestrictedBlockLower a 1 qouter kouter n n' : ℕ) : ℝ) ≤
            (qouter : ℝ) := by exact_mod_cast hlenNat
    have hrangeRaw := reciprocalPhaseFourStepOptimizedRange_cast_le_of_error_bound
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') hK hF' herrorBound
    have hG : 0 ≤ typeIIShortIntervalEffectiveErrorBound
        N K B 2 qinner kinner :=
      (reciprocalPhaseFourStepEffectiveErrorScale_pos _ _ hK hF').le.trans herrorBound
    have hrange :
        (reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) qouter kouter n n' -
            typeIIProductRestrictedBlockLower a 1 qouter kouter n n') : ℝ) ≤
          (qouter : ℝ) * typeIIShortIntervalEffectiveErrorBound
            N K B 2 qinner kinner ^ (1 / 128 : ℝ) :=
      hrangeRaw.trans (mul_le_mul_of_nonneg_right hlen
        (Real.rpow_nonneg hG _))
    have hmargin : (qouter : ℝ) +
        (4 * reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) qouter kouter n n' -
            typeIIProductRestrictedBlockLower a 1 qouter kouter n n') : ℕ) ≤ K := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      have hfour := mul_le_mul_of_nonneg_left hrange (by norm_num : (0 : ℝ) ≤ 4)
      calc
        (qouter : ℝ) + 4 *
            (reciprocalPhaseFourStepOptimizedRange
              (typeIICorrelationLinearParameter N n n')
              (typeIICorrelationHigherParameter N 2 n n') 2 K
              (typeIIProductRestrictedBlockUpper b 1 (Bouter + 1) qouter kouter n n' -
                typeIIProductRestrictedBlockLower a 1 qouter kouter n n') : ℝ) ≤
          (qouter : ℝ) + 4 * ((qouter : ℝ) *
            typeIIShortIntervalEffectiveErrorBound N K B 2 qinner kinner ^
              (1 / 128 : ℝ)) := add_le_add le_rfl hfour
        _ = (qouter : ℝ) + 4 * (qouter : ℝ) *
            typeIIShortIntervalEffectiveErrorBound N K B 2 qinner kinner ^
              (1 / 128 : ℝ) := by ring
        _ ≤ K := hmarginScale
    have hgeom := typeIIProductRestrictedBlock_quadratic_fourStep_geometry
      a b Bouter qouter kouter n n'
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') K hKouter hLength hmargin
    exact ⟨hscale',
      herror', hgeom.1,
      hgeom.2.1, hgeom.2.1, hgeom.2.2⟩
  exact sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_fourStepWeyl_productScale
    a b γ N orders Bouter Binner qouter qinner kouter kinner
    hqouter hqinner hL hγ hN hK hB hKB hBinner hqinnerB hF
    (by norm_num) hrFive hrSix hanalytic

/-- Pointwise quadratic Type II correlation estimate in the low transformed-
scale branch.  The effective-error budget is manufactured from the pair's own
bound `F' ≤ K^4`; the independent majorant `E` is used only in the final
source-scale decay kernel. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_quadratic_lowScale
    (a b K₀ K₁ q k : ℕ) (N : ℝ) (orders : Finset ℕ)
    {n n' : ℕ} {K B E : ℝ}
    (hK₀ : 0 < K₀) (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hN : N ≠ 0) (hKouter : K = ((K₀ + k * q : ℕ) : ℝ))
    (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K / K ^ 5 ≤ E)
    (hscale :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K ≤ K ^ 4)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N N 2 (K * B) / B)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqK : 5 * (q : ℝ) ≤ K) :
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let F := reciprocalPhaseScale N N 2 (K * B)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
            (E ^ (1 / 1024 : ℝ) +
              4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n))) := by
  dsimp only
  have hKnat : 0 < K₀ + k * q := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hpairError :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K / K ^ 5 ≤ 1 / K :=
    div_pow_five_le_one_div_of_le_pow_four hK hscale
  have hanalytic :
      let N' := typeIICorrelationLinearParameter N n n'
      let M' := typeIICorrelationHigherParameter N 2 n n'
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      1 ≤ hi - lo →
        reciprocalPhaseScale N' M' 2 K ≤ K ^ 4 ∧
        reciprocalPhaseFourStepEffectiveErrorScale N' M' 2 K (hi - lo) ≤ 1 ∧
        (lo : ℝ) ∈ Set.Icc K (2 * K) ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
          2 * K ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
          2 * K ∧
        ∀ t ∈ Set.Icc K (2 * K), t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
    dsimp only
    intro hLength
    have herror : reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K
        (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n') ≤ 1 := by
      apply reciprocalPhaseFourStepEffectiveErrorScale_typeIICorrelation_le_one_of_far
        N K B
        (reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K / K ^ 5)
        hK hB hKB (by norm_num) hn hn' hnB hn'B
      · exact le_rfl
      · apply mul_error_le_one_div_four_of_error_le_one_div
        · positivity
        · exact hK
        · exact hpairError
        · exact hKbudget
      · exact hLength
      · exact hfar
    have hM' : typeIICorrelationHigherParameter N 2 n n' ≠ 0 :=
      typeIICorrelationHigherParameter_ne_zero hN (by norm_num)
        (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
    have hF' : 0 < reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K := by
      unfold reciprocalPhaseScale
      have hterm : 0 < |typeIICorrelationHigherParameter N 2 n n'| / K ^ 2 :=
        div_pos (abs_pos.mpr hM') (pow_pos hK 2)
      positivity
    have hlenNat :
        typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n' ≤ q :=
      typeIIProductRestrictedBlock_length_le a b K₀ K₁ q k n n'
    have hlen :
        ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hlenNat
    have hrangeRaw := reciprocalPhaseFourStepOptimizedRange_cast_le_of_error_bound
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') hK hF' herror
    have hrange :
        (reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤ (q : ℝ) := by
      calc
        (reciprocalPhaseFourStepOptimizedRange
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K
            (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
              typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤
          ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) *
              (1 : ℝ) ^ (1 / 128 : ℝ) := hrangeRaw
        _ = ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) := by
              norm_num
        _ ≤ (q : ℝ) := hlen
    have hmargin : (q : ℝ) +
        (4 * reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n') : ℕ) ≤ K := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      have hfour := mul_le_mul_of_nonneg_left hrange (by norm_num : (0 : ℝ) ≤ 4)
      calc
        (q : ℝ) + 4 *
            (reciprocalPhaseFourStepOptimizedRange
              (typeIICorrelationLinearParameter N n n')
              (typeIICorrelationHigherParameter N 2 n n') 2 K
              (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
                typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤
          (q : ℝ) + 4 * (q : ℝ) := add_le_add le_rfl hfour
        _ = 5 * (q : ℝ) := by ring
        _ ≤ K := hqK
    have hgeom := typeIIProductRestrictedBlock_quadratic_fourStep_geometryAt
      a b K₀ K₁ q k n n'
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') K hKouter hLength hmargin
    exact ⟨hscale, herror, hgeom.1,
      hgeom.2.1, hgeom.2.1, hgeom.2.2⟩
  exact norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_equalParameters
    a b K₀ K₁ q k N orders hq hn hn' hne hN hK hB hKB
      (by norm_num) hnB hn'B hrFive hrSix hupper hanalytic

/-- Intrinsic low-scale form of the quadratic correlation estimate.  The
branch hypothesis `F' ≤ K^4` itself supplies `F'/K^5 ≤ 1/K`, so no global
short-block error majorant or upper bound on the original phase scale is
needed. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_quadratic_lowScale_intrinsic
    (a b K₀ K₁ q k : ℕ) (N : ℝ) (orders : Finset ℕ)
    {n n' : ℕ} {K B : ℝ}
    (hK₀ : 0 < K₀) (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hN : N ≠ 0) (hKouter : K = ((K₀ + k * q : ℕ) : ℝ))
    (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hscale :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K ≤ K ^ 4)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N N 2 (K * B) / B)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqK : 5 * (q : ℝ) ≤ K) :
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let F := reciprocalPhaseScale N N 2 (K * B)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
            ((1 / K) ^ (1 / 1024 : ℝ) +
              4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n))) := by
  have hKnat : 0 < K₀ + k * q := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  apply norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_quadratic_lowScale
    a b K₀ K₁ q k N orders hK₀ hq hn hn' hne hN hKouter hB hKB
      hnB hn'B hrFive hrSix
  · exact div_pow_five_le_one_div_of_le_pow_four hK hscale
  · exact hscale
  · exact hfar
  · exact hKbudget
  · exact hqK

/-- Quadratic Type II propagation with the source's pairwise analytic split.
Far pairs with transformed scale at most `K^4` are proved here by four-step
Weyl differencing; only the complementary high-scale pairs are delegated to
`hhigh`.  Nearby pairs and the final double-block summation are automatic. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_quadratic
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hKouter : K = ((K₀ + kouter * qouter : ℕ) : ℝ))
    (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hS₁ : (S₁ : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqouterK : 5 * (qouter : ℝ) ≤ K)
    (hhigh : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        let F := reciprocalPhaseScale N N 2 (K * B)
        let E := typeIIShortIntervalScaleErrorAt N N K B 2 S₀ qinner kinner
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            E ^ (1 / 1024 : ℝ))) :
    let E := typeIIShortIntervalScaleErrorAt N N K B 2 S₀ qinner kinner
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  dsimp only
  let E := typeIIShortIntervalScaleErrorAt N N K B 2 S₀ qinner kinner
  let F := reciprocalPhaseScale N N 2 (K * B)
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hKnat : 0 < K₀ + kouter * qouter := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hE : 0 ≤ E := by
    unfold E typeIIShortIntervalScaleErrorAt
    positivity
  have hupper : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K / K ^ 5 ≤ E := by
    intro n hnmem n' hn'mem _
    simpa only [E] using
      (reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_shortIntervalAt
        N N K B (by norm_num) hK hS₀ hqinner hS₁ hnmem hn'mem)
  have hfarBound : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            E ^ (1 / 1024 : ℝ)) := by
    intro n hnmem n' hn'mem hne hfar
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnUpper : n ≤ S₁ := by omega
    have hn'Upper : n' ≤ S₁ := by omega
    have hnB : (n : ℝ) ≤ B := (by exact_mod_cast hnUpper : (n : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    have hn'B : (n' : ℝ) ≤ B :=
      (by exact_mod_cast hn'Upper : (n' : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    by_cases hscale : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K ≤ K ^ 4
    · have hraw :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_quadratic_lowScale
          a b K₀ K₁ qouter kouter N orders hK₀ hqouter hnpos hn'pos hne
            hN hKouter hB hKB hnB hn'B hrFive hrSix
            (hupper n hnmem n' hn'mem hne) hscale hfar hKbudget hqouterK
      have huniform :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength
          a b K₀ K₁ qouter kouter N orders hqouter hK.le hB hE hraw
      simpa only [E, F, Q] using huniform
    · have hscaleHigh : K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K :=
        lt_of_not_ge hscale
      simpa only [E, F, Q] using
        hhigh n hnmem n' hn'mem hne hfar hscaleHigh
  have hqouterK' : (qouter : ℝ) ≤ K := by
    nlinarith [hqouterK]
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_nearFar_of_farBound
      a b γ N orders K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hK hB hqinnerB hF hE hqouterK' hfarBound
  simpa only [E, F, Q] using hresult

/-- Source-faithful quadratic Type II hybrid with separate analytic errors.
The low-scale Weyl branch contributes `E^(1/1024)`; the high-scale Vinogradov
branch contributes the independent additive error `V`. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_quadratic_additiveError
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B V : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hKouter : K = ((K₀ + kouter * qouter : ℕ) : ℝ))
    (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hS₁ : (S₁ : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqouterK : 5 * (qouter : ℝ) ≤ K) (hV : 0 ≤ V)
    (hhigh : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        let F := reciprocalPhaseScale N N 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V)) :
    let E := typeIIShortIntervalScaleErrorAt N N K B 2 S₀ qinner kinner
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * (E ^ (1 / 1024 : ℝ) + V)))) := by
  dsimp only
  let E := typeIIShortIntervalScaleErrorAt N N K B 2 S₀ qinner kinner
  let F := reciprocalPhaseScale N N 2 (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hKnat : 0 < K₀ + kouter * qouter := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hE : 0 ≤ E := by unfold E typeIIShortIntervalScaleErrorAt; positivity
  have hEpow : 0 ≤ E ^ δ := Real.rpow_nonneg hE _
  have hZ : 0 ≤ E ^ δ + V := add_nonneg hEpow hV
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hupper : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K / K ^ 5 ≤ E := by
    intro n hnmem n' hn'mem _
    simpa only [E] using
      (reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_shortIntervalAt
        N N K B (by norm_num) hK hS₀ hqinner hS₁ hnmem hn'mem)
  have hfarBound : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            (E ^ δ + V)) := by
    intro n hnmem n' hn'mem hne hfar
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnUpper : n ≤ S₁ := by omega
    have hn'Upper : n' ≤ S₁ := by omega
    have hnB : (n : ℝ) ≤ B :=
      (by exact_mod_cast hnUpper : (n : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    have hn'B : (n' : ℝ) ≤ B :=
      (by exact_mod_cast hn'Upper : (n' : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    by_cases hscale : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K ≤ K ^ 4
    · have hraw :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_quadratic_lowScale
          a b K₀ K₁ qouter kouter N orders hK₀ hqouter hnpos hn'pos hne
            hN hKouter hB hKB hnB hn'B hrFive hrSix
            (hupper n hnmem n' hn'mem hne) hscale hfar hKbudget hqouterK
      have hlow :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength
          a b K₀ K₁ qouter kouter N orders hqouter hK.le hB hE hraw
      have hadd : 4 * typeIIDecayKernel B F δ (Nat.dist n' n) + E ^ δ ≤
          4 * typeIIDecayKernel B F δ (Nat.dist n' n) + (E ^ δ + V) := by
        linarith
      have hlow' : ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + E ^ δ) := by
        simpa only [E, F, Q, δ] using hlow
      exact hlow'.trans
        (mul_le_mul_of_nonneg_left hadd hQ)
    · have hscaleHigh : K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K := lt_of_not_ge hscale
      have hhighPair := hhigh n hnmem n' hn'mem hne hfar hscaleHigh
      have hadd : 4 * typeIIDecayKernel B F δ (Nat.dist n' n) + V ≤
          4 * typeIIDecayKernel B F δ (Nat.dist n' n) + (E ^ δ + V) := by
        linarith
      have hhighPair' : ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + V) := by
        simpa only [F, Q, δ] using hhighPair
      exact hhighPair'.trans
        (mul_le_mul_of_nonneg_left hadd hQ)
  have hqouterK' : (qouter : ℝ) ≤ K := by nlinarith [hqouterK]
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_nearFar_of_farBound_additiveError
      a b γ N orders K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hK hB hqinnerB hF hZ hqouterK' hfarBound
  simpa only [E, F, Q, δ] using hresult

/-- Quadratic Type II hybrid with an intrinsic low-scale error.  Low pairs use
`(1/K)^(1/1024)`, obtained directly from `F' ≤ K^4`; high pairs use the
independent Vinogradov error `V`.  Consequently this estimate has no global
short-block scale error and needs no upper bound on the original phase scale.
-/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_quadratic_intrinsicError
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B V : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hKouter : K = ((K₀ + kouter * qouter : ℕ) : ℝ))
    (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hS₁ : (S₁ : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqouterK : 5 * (qouter : ℝ) ≤ K) (hV : 0 ≤ V)
    (hhigh : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        let F := reciprocalPhaseScale N N 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V)) :
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) + V)))) := by
  dsimp only
  let F := reciprocalPhaseScale N N 2 (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hKnat : 0 < K₀ + kouter * qouter := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hInvK : 0 ≤ 1 / K := by positivity
  have hInvKpow : 0 ≤ (1 / K) ^ δ := Real.rpow_nonneg hInvK _
  have hZ : 0 ≤ (1 / K) ^ δ + V := add_nonneg hInvKpow hV
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hfarBound : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V)) := by
    intro n hnmem n' hn'mem hne hfar
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnUpper : n ≤ S₁ := by omega
    have hn'Upper : n' ≤ S₁ := by omega
    have hnB : (n : ℝ) ≤ B :=
      (by exact_mod_cast hnUpper : (n : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    have hn'B : (n' : ℝ) ≤ B :=
      (by exact_mod_cast hn'Upper : (n' : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    by_cases hscale : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K ≤ K ^ 4
    · have hraw :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_quadratic_lowScale_intrinsic
          a b K₀ K₁ qouter kouter N orders hK₀ hqouter hnpos hn'pos hne
            hN hKouter hB hKB hnB hn'B hrFive hrSix hscale hfar
            hKbudget hqouterK
      have hlow :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength
          a b K₀ K₁ qouter kouter N orders hqouter hK.le hB hInvK hraw
      have hadd : 4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
          (1 / K) ^ δ ≤
          4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V) := by linarith
      have hlow' : ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            (1 / K) ^ δ) := by
        simpa only [F, Q, δ] using hlow
      exact hlow'.trans (mul_le_mul_of_nonneg_left hadd hQ)
    · have hscaleHigh : K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K := lt_of_not_ge hscale
      have hhighPair := hhigh n hnmem n' hn'mem hne hfar hscaleHigh
      have hadd : 4 * typeIIDecayKernel B F δ (Nat.dist n' n) + V ≤
          4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V) := by linarith
      have hhighPair' : ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + V) := by
        simpa only [F, Q, δ] using hhighPair
      exact hhighPair'.trans (mul_le_mul_of_nonneg_left hadd hQ)
  have hqouterK' : (qouter : ℝ) ≤ K := by nlinarith [hqouterK]
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_nearFar_of_farBound_additiveError
      a b γ N orders K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hK hB hqinnerB hF hZ hqouterK' hfarBound
  simpa only [F, Q, δ] using hresult

/-- Quadratic Type II estimate on arbitrary positive short blocks.  This is
the direct analytic interface for the dyadic blocks appearing in the canonical
Vaughan double-family decomposition. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_fourStepWeyl_quadratic
    (a b : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hN : N ≠ 0) (hKouter : K = ((K₀ + kouter * qouter : ℕ) : ℝ))
    (hB : 0 < B) (hKB : 1 ≤ K * B)
    (hS₁ : (S₁ : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hscaleError : typeIIShortIntervalScaleErrorAt
      N N K B 2 S₀ qinner kinner ≤ 1 / K)
    (hscaleBudget : 240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      typeIIShortIntervalScaleErrorAt N N K B 2 S₀ qinner kinner ≤ 1 / 4)
    (hqouterK : 5 * (qouter : ℝ) ≤ K) :
    let E := typeIIShortIntervalScaleErrorAt N N K B 2 S₀ qinner kinner
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  let E := typeIIShortIntervalScaleErrorAt N N K B 2 S₀ qinner kinner
  have hKnat : 0 < K₀ + kouter * qouter := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hE : 0 ≤ E := by
    unfold E typeIIShortIntervalScaleErrorAt
    positivity
  have hupper : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K / K ^ 5 ≤ E := by
    intro n hnmem n' hn'mem _
    simpa only [E] using
      (reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_shortIntervalAt
        N N K B (by norm_num) hK hS₀ hqinner hS₁ hnmem hn'mem)
  have hanalyticFar : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        let N' := typeIICorrelationLinearParameter N n n'
        let M' := typeIICorrelationHigherParameter N 2 n n'
        let lo := typeIIProductRestrictedBlockLower a K₀ qouter kouter n n'
        let hi := typeIIProductRestrictedBlockUpper b K₀ K₁
          qouter kouter n n'
        1 ≤ hi - lo →
          reciprocalPhaseScale N' M' 2 K ≤ K ^ 4 ∧
          reciprocalPhaseFourStepEffectiveErrorScale N' M' 2 K (hi - lo) ≤ 1 ∧
          (lo : ℝ) ∈ Set.Icc K (2 * K) ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
            2 * K ∧
          (lo : ℝ) + (hi - lo : ℕ) +
              (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
            2 * K ∧
          ∀ t ∈ Set.Icc K (2 * K), t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
    intro n hnmem n' hn'mem hne hfar
    dsimp only
    intro hLength
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnUpper : n ≤ S₁ := by omega
    have hn'Upper : n' ≤ S₁ := by omega
    have hnUpperReal : (n : ℝ) ≤ (S₁ : ℝ) := by exact_mod_cast hnUpper
    have hn'UpperReal : (n' : ℝ) ≤ (S₁ : ℝ) := by exact_mod_cast hn'Upper
    have hnB : (n : ℝ) ≤ B := hnUpperReal.trans hS₁
    have hn'B : (n' : ℝ) ≤ B := hn'UpperReal.trans hS₁
    have hpairScale := hupper n hnmem n' hn'mem hne
    have hscale' : reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K ≤ K ^ 4 :=
      le_pow_four_of_div_pow_five_le_one_div hK
        (hpairScale.trans (by simpa only [E] using hscaleError))
    have herror' : reciprocalPhaseFourStepEffectiveErrorScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
            typeIIProductRestrictedBlockLower a K₀ qouter kouter n n') ≤ 1 := by
      apply reciprocalPhaseFourStepEffectiveErrorScale_typeIICorrelation_le_one_of_far
        N K B E hK hB hKB (by norm_num) hnpos hn'pos hnB hn'B hpairScale
      · simpa only [E] using hscaleBudget
      · exact hLength
      · exact hfar
    have hM' : typeIICorrelationHigherParameter N 2 n n' ≠ 0 :=
      typeIICorrelationHigherParameter_ne_zero hN (by norm_num)
        (Nat.ne_of_gt hnpos) (Nat.ne_of_gt hn'pos) hne
    have hF' : 0 < reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K := by
      unfold reciprocalPhaseScale
      have hterm : 0 < |typeIICorrelationHigherParameter N 2 n n'| / K ^ 2 :=
        div_pos (abs_pos.mpr hM') (pow_pos hK 2)
      positivity
    have hlenNat :
        typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
          typeIIProductRestrictedBlockLower a K₀ qouter kouter n n' ≤ qouter :=
      typeIIProductRestrictedBlock_length_le
        a b K₀ K₁ qouter kouter n n'
    have hlen :
        ((typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
          typeIIProductRestrictedBlockLower a K₀ qouter kouter n n' : ℕ) : ℝ) ≤
            (qouter : ℝ) := by exact_mod_cast hlenNat
    have hrangeRaw := reciprocalPhaseFourStepOptimizedRange_cast_le_of_error_bound
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') hK hF' herror'
    have hrange :
        (reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
            typeIIProductRestrictedBlockLower a K₀ qouter kouter n n') : ℝ) ≤
          (qouter : ℝ) := by
      calc
        (reciprocalPhaseFourStepOptimizedRange
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K
            (typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
              typeIIProductRestrictedBlockLower a K₀ qouter kouter n n') : ℝ) ≤
          ((typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
            typeIIProductRestrictedBlockLower a K₀ qouter kouter n n' : ℕ) : ℝ) *
              (1 : ℝ) ^ (1 / 128 : ℝ) := hrangeRaw
        _ = ((typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
            typeIIProductRestrictedBlockLower a K₀ qouter kouter n n' : ℕ) : ℝ) := by
              norm_num
        _ ≤ (qouter : ℝ) := hlen
    have hmargin : (qouter : ℝ) +
        (4 * reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
            typeIIProductRestrictedBlockLower a K₀ qouter kouter n n') : ℕ) ≤ K := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      have hfour := mul_le_mul_of_nonneg_left hrange (by norm_num : (0 : ℝ) ≤ 4)
      calc
        (qouter : ℝ) + 4 *
            (reciprocalPhaseFourStepOptimizedRange
              (typeIICorrelationLinearParameter N n n')
              (typeIICorrelationHigherParameter N 2 n n') 2 K
              (typeIIProductRestrictedBlockUpper b K₀ K₁ qouter kouter n n' -
                typeIIProductRestrictedBlockLower a K₀ qouter kouter n n') : ℝ) ≤
          (qouter : ℝ) + 4 * (qouter : ℝ) :=
            add_le_add le_rfl hfour
        _ = 5 * (qouter : ℝ) := by ring
        _ ≤ K := hqouterK
    have hgeom := typeIIProductRestrictedBlock_quadratic_fourStep_geometryAt
      a b K₀ K₁ qouter kouter n n'
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') K hKouter hLength hmargin
    exact ⟨hscale', herror', hgeom.1,
      hgeom.2.1, hgeom.2.1, hgeom.2.2⟩
  have hqouterK' : (qouter : ℝ) ≤ K := by
    nlinarith [hqouterK]
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_fourStepWeyl_nearFar
      a b γ N orders K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hN hK hB hKB hS₁ hqinnerB hF hE
      hqouterK' (by norm_num) hrFive hrSix hupper hanalyticFar
  simpa only [E] using hresult

/-- Canonical Vaughan Type II blocks below the common subdivision budget have
inner length at most one.  Their off-diagonal contribution is empty, so the
squared sum is bounded by the diagonal term alone, without any phase-scale or
Weyl hypothesis. -/
theorem sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_singleton
    (a b Bcap : ℕ) (γ : ℕ → ℂ) (N : ℝ) (sk tl : ℕ × ℕ) {L : ℝ}
    (hsmall : 2 ^ tl.1 < vaughanShortIntervalBudget Bcap)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L) :
    let qouter := dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget Bcap)
    ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) sk,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget Bcap) tl)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * L ^ 2 := by
  dsimp only
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hDouter : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinner : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouter hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinner hbudget
  have hqinnerOne : qinner ≤ 1 := by
    have hraw := dyadicShortIntervalLength_le_div_add_one
      (2 ^ tl.1) hbudget
    have hdiv : 2 ^ tl.1 / vaughanShortIntervalBudget Bcap = 0 :=
      Nat.div_eq_of_lt hsmall
    simpa only [qinner, hdiv, zero_add] using hraw
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_singleton
      a b γ N N 2 (2 ^ sk.1) (2 * 2 ^ sk.1)
      (2 ^ tl.1) (2 * 2 ^ tl.1) qouter qinner sk.2 tl.2
      hDouter hDinner hqouter hqinner hqinnerOne hL hγ
  simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner] using hresult

/-- Canonical Vaughan Type II block estimate with the source's pairwise
Weyl/Vinogradov split.  The decomposition discharges every low-scale Weyl and
block-geometry condition; the sole analytic input `hhigh` concerns far pairs
whose transformed scale exceeds the four-step Weyl range. -/
theorem sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_quadratic
    (a b Bcap : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) {L d : ℝ}
    (hBcap : 0 < Bcap) (hlog : 2 ≤ Real.log Bcap)
    (hDouter : (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ))
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L) (hN : N ≠ 0)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) (hd : 0 ≤ d)
    (hFhigh : (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N N 2
      (((dyadicShortIntervalLeftEndpoint (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)))
    (hhigh :
      let qouter := dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget Bcap)
      let qinner := dyadicShortIntervalLength (2 ^ tl.1)
        (vaughanShortIntervalBudget Bcap)
      let K : ℝ := (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget Bcap) sk : ℕ)
      let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
      ∀ n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl,
        ∀ n' ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget Bcap) tl, n ≠ n' →
          3 ≤ (Nat.dist n' n : ℝ) *
            reciprocalPhaseScale N N 2 (K * B) / B →
          K ^ 4 < reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K →
          let F := reciprocalPhaseScale N N 2 (K * B)
          let E := typeIIShortIntervalScaleErrorAt N N K B 2
            (2 ^ tl.1) qinner tl.2
          let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
            (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
                (1 + Real.log (qouter : ℝ)) * K)
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) sk)
              N N 2 n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
              E ^ (1 / 1024 : ℝ))) :
    let qouter := dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget Bcap)
    let qinner := dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget Bcap)
    let K : ℝ := (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget Bcap) sk : ℕ)
    let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
    let E := typeIIShortIntervalScaleErrorAt N N K B 2 (2 ^ tl.1) qinner tl.2
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) sk,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget Bcap) tl)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  dsimp only
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinnerPos : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinnerPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by rfl
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B) := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [K, B] using hFhigh)
  have hB : 0 < B := by unfold B; positivity
  have hKnat : 0 < (2 ^ sk.1) + sk.2 * qouter := by omega
  have hKpos : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hKone : (1 : ℝ) ≤ K := by rw [hKouter]; exact_mod_cast hKnat
  have hKB : 1 ≤ K * B := by
    have hpowOne : 1 ≤ 2 ^ tl.1 := one_le_pow₀ (by omega)
    have hBoneNat : 1 ≤ 2 * 2 ^ tl.1 := by omega
    have hBone : (1 : ℝ) ≤ B := by unfold B; exact_mod_cast hBoneNat
    simpa only [one_mul] using
      (mul_le_mul hKone hBone (by norm_num : (0 : ℝ) ≤ 1)
        (zero_le_one.trans hKone))
  have hS₁ : (((2 * 2 ^ tl.1 : ℕ) : ℝ)) ≤ B := by rfl
  have hqinnerNat : qinner ≤ 2 * 2 ^ tl.1 := by
    have hraw := dyadicShortIntervalLength_le_div_add_one
      (2 ^ tl.1) hbudget
    unfold qinner
    have hdiv : 2 ^ tl.1 / vaughanShortIntervalBudget Bcap ≤ 2 ^ tl.1 :=
      Nat.div_le_self _ _
    omega
  have hqinnerB : (qinner : ℝ) ≤ B := by
    unfold B
    exact_mod_cast hqinnerNat
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    have hnat : 2 ^ sk.1 ≤ 2 ^ sk.1 + sk.2 * qouter :=
      Nat.le_add_right _ _
    exact_mod_cast hnat
  have hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K :=
    hbudgetLarge.trans (hDouter.trans hDouterK)
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : 5 * (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    exact hfiveQ.trans hDouterK
  have hhigh' : ∀ n ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2,
      ∀ n' ∈ shortIntervalBlock
          (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        let F := reciprocalPhaseScale N N 2 (K * B)
        let E := typeIIShortIntervalScaleErrorAt N N K B 2
          (2 ^ tl.1) qinner tl.2
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock (2 ^ sk.1) (2 * 2 ^ sk.1) qouter sk.2)
            N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            E ^ (1 / 1024 : ℝ)) := by
    simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hhigh
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_quadratic
      a b γ N orders (2 ^ sk.1) (2 * 2 ^ sk.1) (2 ^ tl.1) (2 * 2 ^ tl.1)
      qouter qinner sk.2 tl.2 hDouterPos hDinnerPos hqouter hqinner hL hγ hN
      hKouter hB hKB hS₁ hqinnerB (by simpa only [K, B] using hF)
      hrFive hrSix hKbudget hqouterK hhigh'
  simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hresult

/-- Source-faithful canonical Vaughan Type II block estimate with separate
analytic errors.  The low-scale Weyl branch contributes `E^(1/1024)`, while
the high-scale callback contributes the independent additive error `V`.  All
block geometry and low-scale Weyl conditions are discharged internally. -/
theorem sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_quadratic_additiveError
    (a b Bcap : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) {L d V : ℝ}
    (hBcap : 0 < Bcap) (hlog : 2 ≤ Real.log Bcap)
    (hDouter : (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ))
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L) (hN : N ≠ 0)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) (hd : 0 ≤ d)
    (hFhigh : (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N N 2
      (((dyadicShortIntervalLeftEndpoint (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)))
    (hV : 0 ≤ V)
    (hhigh :
      let qouter := dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget Bcap)
      let K : ℝ := (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget Bcap) sk : ℕ)
      let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
      ∀ n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl,
        ∀ n' ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget Bcap) tl, n ≠ n' →
          3 ≤ (Nat.dist n' n : ℝ) *
            reciprocalPhaseScale N N 2 (K * B) / B →
          K ^ 4 < reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K →
          let F := reciprocalPhaseScale N N 2 (K * B)
          let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
            (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
                (1 + Real.log (qouter : ℝ)) * K)
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) sk)
              N N 2 n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V)) :
    let qouter := dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget Bcap)
    let qinner := dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget Bcap)
    let K : ℝ := (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget Bcap) sk : ℕ)
    let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
    let E := typeIIShortIntervalScaleErrorAt N N K B 2 (2 ^ tl.1) qinner tl.2
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) sk,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget Bcap) tl)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * (E ^ (1 / 1024 : ℝ) + V)))) := by
  dsimp only
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinnerPos : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinnerPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by rfl
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B) := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [K, B] using hFhigh)
  have hB : 0 < B := by unfold B; positivity
  have hKnat : 0 < (2 ^ sk.1) + sk.2 * qouter := by omega
  have hKpos : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hKone : (1 : ℝ) ≤ K := by rw [hKouter]; exact_mod_cast hKnat
  have hKB : 1 ≤ K * B := by
    have hpowOne : 1 ≤ 2 ^ tl.1 := one_le_pow₀ (by omega)
    have hBoneNat : 1 ≤ 2 * 2 ^ tl.1 := by omega
    have hBone : (1 : ℝ) ≤ B := by unfold B; exact_mod_cast hBoneNat
    simpa only [one_mul] using
      (mul_le_mul hKone hBone (by norm_num : (0 : ℝ) ≤ 1)
        (zero_le_one.trans hKone))
  have hS₁ : (((2 * 2 ^ tl.1 : ℕ) : ℝ)) ≤ B := by rfl
  have hqinnerNat : qinner ≤ 2 * 2 ^ tl.1 := by
    have hraw := dyadicShortIntervalLength_le_div_add_one
      (2 ^ tl.1) hbudget
    unfold qinner
    have hdiv : 2 ^ tl.1 / vaughanShortIntervalBudget Bcap ≤ 2 ^ tl.1 :=
      Nat.div_le_self _ _
    omega
  have hqinnerB : (qinner : ℝ) ≤ B := by
    unfold B
    exact_mod_cast hqinnerNat
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    have hnat : 2 ^ sk.1 ≤ 2 ^ sk.1 + sk.2 * qouter :=
      Nat.le_add_right _ _
    exact_mod_cast hnat
  have hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K :=
    hbudgetLarge.trans (hDouter.trans hDouterK)
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : 5 * (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    exact hfiveQ.trans hDouterK
  have hhigh' : ∀ n ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2,
      ∀ n' ∈ shortIntervalBlock
          (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        let F := reciprocalPhaseScale N N 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock (2 ^ sk.1) (2 * 2 ^ sk.1) qouter sk.2)
            N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V) := by
    simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hhigh
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_quadratic_additiveError
      a b γ N orders (2 ^ sk.1) (2 * 2 ^ sk.1) (2 ^ tl.1) (2 * 2 ^ tl.1)
      qouter qinner sk.2 tl.2 hDouterPos hDinnerPos hqouter hqinner hL hγ hN
      hKouter hB hKB hS₁ hqinnerB (by simpa only [K, B] using hF)
      hrFive hrSix hKbudget hqouterK hV hhigh'
  simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hresult

/-- Canonical Vaughan Type II hybrid with intrinsic low-scale error.  The
low-scale contribution is `(1/K)^(1/1024)` and therefore no source upper bound
is needed to control a retained short-block error. -/
theorem sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_quadratic_intrinsicError
    (a b Bcap : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) {L d V : ℝ}
    (hBcap : 0 < Bcap) (hlog : 2 ≤ Real.log Bcap)
    (hDouter : (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ))
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L) (hN : N ≠ 0)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) (hd : 0 ≤ d)
    (hFhigh : (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N N 2
      (((dyadicShortIntervalLeftEndpoint (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)))
    (hV : 0 ≤ V)
    (hhigh :
      let qouter := dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget Bcap)
      let K : ℝ := (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget Bcap) sk : ℕ)
      let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
      ∀ n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl,
        ∀ n' ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget Bcap) tl, n ≠ n' →
          3 ≤ (Nat.dist n' n : ℝ) *
            reciprocalPhaseScale N N 2 (K * B) / B →
          K ^ 4 < reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K →
          let F := reciprocalPhaseScale N N 2 (K * B)
          let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
            (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
                (1 + Real.log (qouter : ℝ)) * K)
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) sk)
              N N 2 n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V)) :
    let qouter := dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget Bcap)
    let qinner := dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget Bcap)
    let K : ℝ := (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget Bcap) sk : ℕ)
    let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) sk,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget Bcap) tl)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) + V)))) := by
  dsimp only
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinnerPos : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinnerPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by rfl
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B) := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [K, B] using hFhigh)
  have hB : 0 < B := by unfold B; positivity
  have hKnat : 0 < (2 ^ sk.1) + sk.2 * qouter := by omega
  have hKone : (1 : ℝ) ≤ K := by rw [hKouter]; exact_mod_cast hKnat
  have hKB : 1 ≤ K * B := by
    have hpowOne : 1 ≤ 2 ^ tl.1 := one_le_pow₀ (by omega)
    have hBoneNat : 1 ≤ 2 * 2 ^ tl.1 := by omega
    have hBone : (1 : ℝ) ≤ B := by unfold B; exact_mod_cast hBoneNat
    simpa only [one_mul] using
      (mul_le_mul hKone hBone (by norm_num : (0 : ℝ) ≤ 1)
        (zero_le_one.trans hKone))
  have hS₁ : (((2 * 2 ^ tl.1 : ℕ) : ℝ)) ≤ B := by rfl
  have hqinnerNat : qinner ≤ 2 * 2 ^ tl.1 := by
    have hraw := dyadicShortIntervalLength_le_div_add_one
      (2 ^ tl.1) hbudget
    unfold qinner
    have hdiv : 2 ^ tl.1 / vaughanShortIntervalBudget Bcap ≤ 2 ^ tl.1 :=
      Nat.div_le_self _ _
    omega
  have hqinnerB : (qinner : ℝ) ≤ B := by
    unfold B
    exact_mod_cast hqinnerNat
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    have hnat : 2 ^ sk.1 ≤ 2 ^ sk.1 + sk.2 * qouter := Nat.le_add_right _ _
    exact_mod_cast hnat
  have hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K :=
    hbudgetLarge.trans (hDouter.trans hDouterK)
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : 5 * (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    exact hfiveQ.trans hDouterK
  have hhigh' : ∀ n ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2,
      ∀ n' ∈ shortIntervalBlock
          (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N N 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        let F := reciprocalPhaseScale N N 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock (2 ^ sk.1) (2 * 2 ^ sk.1) qouter sk.2)
            N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V) := by
    simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hhigh
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_quadratic_intrinsicError
      a b γ N orders (2 ^ sk.1) (2 * 2 ^ sk.1) (2 ^ tl.1) (2 * 2 ^ tl.1)
      qouter qinner sk.2 tl.2 hDouterPos hDinnerPos hqouter hqinner hL hγ hN
      hKouter hB hKB hS₁ hqinnerB (by simpa only [K, B] using hF)
      hrFive hrSix hKbudget hqouterK hV hhigh'
  simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hresult

/-- Canonical Vaughan Type II hybrid with the high branch discharged by the
source Vinogradov proposition.  The abstract `hhigh` callback has disappeared:
the low branch is the intrinsic four-step Weyl estimate, while the high branch
uses the uniform callback from `Tao2026.Vinogradov` with error
`3(log P)^(-T)`. -/
theorem eventually_sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_sourceVinogradov
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b Bcap : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
        (sk tl : ℕ × ℕ) (L d : ℝ),
        0 < Bcap → 2 ≤ Real.log Bcap →
        (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ) →
        0 ≤ L → (∀ n, ‖γ n‖ ≤ L) → N ≠ 0 →
        5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N N 2
          (((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
            ((2 * 2 ^ tl.1 : ℕ) : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) →
        let qouter := dyadicShortIntervalLength (2 ^ sk.1)
          (vaughanShortIntervalBudget Bcap)
        let qinner := dyadicShortIntervalLength (2 ^ tl.1)
          (vaughanShortIntervalBudget Bcap)
        let K : ℝ := (dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget Bcap) sk : ℕ)
        let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
        let F := reciprocalPhaseScale N N 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ∑ m ∈ dyadicShortIntervalIndexedBlock
              (vaughanShortIntervalBudget Bcap) sk,
            ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) tl)
              γ N N 2 m‖ ^ 2 ≤
          (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
            L ^ 2 * ((qinner : ℝ) *
              (Q * (4 *
                  (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                    (1 - (1 / 1024 : ℝ))) * B *
                      F ^ (-(1 / 1024 : ℝ)))) +
                (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
                  3 * (Real.log P) ^ (-T))))) := by
  have hcallback :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_vaughanInnerBlockCallback
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hcallback,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hcallbackP hlogP
  intro a b Bcap γ N orders sk tl L d hBcap hlog hDouter hL hγ hN
    hrFive hrSix hd hFhigh hNupper hKlower
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinnerPos : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinnerPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by rfl
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    exact_mod_cast Nat.le_add_right (2 ^ sk.1) (sk.2 * qouter)
  have hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K :=
    hbudgetLarge.trans (hDouter.trans hDouterK)
  have hK : (2 : ℝ) ≤ K :=
    (by norm_num : (2 : ℝ) ≤ 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))).trans
      hKbudget
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    linarith
  have hB : 0 < B := by unfold B; positivity
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hFone : 1 ≤ F := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [F, K, B] using hFhigh)
  have hV : 0 ≤ 3 * (Real.log P) ^ (-T) := by positivity
  have hhigh :
      let qouter := dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget Bcap)
      let K : ℝ := (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget Bcap) sk : ℕ)
      let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
      ∀ n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl,
        ∀ n' ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget Bcap) tl, n ≠ n' →
          3 ≤ (Nat.dist n' n : ℝ) *
            reciprocalPhaseScale N N 2 (K * B) / B →
          K ^ 4 < reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K →
          let F := reciprocalPhaseScale N N 2 (K * B)
          let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
            (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
                (1 + Real.log (qouter : ℝ)) * K)
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) sk)
              N N 2 n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
              3 * (Real.log P) ^ (-T)) := by
    dsimp only
    intro n hnBlock n' hn'Block hne _ hpairHigh
    have hnShort : n ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2 := by
      simpa only [dyadicShortIntervalIndexedBlock, qinner] using hnBlock
    have hn'Short : n' ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2 := by
      simpa only [dyadicShortIntervalIndexedBlock, qinner] using hn'Block
    have hnData := mem_shortIntervalBlock.mp hnShort
    have hn'Data := mem_shortIntervalBlock.mp hn'Short
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hraw := hcallbackP a b Bcap (2 ^ sk.1) (2 * 2 ^ sk.1) qouter
      sk.2 N K n n' orders B F tl hKouter hK hqouter hqouterK hnBlock
        hn'Block hnpos hn'pos hne hN hB (zero_le_one.trans hFone) hNupper
        (by simpa only [K] using hKlower) hpairHigh.le
    simpa only [dyadicShortIntervalIndexedBlock, qouter, K, B, F] using hraw
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_quadratic_intrinsicError
      a b Bcap γ N orders sk tl hBcap hlog hDouter hL hγ hN hrFive hrSix hd
        hFhigh hV hhigh
  simpa only [qouter, qinner, K, B, F] using hresult

/-- Direct specialization to one pair of canonical Vaughan dyadic short
blocks.  All block geometry, positivity, and the five-block expansion margin
are discharged from the named decomposition. -/
theorem sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_fourStepWeyl_quadratic
    (a b Bcap : ℕ) (γ : ℕ → ℂ) (N : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) {L d : ℝ}
    (hBcap : 0 < Bcap) (hlog : 2 ≤ Real.log Bcap)
    (hDouter : (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ))
    (hDinner : (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ tl.1 : ℕ))
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L) (hN : N ≠ 0)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) (hd : 0 ≤ d)
    (hFhigh : (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N N 2
      (((dyadicShortIntervalLeftEndpoint (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)))
    (hFlow : 10 * reciprocalPhaseScale N N 2
        (((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
          ((2 * 2 ^ tl.1 : ℕ) : ℝ)) ≤
      ((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) ^ 4 *
        (Real.log Bcap) ^ 100)
    :
    let qouter := dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget Bcap)
    let qinner := dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget Bcap)
    let K : ℝ := (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget Bcap) sk : ℕ)
    let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
    let E := typeIIShortIntervalScaleErrorAt N N K B 2 (2 ^ tl.1) qinner tl.2
    let F := reciprocalPhaseScale N N 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) sk,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget Bcap) tl)
          γ N N 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * E ^ (1 / 1024 : ℝ)))) := by
  dsimp only
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinnerPos : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinnerPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by
    rfl
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hF : 1 ≤ reciprocalPhaseScale N N 2 (K * B) := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [K, B] using hFhigh)
  have hB : 0 < B := by unfold B; positivity
  have hKnat : 0 < (2 ^ sk.1) + sk.2 * qouter := by omega
  have hKpos : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hKone : (1 : ℝ) ≤ K := by rw [hKouter]; exact_mod_cast hKnat
  have hKB : 1 ≤ K * B := by
    have hpowOne : 1 ≤ 2 ^ tl.1 := one_le_pow₀ (by omega)
    have hBoneNat : 1 ≤ 2 * 2 ^ tl.1 := by omega
    have hBone : (1 : ℝ) ≤ B := by unfold B; exact_mod_cast hBoneNat
    simpa only [one_mul] using
      (mul_le_mul hKone hBone (by norm_num : (0 : ℝ) ≤ 1)
        (zero_le_one.trans hKone))
  have hS₁ : (((2 * 2 ^ tl.1 : ℕ) : ℝ)) ≤ B := by rfl
  have hqinnerNat : qinner ≤ 2 * 2 ^ tl.1 := by
    have hraw := dyadicShortIntervalLength_le_div_add_one
      (2 ^ tl.1) hbudget
    unfold qinner
    have hone : 1 ≤ 2 ^ tl.1 := one_le_pow₀ (by omega)
    have hdiv : 2 ^ tl.1 / vaughanShortIntervalBudget Bcap ≤ 2 ^ tl.1 :=
      Nat.div_le_self _ _
    omega
  have hqinnerB : (qinner : ℝ) ≤ B := by
    unfold B
    exact_mod_cast hqinnerNat
  have hBupper : B ≤ 2 * (((2 ^ tl.1) + tl.2 * qinner : ℕ) : ℝ) := by
    unfold B
    have hnat :
        2 * 2 ^ tl.1 ≤ 2 * ((2 ^ tl.1) + tl.2 * qinner) :=
      Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)
    exact_mod_cast hnat
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    have hnat : 2 ^ sk.1 ≤ 2 ^ sk.1 + sk.2 * qouter :=
      Nat.le_add_right _ _
    exact_mod_cast hnat
  have hDinnerR : ((2 ^ tl.1 : ℕ) : ℝ) ≤
      (((2 ^ tl.1) + tl.2 * qinner : ℕ) : ℝ) := by
    have hnat : 2 ^ tl.1 ≤ 2 ^ tl.1 + tl.2 * qinner :=
      Nat.le_add_right _ _
    exact_mod_cast hnat
  have hsourceLow : 10 * (qinner : ℝ) *
      reciprocalPhaseScale N N 2 (K * B) ≤
        K ^ 4 * (((2 ^ tl.1) + tl.2 * qinner : ℕ) : ℝ) := by
    apply ten_mul_vaughanShortIntervalLength_mul_le_pow_four_mul
      hBcap hlog hDinner
    · simpa only [K, B] using hFlow
    · exact hDinnerR
  have hscaleError : typeIIShortIntervalScaleErrorAt N N K B 2
      (2 ^ tl.1) qinner tl.2 ≤ 1 / K := by
    apply typeIIShortIntervalScaleErrorAt_quadratic_le_one_div_of_sourceScale
      N K B hKone hDinnerPos hB hBupper
    simpa only [K, B, qinner] using hsourceLow
  have hscaleBudget : 240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      typeIIShortIntervalScaleErrorAt N N K B 2
        (2 ^ tl.1) qinner tl.2 ≤ 1 / 4 := by
    apply mul_error_le_one_div_four_of_error_le_one_div
      (by positivity) hKpos hscaleError
    exact hbudgetLarge.trans (hDouter.trans hDouterK)
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : 5 * (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    exact hfiveQ.trans hDouterK
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_fourStepWeyl_quadratic
      a b γ N orders (2 ^ sk.1) (2 * 2 ^ sk.1) (2 ^ tl.1) (2 * 2 ^ tl.1)
      qouter qinner sk.2 tl.2 hDouterPos hDinnerPos hqouter hqinner hL hγ hN
      hKouter hB hKB hS₁ hqinnerB
      (by simpa only [K, B] using hF) hrFive hrSix
      hscaleError
      hscaleBudget hqouterK
  simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hresult

/-- Exact `r`-th derivative of one finite difference of the reciprocal
phase, expressed as the matching finite difference of its `r`-th derivative.
-/
theorem iteratedDeriv_realForwardDifferenceNat_reciprocalPhase
    (N M : ℝ) (j r d : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv r
        (realForwardDifferenceNat (reciprocalPhase N M j) d) x =
      realForwardDifferenceNat
        (iteratedDeriv r (reciprocalPhase N M j)) d x := by
  apply iteratedDeriv_realForwardDifferenceNat
  · exact contDiffAt_reciprocalPhase_of_pos N M j r (by positivity)
  · exact contDiffAt_reciprocalPhase_of_pos N M j r hx

/-- One unconditional van der Corput step for the exact reciprocal phase and
arbitrary half-open interval used by Proposition 1.12. -/
theorem norm_reciprocalPhaseSum_sq_mul_shift_le_differences
    (N M : ℝ) (j a b H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖reciprocalPhaseSum N M j a b‖ ^ 2 ≤
      2 * (((b - a) + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range (H + 1),
          ‖phaseExponentialSum
            (forwardPhaseDifference
              (fun n => reciprocalPhase N M j (a + n)) d)
            ((b - a) - d)‖ := by
  rw [reciprocalPhaseSum_eq_phaseExponentialSum_translate]
  exact norm_phaseExponentialSum_sq_mul_shift_le_differences _ _ _ hH

/-- Sharp-lag van der Corput step for the exact reciprocal-phase interval
sum; every new lag satisfies `d < H`. -/
theorem norm_reciprocalPhaseSum_sq_mul_shift_le_differences_sharp
    (N M : ℝ) (j a b H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖reciprocalPhaseSum N M j a b‖ ^ 2 ≤
      2 * (((b - a) + H : ℕ) : ℝ) *
        ∑ d ∈ Finset.range H,
          ‖phaseExponentialSum
            (forwardPhaseDifference
              (fun n => reciprocalPhase N M j (a + n)) d)
            ((b - a) - d)‖ := by
  rw [reciprocalPhaseSum_eq_phaseExponentialSum_translate]
  exact norm_phaseExponentialSum_sq_mul_shift_le_differences_sharp _ _ _ hH

end

end Tao2026
