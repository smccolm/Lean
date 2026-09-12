import Tao2026.SmoothNumberRankin
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Weighted prime sums for the smooth-number Rankin bound

The saddle-point form of Rankin's inequality leaves one finite weighted prime
sum.  This module performs the exact Abel transformation of that sum into the
prime-counting function.  It is deliberately lightweight and independent of
the complex-valued partial-summation layer used for prime equidistribution.
-/

namespace Tao2026

noncomputable section

/-- Exact finite Abel summation over primes at most `y`.  The endpoint uses
`Nat.primeCounting y`, while the remaining terms are backward differences of
the weight. -/
theorem sum_primesLE_eq_endpoint_add_primeCounting_differences
    (f : ℕ → ℝ) (y : ℕ) :
    ∑ p ∈ y.primesLE, f p =
      f y * (Nat.primeCounting y : ℝ) +
        ∑ n ∈ Finset.range y,
          (f n - f (n + 1)) * (Nat.primeCounting n : ℝ) := by
  let g : ℕ → ℝ := fun n => if n.Prime then 1 else 0
  have hprefix (n : ℕ) :
      ∑ i ∈ Finset.range n, g i = (Nat.primeCounting' n : ℝ) := by
    rw [← Nat.primesBelow_card_eq_primeCounting']
    simp [g, Nat.primesBelow_eq_filter_range]
  have hraw := Finset.sum_range_by_parts f g (y + 1)
  simp only [Nat.add_sub_cancel, hprefix, smul_eq_mul] at hraw
  calc
    ∑ p ∈ y.primesLE, f p = ∑ n ∈ Finset.range (y + 1), f n * g n := by
      rw [Nat.primesLE_eq_filter_range]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hnPrime : n.Prime <;> simp [g, hnPrime]
    _ = f y * (Nat.primeCounting y : ℝ) -
        ∑ n ∈ Finset.range y,
          (f (n + 1) - f n) * (Nat.primeCounting n : ℝ) := hraw
    _ = f y * (Nat.primeCounting y : ℝ) +
        ∑ n ∈ Finset.range y,
          (f n - f (n + 1)) * (Nat.primeCounting n : ℝ) := by
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro n _hn
      ring

/-- The zero and one terms in the Abel transform vanish, so only the natural
range `2 ≤ n < y` contributes. -/
theorem sum_primesLE_eq_endpoint_add_primeCounting_differences_Ico
    (f : ℕ → ℝ) (y : ℕ) :
    ∑ p ∈ y.primesLE, f p =
      f y * (Nat.primeCounting y : ℝ) +
        ∑ n ∈ Finset.Ico 2 y,
          (f n - f (n + 1)) * (Nat.primeCounting n : ℝ) := by
  rw [sum_primesLE_eq_endpoint_add_primeCounting_differences]
  congr 1
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  · intro n hnRange hnIco
    have hnlt : n < 2 := by
      have := Finset.mem_range.mp hnRange
      by_contra hn
      exact hnIco (Finset.mem_Ico.mpr ⟨by omega, this⟩)
    interval_cases n <;> simp

/-- Exact source-convention identity for the weighted prime sum in Rankin's
method. -/
theorem primeRpowSum_eq_endpoint_add_primeCounting_differences
    (y : ℕ) (sigma : ℝ) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) =
      (y : ℝ) ^ (-sigma) * (Nat.primeCounting y : ℝ) +
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            (Nat.primeCounting n : ℝ) := by
  rw [← Nat.primesLE_eq_filter_Icc_two]
  exact sum_primesLE_eq_endpoint_add_primeCounting_differences_Ico
    (fun n => (n : ℝ) ^ (-sigma)) y

/-- Positive powers in the Rankin range have nonnegative backward
differences. -/
theorem natCast_rpow_neg_backwardDifference_nonneg
    {n : ℕ} (hn : 1 ≤ n) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    0 ≤ (n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma) := by
  apply sub_nonneg.mpr
  exact Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast (Nat.zero_lt_of_lt hn))
    (by exact_mod_cast (Nat.le_succ n))
    (neg_nonpos.mpr hsigma)

/-- Bernoulli's inequality gives the sharp first-order upper bound for the
backward difference of `n ↦ n⁻ˢ` when `0 ≤ sigma ≤ 1`. -/
theorem natCast_rpow_neg_backwardDifference_le
    {n : ℕ} (hn : 1 ≤ n) {sigma : ℝ} (hsigma : 0 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    (n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma) ≤
      (n : ℝ) ^ (-sigma) * (sigma / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  let a : ℝ := 1 + 1 / (n : ℝ)
  have haOne : 1 ≤ a := by
    dsimp [a]
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  have haPos : 0 < a := zero_lt_one.trans_le haOne
  have hfracLower : (-1 : ℝ) ≤ 1 / (n : ℝ) := by
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hbern : a ^ sigma ≤ 1 + sigma * (1 / (n : ℝ)) := by
    simpa [a] using rpow_one_add_le_one_add_mul_self
      (p := sigma) (s := 1 / (n : ℝ)) hfracLower hsigma hsigmaOne
  have hbOne : 1 ≤ a ^ sigma := Real.one_le_rpow haOne hsigma
  have hbPos : 0 < a ^ sigma := Real.rpow_pos_of_pos haPos sigma
  have hgap : 1 - (a ^ sigma)⁻¹ ≤ a ^ sigma - 1 := by
    have hid : 1 - (a ^ sigma)⁻¹ = (a ^ sigma - 1) / a ^ sigma := by
      field_simp
    rw [hid, div_le_iff₀ hbPos]
    calc
      a ^ sigma - 1 = (a ^ sigma - 1) * 1 := by ring
      _ ≤ (a ^ sigma - 1) * a ^ sigma :=
        mul_le_mul_of_nonneg_left hbOne (sub_nonneg.mpr hbOne)
  have hbern' : a ^ sigma - 1 ≤ sigma / (n : ℝ) := by
    calc
      a ^ sigma - 1 ≤ sigma * (1 / (n : ℝ)) := by linarith [hbern]
      _ = sigma / (n : ℝ) := by ring
  have htail : 1 - a ^ (-sigma) ≤ sigma / (n : ℝ) := by
    rw [Real.rpow_neg haPos.le]
    exact hgap.trans hbern'
  have hfactor :
      ((n + 1 : ℕ) : ℝ) ^ (-sigma) = (n : ℝ) ^ (-sigma) * a ^ (-sigma) := by
    have hna : ((n + 1 : ℕ) : ℝ) = (n : ℝ) * a := by
      push_cast
      dsimp [a]
      field_simp
    rw [hna, Real.mul_rpow hnpos.le haPos.le]
  rw [hfactor]
  convert mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hnpos.le _) using 1
  ring

/-- Conditional Chebyshev consumer for the weighted prime sum.  Any explicit
upper bound for `Nat.primeCounting` on `[2,y]` can be substituted pointwise;
the nonnegative Abel coefficients preserve it term by term. -/
theorem primeRpowSum_le_of_primeCounting_le
    (y : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) (P : ℕ → ℝ)
    (hP : ∀ n, 0 ≤ P n)
    (hpi : ∀ n, 2 ≤ n → n ≤ y → (Nat.primeCounting n : ℝ) ≤ P n) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      (y : ℝ) ^ (-sigma) * P y +
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) * P n := by
  rw [primeRpowSum_eq_endpoint_add_primeCounting_differences]
  by_cases hy : 2 ≤ y
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hpi y hy le_rfl)
        (Real.rpow_nonneg (by positivity) _)
    · apply Finset.sum_le_sum
      intro n hn
      have hnBounds := Finset.mem_Ico.mp hn
      exact mul_le_mul_of_nonneg_left
        (hpi n hnBounds.1 hnBounds.2.le)
        (natCast_rpow_neg_backwardDifference_nonneg
          (by omega) hsigma)
  · have hySmall : y ≤ 1 := by omega
    have hpiZero : Nat.primeCounting y = 0 := Nat.primeCounting_eq_zero_iff.mpr hySmall
    have hIco : Finset.Ico 2 y = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hIco]
    simp only [Finset.sum_empty, add_zero, hpiZero, Nat.cast_zero, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (hP y)

/-- Mathlib's fully explicit Chebyshev majorant, specialized to natural
arguments. -/
def chebyshevPrimeCountingMajorant (n : ℕ) : ℝ :=
  Real.log 4 * (n : ℝ) / Real.log (Real.sqrt n) + Real.sqrt n

theorem chebyshevPrimeCountingMajorant_nonneg (n : ℕ) :
    0 ≤ chebyshevPrimeCountingMajorant n := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num [chebyshevPrimeCountingMajorant]
  · have hnReal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (Real.sqrt (n : ℝ)) := by
      exact Real.log_pos (Real.lt_sqrt_of_sq_lt (by simpa using hnReal))
    unfold chebyshevPrimeCountingMajorant
    exact add_nonneg
      (div_nonneg
        (mul_nonneg (Real.log_nonneg (by norm_num)) (by positivity)) hlog.le)
      (Real.sqrt_nonneg _)

/-- The explicit Chebyshev estimate from Mathlib, in the exact pointwise form
consumed by the finite Abel inequality. -/
theorem primeCounting_cast_le_chebyshevPrimeCountingMajorant
    {n : ℕ} (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ chebyshevPrimeCountingMajorant n := by
  have hnReal : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le one_lt_two hn)
  simpa [chebyshevPrimeCountingMajorant] using
    (Chebyshev.pi_le_log4_mul_div (x := (n : ℝ)) hnReal)

/-- A convenient elementary estimate used to absorb the square-root remainder
in the explicit Chebyshev bound. -/
theorem sqrt_le_two_mul_self_div_log {x : ℝ} (hx : 1 < x) :
    Real.sqrt x ≤ 2 * x / Real.log x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx.le
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    convert h using 1
    ring
  rw [le_div_iff₀ (Real.log_pos hx)]
  calc
    Real.sqrt x * Real.log x ≤ Real.sqrt x * (2 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    _ = 2 * (Real.sqrt x * Real.sqrt x) := by ring
    _ = 2 * x := by rw [Real.mul_self_sqrt hx0]

/-- A clean global `C n / log n` majorant for the prime-counting function,
with the explicit constant inherited from Chebyshev's theorem. -/
def logarithmicPrimeCountingMajorant (n : ℕ) : ℝ :=
  (2 * Real.log 4 + 2) * (n : ℝ) / Real.log n

/-- The explicit constant in `logarithmicPrimeCountingMajorant`. -/
def smoothPrimeCountingConstant : ℝ := 2 * Real.log 4 + 2

theorem smoothPrimeCountingConstant_pos : 0 < smoothPrimeCountingConstant := by
  unfold smoothPrimeCountingConstant
  positivity

theorem chebyshevPrimeCountingMajorant_le_logarithmic
    {n : ℕ} (hn : 2 ≤ n) :
    chebyshevPrimeCountingMajorant n ≤ logarithmicPrimeCountingMajorant n := by
  have hnReal : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le one_lt_two hn)
  have hlogNe : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hnReal).ne'
  unfold chebyshevPrimeCountingMajorant logarithmicPrimeCountingMajorant
  rw [Real.log_sqrt (Nat.cast_nonneg n)]
  have hfirst :
      Real.log 4 * (n : ℝ) / (Real.log n / 2) =
        2 * Real.log 4 * (n : ℝ) / Real.log n := by
    field_simp
  rw [hfirst]
  grw [sqrt_le_two_mul_self_div_log hnReal]
  field_simp
  norm_num

theorem logarithmicPrimeCountingMajorant_nonneg (n : ℕ) :
    0 ≤ logarithmicPrimeCountingMajorant n := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num [logarithmicPrimeCountingMajorant]
  · unfold logarithmicPrimeCountingMajorant
    positivity

theorem primeCounting_cast_le_logarithmicPrimeCountingMajorant
    {n : ℕ} (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ logarithmicPrimeCountingMajorant n :=
  (primeCounting_cast_le_chebyshevPrimeCountingMajorant hn).trans
    (chebyshevPrimeCountingMajorant_le_logarithmic hn)

/-- Unconditional weighted-prime estimate obtained by combining exact Abel
summation with Mathlib's explicit Chebyshev bound.  This is the analytic input
needed before optimizing the Rankin saddle parameter. -/
theorem primeRpowSum_le_chebyshevMajorant
    (y : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      (y : ℝ) ^ (-sigma) * chebyshevPrimeCountingMajorant y +
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            chebyshevPrimeCountingMajorant n := by
  exact primeRpowSum_le_of_primeCounting_le y hsigma chebyshevPrimeCountingMajorant
    chebyshevPrimeCountingMajorant_nonneg
    (fun n hn _hny => primeCounting_cast_le_chebyshevPrimeCountingMajorant hn)

/-- Abel summation with the simplified global `C n / log n` Chebyshev
majorant. -/
theorem primeRpowSum_le_logarithmicPrimeCountingMajorant
    (y : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      (y : ℝ) ^ (-sigma) * logarithmicPrimeCountingMajorant y +
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            logarithmicPrimeCountingMajorant n := by
  exact primeRpowSum_le_of_primeCounting_le y hsigma logarithmicPrimeCountingMajorant
    logarithmicPrimeCountingMajorant_nonneg
    (fun n hn _hny => primeCounting_cast_le_logarithmicPrimeCountingMajorant hn)

/-- The logarithmic Chebyshev reduction with every backward difference
replaced by its sharp Bernoulli first-order majorant. -/
theorem primeRpowSum_le_logarithmicPrimeCountingMajorant_firstOrder
    (y : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      (y : ℝ) ^ (-sigma) * logarithmicPrimeCountingMajorant y +
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) * (sigma / n)) *
            logarithmicPrimeCountingMajorant n := by
  refine (primeRpowSum_le_logarithmicPrimeCountingMajorant y hsigma).trans ?_
  have hsum :
      (∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
            logarithmicPrimeCountingMajorant n) ≤
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (-sigma) * (sigma / n)) *
            logarithmicPrimeCountingMajorant n := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right
      (natCast_rpow_neg_backwardDifference_le
        (le_trans (by norm_num) (Finset.mem_Ico.mp hn).1) hsigma hsigmaOne)
      (logarithmicPrimeCountingMajorant_nonneg n)
  exact add_le_add_right hsum _

theorem rpow_neg_mul_self {x sigma : ℝ} (hx : 0 < x) :
    x ^ (-sigma) * x = x ^ (1 - sigma) := by
  calc
    x ^ (-sigma) * x = x ^ (-sigma) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ (-sigma + 1) := (Real.rpow_add hx _ _).symm
    _ = x ^ (1 - sigma) := by congr 1; ring

theorem firstOrder_mul_logarithmicPrimeCountingMajorant
    {n : ℕ} (hn : 2 ≤ n) (sigma : ℝ) :
    ((n : ℝ) ^ (-sigma) * (sigma / n)) *
        logarithmicPrimeCountingMajorant n =
      smoothPrimeCountingConstant * sigma * (n : ℝ) ^ (-sigma) / Real.log n := by
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  have hlogNe : Real.log (n : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hn))).ne'
  unfold logarithmicPrimeCountingMajorant smoothPrimeCountingConstant
  field_simp

theorem endpoint_mul_logarithmicPrimeCountingMajorant
    {y : ℕ} (hy : 2 ≤ y) (sigma : ℝ) :
    (y : ℝ) ^ (-sigma) * logarithmicPrimeCountingMajorant y =
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y := by
  have hlogNe : Real.log (y : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))).ne'
  unfold logarithmicPrimeCountingMajorant smoothPrimeCountingConstant
  field_simp
  rw [rpow_neg_mul_self (by positivity)]

/-- Canonical finite weighted-prime estimate.  The prime-counting and
backward-difference layers have disappeared; the remaining sum is exactly
`sum n⁻ˢ / log n`. -/
theorem primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
        smoothPrimeCountingConstant * sigma *
          ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n := by
  refine (primeRpowSum_le_logarithmicPrimeCountingMajorant_firstOrder
    y hsigma hsigmaOne).trans_eq ?_
  rw [endpoint_mul_logarithmicPrimeCountingMajorant hy sigma, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [firstOrder_mul_logarithmicPrimeCountingMajorant
    (Finset.mem_Ico.mp hn).1 sigma]
  ring

/-- A backward difference of `n^(1-sigma)` dominates its right-endpoint
derivative.  This is the discrete integral comparison for `n^(-sigma)`. -/
theorem one_sub_mul_rpow_neg_le_rpow_one_sub_backwardDifference
    {n : ℕ} (hn : 2 ≤ n) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1) :
    (1 - sigma) * (n : ℝ) ^ (-sigma) ≤
      (n : ℝ) ^ (1 - sigma) - (n - 1 : ℕ) ^ (1 - sigma) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hdeltaPos : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  have hdeltaOne : 1 - sigma ≤ 1 := by linarith
  let a : ℝ := 1 - 1 / (n : ℝ)
  have haNonneg : 0 ≤ a := by
    dsimp [a]
    rw [sub_nonneg, div_le_one hnpos]
    exact_mod_cast (le_trans (by norm_num) hn)
  have hbern : a ^ (1 - sigma) ≤ 1 - (1 - sigma) / (n : ℝ) := by
    have ht : (-1 : ℝ) ≤ -(1 / (n : ℝ)) := by
      have hone : 1 / (n : ℝ) ≤ 1 := by
        rw [div_le_one hnpos]
        exact_mod_cast (le_trans (by norm_num) hn)
      linarith
    have h := rpow_one_add_le_one_add_mul_self
      (p := 1 - sigma) (s := -(1 / (n : ℝ))) ht hdeltaPos.le hdeltaOne
    convert h using 1
    ring
  have hfactor :
      ((n - 1 : ℕ) : ℝ) ^ (1 - sigma) =
        (n : ℝ) ^ (1 - sigma) * a ^ (1 - sigma) := by
    have hna : ((n - 1 : ℕ) : ℝ) = (n : ℝ) * a := by
      rw [Nat.cast_sub (le_trans (by norm_num) hn)]
      push_cast
      dsimp [a]
      field_simp
    rw [hna, Real.mul_rpow hnpos.le haNonneg]
  have hscale :
      (1 - sigma) * (n : ℝ) ^ (-sigma) =
        (n : ℝ) ^ (1 - sigma) * ((1 - sigma) / (n : ℝ)) := by
    field_simp
    rw [rpow_neg_mul_self hnpos]
  rw [hscale, hfactor]
  calc
    (n : ℝ) ^ (1 - sigma) * ((1 - sigma) / (n : ℝ)) ≤
        (n : ℝ) ^ (1 - sigma) * (1 - a ^ (1 - sigma)) :=
      mul_le_mul_of_nonneg_left (by linarith [hbern])
        (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ) ^ (1 - sigma) -
        (n : ℝ) ^ (1 - sigma) * a ^ (1 - sigma) := by ring

/-- Backward differences telescope on a natural half-open interval. -/
theorem sum_Ico_backwardDifference_pred
    (f : ℕ → ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n - 1)) = f (b - 1) - f (a - 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab', ih hab']
        simp only [Nat.add_sub_cancel]
        ring
      · have haEq : a = b + 1 := by omega
        subst a
        simp

/-- Elementary finite `p`-sum bound in the saddle range. -/
theorem sum_rpow_neg_Ico_le
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) ≤
      (y : ℝ) ^ (1 - sigma) / (1 - sigma) := by
  have hdeltaPos : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  rw [le_div_iff₀ hdeltaPos]
  rw [Finset.sum_mul]
  calc
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) * (1 - sigma) ≤
        ∑ n ∈ Finset.Ico 2 y,
          ((n : ℝ) ^ (1 - sigma) - (n - 1 : ℕ) ^ (1 - sigma)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [mul_comm]
      exact one_sub_mul_rpow_neg_le_rpow_one_sub_backwardDifference
        (Finset.mem_Ico.mp hn).1 hsigma hsigmaOne
    _ = (y - 1 : ℕ) ^ (1 - sigma) - 1 := by
      rw [sum_Ico_backwardDifference_pred (fun n => (n : ℝ) ^ (1 - sigma))
        (by norm_num) hy]
      norm_num
    _ ≤ (y : ℝ) ^ (1 - sigma) := by
      have hmono : ((y - 1 : ℕ) : ℝ) ^ (1 - sigma) ≤
          (y : ℝ) ^ (1 - sigma) := by
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.sub_le y 1)
          hdeltaPos.le
      linarith

/-- Local finite integral comparison retaining both endpoints.  Unlike the
coarse global corollary below, this form keeps the cancellation that is
needed when `1-sigma` is small. -/
theorem sum_rpow_neg_Ico_interval_le
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico a b, (n : ℝ) ^ (-sigma) ≤
      (((b - 1 : ℕ) : ℝ) ^ (1 - sigma) -
        ((a - 1 : ℕ) : ℝ) ^ (1 - sigma)) / (1 - sigma) := by
  have hdeltaPos : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  rw [le_div_iff₀ hdeltaPos]
  rw [Finset.sum_mul]
  calc
    ∑ n ∈ Finset.Ico a b, (n : ℝ) ^ (-sigma) * (1 - sigma) ≤
        ∑ n ∈ Finset.Ico a b,
          ((n : ℝ) ^ (1 - sigma) - (n - 1 : ℕ) ^ (1 - sigma)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [mul_comm]
      exact one_sub_mul_rpow_neg_le_rpow_one_sub_backwardDifference
        (le_trans ha (Finset.mem_Ico.mp hn).1) hsigma hsigmaOne
    _ = ((b - 1 : ℕ) : ℝ) ^ (1 - sigma) -
        ((a - 1 : ℕ) : ℝ) ^ (1 - sigma) := by
      exact sum_Ico_backwardDifference_pred
        (fun n => (n : ℝ) ^ (1 - sigma)) (by omega) hab

/-- Local power-log comparison on `[a,b)`, retaining the exact difference of
the two endpoint powers and the denominator `log a`. -/
theorem sum_rpow_neg_div_log_Ico_interval_le
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico a b, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ((((b - 1 : ℕ) : ℝ) ^ (1 - sigma) -
          ((a - 1 : ℕ) : ℝ) ^ (1 - sigma)) / (1 - sigma)) /
        Real.log a := by
  have hlogA : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two ha))
  calc
    ∑ n ∈ Finset.Ico a b, (n : ℝ) ^ (-sigma) / Real.log n ≤
        ∑ n ∈ Finset.Ico a b, (n : ℝ) ^ (-sigma) / Real.log a := by
      apply Finset.sum_le_sum
      intro n hn
      have han : a ≤ n := (Finset.mem_Ico.mp hn).1
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
        hlogA (Real.strictMonoOn_log.monotoneOn
          (show (0 : ℝ) < a by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two ha))
          (show (0 : ℝ) < n by
            exact_mod_cast (lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_two ha) han))
          (by exact_mod_cast han))
    _ = (∑ n ∈ Finset.Ico a b, (n : ℝ) ^ (-sigma)) / Real.log a := by
      rw [Finset.sum_div]
    _ ≤ ((((b - 1 : ℕ) : ℝ) ^ (1 - sigma) -
          ((a - 1 : ℕ) : ℝ) ^ (1 - sigma)) / (1 - sigma)) /
        Real.log a :=
      div_le_div_of_nonneg_right
        (sum_rpow_neg_Ico_interval_le ha hab hsigma hsigmaOne) hlogA.le

/-- A complementary local estimate using interval cardinality and monotonicity
of both factors.  This avoids the factor `(1-sigma)⁻¹` on short geometric
blocks. -/
theorem sum_rpow_neg_div_log_Ico_le_card_mul
    {a b : ℕ} (ha : 2 ≤ a) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) :
    ∑ n ∈ Finset.Ico a b, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ((b - a : ℕ) : ℝ) * (a : ℝ) ^ (-sigma) / Real.log a := by
  have hlogA : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two ha))
  calc
    ∑ n ∈ Finset.Ico a b, (n : ℝ) ^ (-sigma) / Real.log n ≤
        ∑ _n ∈ Finset.Ico a b, (a : ℝ) ^ (-sigma) / Real.log a := by
      apply Finset.sum_le_sum
      intro n hn
      have han : a ≤ n := (Finset.mem_Ico.mp hn).1
      have haPos : (0 : ℝ) < a := by positivity
      have hnPos : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_two ha) han)
      have hpow : (n : ℝ) ^ (-sigma) ≤ (a : ℝ) ^ (-sigma) :=
        Real.rpow_le_rpow_of_nonpos haPos (by exact_mod_cast han)
          (neg_nonpos.mpr hsigma)
      have hlog : Real.log (a : ℝ) ≤ Real.log (n : ℝ) :=
        Real.strictMonoOn_log.monotoneOn haPos hnPos (by exact_mod_cast han)
      calc
        (n : ℝ) ^ (-sigma) / Real.log n ≤
            (a : ℝ) ^ (-sigma) / Real.log n :=
          div_le_div_of_nonneg_right hpow (Real.log_pos (by
            exact_mod_cast (lt_of_lt_of_le one_lt_two (ha.trans han)))).le
        _ ≤ (a : ℝ) ^ (-sigma) / Real.log a :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
            hlogA hlog
    _ = ((b - a : ℕ) : ℝ) * (a : ℝ) ^ (-sigma) / Real.log a := by
      simp
      ring

/-- A global power-log bound obtained from the finite `p`-sum estimate and
the uniform denominator `log 2`.  The sharper saddle estimate will refine
this by splitting the range, but this theorem already closes the entire
finite summation step with explicit constants. -/
theorem sum_rpow_neg_div_log_Ico_le
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
        ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnTwo : 2 ≤ n := (Finset.mem_Ico.mp hn).1
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
        hlogTwo (Real.strictMonoOn_log.monotoneOn (by norm_num)
          (show (0 : ℝ) < n by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hnTwo))
          (show (2 : ℝ) ≤ n by exact_mod_cast hnTwo))
    _ = (∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma)) / Real.log 2 := by
      rw [Finset.sum_div]
    _ ≤ ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) / Real.log 2 :=
      div_le_div_of_nonneg_right
        (sum_rpow_neg_Ico_le hy hsigma hsigmaOne) hlogTwo.le
    _ = (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2) := by
      field_simp

/-- On an upper subrange `[k,y)`, retain the stronger denominator `log k`
instead of falling back to `log 2`. -/
theorem sum_rpow_neg_div_log_Ico_upper_le
    {k y : ℕ} (hk : 2 ≤ k) (hky : k ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico k y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log k) := by
  have hlogK : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hk))
  have hsumSubset :
      (∑ n ∈ Finset.Ico k y, (n : ℝ) ^ (-sigma)) ≤
        ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_Ico.mpr
        ⟨le_trans hk (Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2⟩
    · intro n _hn _hnSmall
      exact Real.rpow_nonneg (by positivity) _
  calc
    ∑ n ∈ Finset.Ico k y, (n : ℝ) ^ (-sigma) / Real.log n ≤
        ∑ n ∈ Finset.Ico k y, (n : ℝ) ^ (-sigma) / Real.log k := by
      apply Finset.sum_le_sum
      intro n hn
      have hkn : k ≤ n := (Finset.mem_Ico.mp hn).1
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
        hlogK (Real.strictMonoOn_log.monotoneOn
          (show (0 : ℝ) < k by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk))
          (show (0 : ℝ) < n by
            exact_mod_cast (lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_two hk) hkn))
          (by exact_mod_cast hkn))
    _ = (∑ n ∈ Finset.Ico k y, (n : ℝ) ^ (-sigma)) / Real.log k := by
      rw [Finset.sum_div]
    _ ≤ (∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma)) / Real.log k :=
      div_le_div_of_nonneg_right hsumSubset hlogK.le
    _ ≤ ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) / Real.log k :=
      div_le_div_of_nonneg_right
        (sum_rpow_neg_Ico_le (le_trans hk hky) hsigma hsigmaOne) hlogK.le
    _ = (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log k) := by
      field_simp

/-- Two-scale power-log estimate.  The initial range pays only `log 2`, but
its power scale is `k^(1-sigma)`; the long upper range gains `log k` while
retaining the full `y^(1-sigma)` scale. -/
theorem sum_rpow_neg_div_log_Ico_le_split
    {k y : ℕ} (hk : 2 ≤ k) (hky : k ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      (k : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2) +
        (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log k) := by
  rw [← Finset.sum_Ico_consecutive _ hk hky]
  exact add_le_add
    (sum_rpow_neg_div_log_Ico_le hk hsigma hsigmaOne)
    (sum_rpow_neg_div_log_Ico_upper_le hk hky hsigma hsigmaOne)

/-- Two-scale comparison retaining the endpoint cancellation in each range.
This is the finite building block for a multi-scale critical-regime estimate. -/
theorem sum_rpow_neg_div_log_Ico_le_split_sharp
    {k y : ℕ} (hk : 2 ≤ k) (hky : k ≤ y) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ((((k - 1 : ℕ) : ℝ) ^ (1 - sigma) - 1) / (1 - sigma)) /
          Real.log 2 +
        ((((y - 1 : ℕ) : ℝ) ^ (1 - sigma) -
            ((k - 1 : ℕ) : ℝ) ^ (1 - sigma)) / (1 - sigma)) /
          Real.log k := by
  rw [← Finset.sum_Ico_consecutive _ hk hky]
  have hfirst := sum_rpow_neg_div_log_Ico_interval_le (a := 2) (b := k)
    (by norm_num) hk hsigma hsigmaOne
  have hsecond := sum_rpow_neg_div_log_Ico_interval_le (a := k) (b := y)
    hk hky hsigma hsigmaOne
  simpa using add_le_add hfirst hsecond

/-- The endpoint-sensitive majorant contributed by one cutoff interval. -/
def smoothPowerLogIntervalMajorant (a b : ℕ) (sigma : ℝ) : ℝ :=
  ((((b - 1 : ℕ) : ℝ) ^ (1 - sigma) -
      ((a - 1 : ℕ) : ℝ) ^ (1 - sigma)) / (1 - sigma)) /
    Real.log a

/-- Sum of the endpoint-sensitive majorants along a cutoff chain. -/
def smoothPowerLogChainMajorant (c : ℕ → ℕ) (m : ℕ) (sigma : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m,
    smoothPowerLogIntervalMajorant (c i) (c (i + 1)) sigma

/-- Consecutive half-open intervals along a monotone chain reassemble into
one interval. -/
theorem sum_sum_Ico_monotone_chain
    (c : ℕ → ℕ) (hc : Monotone c) (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, ∑ n ∈ Finset.Ico (c i) (c (i + 1)), f n =
      ∑ n ∈ Finset.Ico (c 0) (c m), f n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      exact Finset.sum_Ico_consecutive _
        (hc (Nat.zero_le m)) (hc (Nat.le_succ m))

/-- Multi-scale finite power-log estimate along any monotone natural cutoff
chain.  Each scale retains both endpoint powers and its own logarithmic
denominator. -/
theorem sum_rpow_neg_div_log_Ico_le_monotone_chain
    (c : ℕ → ℕ) (hc : Monotone c) (hc0 : 2 ≤ c 0) (m : ℕ)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico (c 0) (c m), (n : ℝ) ^ (-sigma) / Real.log n ≤
      smoothPowerLogChainMajorant c m sigma := by
  unfold smoothPowerLogChainMajorant smoothPowerLogIntervalMajorant
  rw [← sum_sum_Ico_monotone_chain c hc
    (fun n => (n : ℝ) ^ (-sigma) / Real.log n) m]
  apply Finset.sum_le_sum
  intro i hi
  exact sum_rpow_neg_div_log_Ico_interval_le
    (hc0.trans (hc (Nat.zero_le i))) (hc (Nat.le_succ i)) hsigma hsigmaOne

/-- Dyadic cutoff chain, saturated at the terminal smoothness bound `y`. -/
def smoothDyadicCutoff (y i : ℕ) : ℕ :=
  min y (2 ^ (i + 1))

/-- Number of dyadic steps required to reach `y`. -/
def smoothDyadicDepth (y : ℕ) : ℕ :=
  Nat.clog 2 y

/-- Nonempty dyadic intervals required after starting at `2`. -/
def smoothDyadicSteps (y : ℕ) : ℕ :=
  (smoothDyadicDepth y).pred

theorem monotone_smoothDyadicCutoff (y : ℕ) :
    Monotone (smoothDyadicCutoff y) := by
  intro i j hij
  unfold smoothDyadicCutoff
  exact min_le_min_left y
    (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right hij 1))

@[simp]
theorem smoothDyadicCutoff_zero {y : ℕ} (hy : 2 ≤ y) :
    smoothDyadicCutoff y 0 = 2 := by
  simp [smoothDyadicCutoff, min_eq_right hy]

@[simp]
theorem smoothDyadicCutoff_self (y : ℕ) :
    smoothDyadicCutoff y y = y := by
  unfold smoothDyadicCutoff
  rw [min_eq_left]
  exact (show y < 2 ^ y from Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ y))

@[simp]
theorem smoothDyadicCutoff_depth (y : ℕ) :
    smoothDyadicCutoff y (smoothDyadicDepth y) = y := by
  unfold smoothDyadicCutoff smoothDyadicDepth
  rw [min_eq_left]
  exact (Nat.le_pow_clog (by norm_num) y).trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))

@[simp]
theorem smoothDyadicCutoff_steps
    {y : ℕ} (hy : 2 ≤ y) :
    smoothDyadicCutoff y (smoothDyadicSteps y) = y := by
  have hdepthPos : 0 < smoothDyadicDepth y := by
    exact Nat.clog_pos (by norm_num) (by omega)
  unfold smoothDyadicCutoff smoothDyadicSteps
  rw [min_eq_left]
  have hpred : (smoothDyadicDepth y).pred + 1 = smoothDyadicDepth y :=
    by simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hdepthPos
  rw [hpred]
  exact Nat.le_pow_clog (by norm_num) y

/-- For `y ≥ 2`, the active block count is exactly one less than the dyadic
depth. -/
theorem smoothDyadicSteps_add_one
    {y : ℕ} (hy : 2 ≤ y) :
    smoothDyadicSteps y + 1 = smoothDyadicDepth y := by
  have hdepthPos : 0 < smoothDyadicDepth y := by
    exact Nat.clog_pos (by norm_num) (by omega)
  unfold smoothDyadicSteps
  simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hdepthPos

/-- The real logarithm of `y` is at most its dyadic depth times `log 2`. -/
theorem log_le_smoothDyadicDepth_mul_log_two
    {y : ℕ} (hy : 2 ≤ y) :
    Real.log y ≤ (smoothDyadicDepth y : ℝ) * Real.log 2 := by
  have hyPos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hpow : y ≤ 2 ^ smoothDyadicDepth y :=
    Nat.le_pow_clog (by norm_num) y
  have hpowR : (y : ℝ) ≤ ((2 ^ smoothDyadicDepth y : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log hyPos hpowR
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
  exact hlog

/-- The denominator at the midpoint of the dyadic block range already
captures at least half of `log y`. -/
theorem half_log_le_midpoint_mul_log_two
    {y : ℕ} (hy : 2 ≤ y) :
    Real.log y / 2 ≤
      ((smoothDyadicSteps y / 2 + 1 : ℕ) : ℝ) * Real.log 2 := by
  have hdepth : smoothDyadicDepth y ≤
      2 * (smoothDyadicSteps y / 2 + 1) := by
    rw [← smoothDyadicSteps_add_one hy]
    omega
  have hcast : (smoothDyadicDepth y : ℝ) ≤
      2 * ((smoothDyadicSteps y / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hdepth
  have hlogTwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hmul := mul_le_mul_of_nonneg_right hcast hlogTwo
  have hylog := log_le_smoothDyadicDepth_mul_log_two hy
  nlinarith

/-- The terminal dyadic power overshoots `y` by a factor strictly smaller
than two. -/
theorem two_pow_smoothDyadicDepth_lt_two_mul
    {y : ℕ} (hy : 2 ≤ y) :
    2 ^ smoothDyadicDepth y < 2 * y := by
  have hdepthPos : 0 < smoothDyadicDepth y := by
    exact Nat.clog_pos (by norm_num) (by omega)
  have hpred : (smoothDyadicDepth y).pred < smoothDyadicDepth y :=
    Nat.pred_lt hdepthPos.ne'
  have hpow : 2 ^ (smoothDyadicDepth y).pred < y :=
    Nat.pow_lt_of_lt_clog hpred
  rw [← Nat.succ_pred_eq_of_pos hdepthPos, pow_succ]
  omega

/-- The logarithmic prefix factor is controlled by the logarithm of the
continuous dyadic depth `log (2y) / log 2`. -/
theorem smoothDyadicPrefixLog_le_log_logScale
    {y : ℕ} (hy : 2 ≤ y) :
    1 + Real.log (smoothDyadicSteps y / 2 : ℕ) ≤
      1 + Real.log (Real.log (2 * (y : ℝ)) / Real.log 2) := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hyPos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have htwoYPos : (0 : ℝ) < 2 * (y : ℝ) := by positivity
  have hpowR : (((2 ^ smoothDyadicDepth y : ℕ) : ℝ)) <
      2 * (y : ℝ) := by
    exact_mod_cast two_pow_smoothDyadicDepth_lt_two_mul hy
  have hlogPow := Real.strictMonoOn_log
    (by positivity : (0 : ℝ) < ((2 ^ smoothDyadicDepth y : ℕ) : ℝ))
    htwoYPos hpowR
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlogPow
  have hdepthRatio : (smoothDyadicDepth y : ℝ) <
      Real.log (2 * (y : ℝ)) / Real.log 2 := by
    rw [lt_div_iff₀ hlogTwo]
    simpa [mul_comm] using hlogPow
  have hdepthPos : 0 < smoothDyadicDepth y :=
    Nat.clog_pos (by norm_num) (by omega)
  have hratioOne : (1 : ℝ) <
      Real.log (2 * (y : ℝ)) / Real.log 2 :=
    lt_of_le_of_lt (by exact_mod_cast hdepthPos) hdepthRatio
  have hkNat : smoothDyadicSteps y / 2 ≤ smoothDyadicDepth y :=
    (Nat.div_le_self _ _).trans (by
      unfold smoothDyadicSteps
      exact Nat.pred_le _)
  have hkDepth : ((smoothDyadicSteps y / 2 : ℕ) : ℝ) ≤
      (smoothDyadicDepth y : ℝ) := by exact_mod_cast hkNat
  have hk : ((smoothDyadicSteps y / 2 : ℕ) : ℝ) ≤
      Real.log (2 * (y : ℝ)) / Real.log 2 :=
    hkDepth.trans hdepthRatio.le
  by_cases hkZero : smoothDyadicSteps y / 2 = 0
  · simp [hkZero, Real.log_nonneg hratioOne.le]
  · have hkPos : (0 : ℝ) < (smoothDyadicSteps y / 2 : ℕ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hkZero)
    have hlog := Real.log_le_log hkPos hk
    linarith

/-- Consequently the terminal exponential in the scalar midpoint estimate is
bounded by the source-scale power `(2y)^delta`. -/
theorem smoothDyadicTerminalExponential_le
    {y : ℕ} (hy : 2 ≤ y) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (((2 : ℝ) ^ delta) ^ (smoothDyadicSteps y + 1)) ≤
      (2 * (y : ℝ)) ^ delta := by
  have hpowR : (((2 ^ smoothDyadicDepth y : ℕ) : ℝ)) ≤
      2 * (y : ℝ) := by
    exact_mod_cast (two_pow_smoothDyadicDepth_lt_two_mul hy).le
  calc
    (((2 : ℝ) ^ delta) ^ (smoothDyadicSteps y + 1)) =
        (2 : ℝ) ^ (((smoothDyadicSteps y + 1 : ℕ) : ℝ) * delta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ = (2 : ℝ) ^ ((smoothDyadicDepth y : ℝ) * delta) := by
      rw [smoothDyadicSteps_add_one hy]
    _ = (((2 ^ smoothDyadicDepth y : ℕ) : ℝ)) ^ delta := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast,
        Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 * (y : ℝ)) ^ delta :=
      Real.rpow_le_rpow (by positivity) hpowR hdelta

/-- Before the terminal dyadic step, saturation has not occurred. -/
theorem smoothDyadicCutoff_eq_pow_of_lt_steps
    {y i : ℕ} (hi : i < smoothDyadicSteps y) :
    smoothDyadicCutoff y i = 2 ^ (i + 1) := by
  have hpredPos : 0 < (smoothDyadicDepth y).pred := by
    exact lt_of_le_of_lt (Nat.zero_le i) hi
  have hdepthPos : 0 < smoothDyadicDepth y :=
    hpredPos.trans_le (Nat.pred_le _)
  have hpred : (smoothDyadicDepth y).pred + 1 = smoothDyadicDepth y :=
    by simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hdepthPos
  have hiDepth : i + 1 < smoothDyadicDepth y := by
    unfold smoothDyadicSteps at hi
    have := Nat.add_lt_add_right hi 1
    rw [hpred] at this
    exact this
  have hpow : 2 ^ (i + 1) < y := by
    exact Nat.pow_lt_of_lt_clog hiDepth
  simp [smoothDyadicCutoff, min_eq_right hpow.le]

/-- Explicit envelope for one dyadic interval. -/
def smoothDyadicIntervalEnvelope (i : ℕ) (sigma : ℝ) : ℝ :=
  (((2 ^ (i + 2) : ℕ) : ℝ) ^ (1 - sigma)) /
    ((1 - sigma) * Real.log ((2 ^ (i + 1) : ℕ) : ℝ))

theorem smoothDyadicIntervalEnvelope_eq (i : ℕ) (sigma : ℝ) :
    smoothDyadicIntervalEnvelope i sigma =
      (2 : ℝ) ^ ((i + 2 : ℕ) * (1 - sigma)) /
        ((1 - sigma) * ((i + 1 : ℕ) * Real.log 2)) := by
  unfold smoothDyadicIntervalEnvelope
  push_cast
  rw [Real.log_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num [Nat.cast_add]

/-- Sharper dyadic block envelope obtained from the block cardinality. -/
def smoothDyadicBlockEnvelope (i : ℕ) (sigma : ℝ) : ℝ :=
  (((2 ^ (i + 1) : ℕ) : ℝ) ^ (1 - sigma)) /
    Real.log ((2 ^ (i + 1) : ℕ) : ℝ)

theorem smoothDyadicBlockEnvelope_eq (i : ℕ) (sigma : ℝ) :
    smoothDyadicBlockEnvelope i sigma =
      (2 : ℝ) ^ ((i + 1 : ℕ) * (1 - sigma)) /
        ((i + 1 : ℕ) * Real.log 2) := by
  unfold smoothDyadicBlockEnvelope
  push_cast
  rw [Real.log_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num [Nat.cast_add]

/-- Scalar exponential-harmonic sum left by the dyadic decomposition. -/
def smoothExponentialHarmonicSum (m : ℕ) (delta : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m,
    (2 : ℝ) ^ ((i + 1 : ℕ) * delta) / (i + 1 : ℕ)

/-- The exponential factor in the scalar dyadic sum is an ordinary natural
power of the one-step ratio. -/
theorem smoothExponentialFactor_eq_ratio_pow (i : ℕ) (delta : ℝ) :
    (2 : ℝ) ^ ((i + 1 : ℕ) * delta) =
      ((2 : ℝ) ^ delta) ^ (i + 1) := by
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- Natural-index version of the exponential ratio identity, including the
zero index. -/
theorem smoothExponentialFactor_eq_ratio_pow_nat (j : ℕ) (delta : ℝ) :
    (2 : ℝ) ^ ((j : ℕ) * delta) = ((2 : ℝ) ^ delta) ^ j := by
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- The midpoint exponential is bounded by the square root of the terminal
source-scale exponential. -/
theorem smoothDyadicMidpointExponential_le_sqrt_source
    {y : ℕ} (hy : 2 ≤ y) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (2 : ℝ) ^ (((smoothDyadicSteps y / 2 : ℕ) : ℝ) * delta) ≤
      Real.sqrt ((2 * (y : ℝ)) ^ delta) := by
  let q : ℝ := (2 : ℝ) ^ delta
  have hqOne : 1 ≤ q := Real.one_le_rpow (by norm_num) hdelta
  have hindex : (smoothDyadicSteps y / 2) * 2 ≤
      smoothDyadicSteps y + 1 := by omega
  have hsquare : (q ^ (smoothDyadicSteps y / 2)) ^ 2 ≤
      q ^ (smoothDyadicSteps y + 1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hqOne hindex
  have hsqrt : q ^ (smoothDyadicSteps y / 2) ≤
      Real.sqrt (q ^ (smoothDyadicSteps y + 1)) :=
    Real.le_sqrt_of_sq_le hsquare
  have hterminal := smoothDyadicTerminalExponential_le hy hdelta
  rw [smoothExponentialFactor_eq_ratio_pow_nat]
  exact hsqrt.trans (Real.sqrt_le_sqrt hterminal)

/-- Exact decomposition of the scalar dyadic sum at an arbitrary block
cutoff. -/
theorem smoothExponentialHarmonicSum_add (k r : ℕ) (delta : ℝ) :
    smoothExponentialHarmonicSum (k + r) delta =
      smoothExponentialHarmonicSum k delta +
        ∑ i ∈ Finset.range r,
          (2 : ℝ) ^ ((k + i + 1 : ℕ) * delta) /
            (k + i + 1 : ℕ) := by
  unfold smoothExponentialHarmonicSum
  rw [Finset.sum_range_add]

/-- The reciprocal-successor sum occurring in the early blocks is exactly a
harmonic number. -/
theorem sum_range_one_div_succ_eq_harmonic (k : ℕ) :
    ∑ i ∈ Finset.range k, (1 : ℝ) / (i + 1 : ℕ) =
      ((harmonic k : ℚ) : ℝ) := by
  induction k with
  | zero => simp [harmonic]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      rw [one_div]

/-- Up to a cutoff, monotonicity of the exponential leaves only a harmonic
factor. -/
theorem smoothExponentialHarmonicSum_le_rpow_mul_harmonic
    (k : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta) :
    smoothExponentialHarmonicSum k delta ≤
      (2 : ℝ) ^ ((k : ℕ) * delta) * ((harmonic k : ℚ) : ℝ) := by
  unfold smoothExponentialHarmonicSum
  calc
    (∑ i ∈ Finset.range k,
        (2 : ℝ) ^ ((i + 1 : ℕ) * delta) / (i + 1 : ℕ)) ≤
        ∑ i ∈ Finset.range k,
          (2 : ℝ) ^ ((k : ℕ) * delta) *
            ((1 : ℝ) / (i + 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : (i + 1 : ℕ) ≤ k := Finset.mem_range.mp hi
      have hexponent : ((i + 1 : ℕ) : ℝ) * delta ≤ (k : ℝ) * delta :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hik) hdelta
      have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        hexponent
      have hdenom : (0 : ℝ) ≤ (i + 1 : ℕ) := by positivity
      calc
        (2 : ℝ) ^ ((i + 1 : ℕ) * delta) / (i + 1 : ℕ) ≤
            (2 : ℝ) ^ ((k : ℕ) * delta) / (i + 1 : ℕ) :=
          div_le_div_of_nonneg_right hrpow hdenom
        _ = (2 : ℝ) ^ ((k : ℕ) * delta) *
            ((1 : ℝ) / (i + 1 : ℕ)) := by ring
    _ = (2 : ℝ) ^ ((k : ℕ) * delta) *
        ((harmonic k : ℚ) : ℝ) := by
      rw [← Finset.mul_sum, sum_range_one_div_succ_eq_harmonic]

/-- Past a cutoff, the reciprocal denominator is frozen at its smallest
value and the remaining exponential factors form a genuine geometric sum. -/
theorem smoothExponentialHarmonicTail_le_geometric
    (k r : ℕ) (delta : ℝ) :
    (∑ i ∈ Finset.range r,
        (2 : ℝ) ^ ((k + i + 1 : ℕ) * delta) /
          (k + i + 1 : ℕ)) ≤
      (((2 : ℝ) ^ delta) ^ (k + 1) / (k + 1 : ℕ)) *
        ∑ i ∈ Finset.range r, ((2 : ℝ) ^ delta) ^ i := by
  calc
    (∑ i ∈ Finset.range r,
        (2 : ℝ) ^ ((k + i + 1 : ℕ) * delta) /
          (k + i + 1 : ℕ)) ≤
        ∑ i ∈ Finset.range r,
          ((2 : ℝ) ^ delta) ^ (k + i + 1) / (k + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [smoothExponentialFactor_eq_ratio_pow]
      have hki : k + 1 ≤ k + i + 1 := by omega
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by exact_mod_cast hki)
    _ = (((2 : ℝ) ^ delta) ^ (k + 1) / (k + 1 : ℕ)) *
        ∑ i ∈ Finset.range r, ((2 : ℝ) ^ delta) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show k + i + 1 = (k + 1) + i by omega, pow_add]
      ring

/-- Arbitrary-cutoff estimate for the full scalar sum: a harmonic prefix and
a geometric tail. -/
theorem smoothExponentialHarmonicSum_le_cutoff_add_geometric
    (k r : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta) :
    smoothExponentialHarmonicSum (k + r) delta ≤
      (2 : ℝ) ^ ((k : ℕ) * delta) * ((harmonic k : ℚ) : ℝ) +
        (((2 : ℝ) ^ delta) ^ (k + 1) / (k + 1 : ℕ)) *
          ∑ i ∈ Finset.range r, ((2 : ℝ) ^ delta) ^ i := by
  rw [smoothExponentialHarmonicSum_add]
  exact add_le_add
    (smoothExponentialHarmonicSum_le_rpow_mul_harmonic k hdelta)
    (smoothExponentialHarmonicTail_le_geometric k r delta)

/-- Closed cutoff bound.  The geometric tail retains both its terminal
exponential and the crucial denominator `2 ^ delta - 1`. -/
theorem smoothExponentialHarmonicSum_le_cutoff
    (k r : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    smoothExponentialHarmonicSum (k + r) delta ≤
      (2 : ℝ) ^ ((k : ℕ) * delta) * ((harmonic k : ℚ) : ℝ) +
        (((2 : ℝ) ^ delta) ^ (k + r + 1)) /
          ((k + 1 : ℕ) * ((2 : ℝ) ^ delta - 1)) := by
  let q : ℝ := (2 : ℝ) ^ delta
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hdelta
  refine (smoothExponentialHarmonicSum_le_cutoff_add_geometric
    k r hdelta.le).trans ?_
  apply add_le_add (le_refl _)
  change (q ^ (k + 1) / (k + 1 : ℕ)) *
      ∑ i ∈ Finset.range r, q ^ i ≤
    q ^ (k + r + 1) / ((k + 1 : ℕ) * (q - 1))
  rw [geom_sum_eq hq.ne']
  calc
    (q ^ (k + 1) / (k + 1 : ℕ)) * ((q ^ r - 1) / (q - 1)) ≤
        (q ^ (k + 1) / (k + 1 : ℕ)) * (q ^ r / (q - 1)) := by
      apply mul_le_mul_of_nonneg_left
      · exact div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hq).le
      · positivity
    _ = q ^ (k + r + 1) / ((k + 1 : ℕ) * (q - 1)) := by
      rw [show k + r + 1 = (k + 1) + r by omega, pow_add]
      field_simp [show ((k + 1 : ℕ) : ℝ) ≠ 0 by positivity,
        sub_ne_zero.mpr hq.ne']
      rw [pow_add, pow_succ]

/-- The one-step dyadic ratio has at least its tangent-line growth. -/
theorem mul_log_two_le_rpow_sub_one (delta : ℝ) :
    delta * Real.log 2 ≤ (2 : ℝ) ^ delta - 1 := by
  have h := Real.add_one_le_exp (delta * Real.log 2)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexp : Real.exp (Real.log 2 * delta) =
      Real.exp (delta * Real.log 2) := by congr 1; ring
  rw [hexp]
  linarith

/-- Source-scale form of the cutoff bound.  Replacing the geometric
denominator by `delta * log 2` makes the eventual `1 / log u` gain explicit. -/
theorem smoothExponentialHarmonicSum_le_cutoff_log
    (k r : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    smoothExponentialHarmonicSum (k + r) delta ≤
      (2 : ℝ) ^ ((k : ℕ) * delta) * ((harmonic k : ℚ) : ℝ) +
        (((2 : ℝ) ^ delta) ^ (k + r + 1)) /
          ((k + 1 : ℕ) * (delta * Real.log 2)) := by
  refine (smoothExponentialHarmonicSum_le_cutoff k r hdelta).trans ?_
  apply add_le_add (le_refl _)
  apply div_le_div_of_nonneg_left (by positivity)
  · have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · exact mul_le_mul_of_nonneg_left
      (mul_log_two_le_rpow_sub_one delta) (by positivity)

/-- The canonical midpoint specialization of the cutoff estimate.  Its tail
has exactly the terminal exponential divided by `m * delta` up to absolute
constants, while the prefix sees only half of the terminal exponent. -/
theorem smoothExponentialHarmonicSum_le_midpoint
    (m : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    smoothExponentialHarmonicSum m delta ≤
      (2 : ℝ) ^ (((m / 2 : ℕ) : ℝ) * delta) *
          ((harmonic (m / 2) : ℚ) : ℝ) +
        (((2 : ℝ) ^ delta) ^ (m + 1)) /
          (((m / 2 + 1 : ℕ) : ℝ) * (delta * Real.log 2)) := by
  have hk : m / 2 ≤ m := Nat.div_le_self m 2
  have hsum : m / 2 + (m - m / 2) = m := Nat.add_sub_of_le hk
  have h := smoothExponentialHarmonicSum_le_cutoff_log
    (m / 2) (m - m / 2) hdelta
  rw [hsum] at h
  exact h

/-- Midpoint estimate with the prefix harmonic number replaced by its
standard logarithmic majorant. -/
theorem smoothExponentialHarmonicSum_le_midpoint_log
    (m : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    smoothExponentialHarmonicSum m delta ≤
      (2 : ℝ) ^ (((m / 2 : ℕ) : ℝ) * delta) *
          (1 + Real.log (m / 2 : ℕ)) +
        (((2 : ℝ) ^ delta) ^ (m + 1)) /
          (((m / 2 + 1 : ℕ) : ℝ) * (delta * Real.log 2)) := by
  refine (smoothExponentialHarmonicSum_le_midpoint m hdelta).trans ?_
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (m / 2))
      (by positivity)
  · exact le_refl _

/-- Dyadic midpoint estimate in source variables.  The terminal contribution
is now expressed using `y` and `log y`, rather than `clog 2 y`. -/
theorem smoothExponentialHarmonicSum_dyadic_le_sourceScale
    {y : ℕ} (hy : 2 ≤ y) {delta : ℝ} (hdelta : 0 < delta) :
    smoothExponentialHarmonicSum (smoothDyadicSteps y) delta ≤
      (2 : ℝ) ^
          (((smoothDyadicSteps y / 2 : ℕ) : ℝ) * delta) *
          (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) +
        2 * (2 * (y : ℝ)) ^ delta / (delta * Real.log y) := by
  refine (smoothExponentialHarmonicSum_le_midpoint_log
    (smoothDyadicSteps y) hdelta).trans ?_
  apply add_le_add (le_refl _)
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterminal := smoothDyadicTerminalExponential_le hy hdelta.le
  have hhalf := half_log_le_midpoint_mul_log_two hy
  have hden : delta * (Real.log y / 2) ≤
      ((smoothDyadicSteps y / 2 + 1 : ℕ) : ℝ) *
        (delta * Real.log 2) := by
    have := mul_le_mul_of_nonneg_left hhalf hdelta.le
    nlinarith
  calc
    (((2 : ℝ) ^ delta) ^ (smoothDyadicSteps y + 1)) /
          (((smoothDyadicSteps y / 2 + 1 : ℕ) : ℝ) *
            (delta * Real.log 2)) ≤
        (2 * (y : ℝ)) ^ delta /
          (((smoothDyadicSteps y / 2 + 1 : ℕ) : ℝ) *
            (delta * Real.log 2)) := by
      exact div_le_div_of_nonneg_right hterminal (by positivity)
    _ ≤ (2 * (y : ℝ)) ^ delta / (delta * (Real.log y / 2)) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 2 * (2 * (y : ℝ)) ^ delta / (delta * Real.log y) := by
      field_simp [hdelta.ne', hlogY.ne']

/-- Source-scale scalar estimate with the remaining prefix compressed to a
square-root exponential times a logarithmic factor. -/
theorem smoothExponentialHarmonicSum_dyadic_le_sourceScale_sqrt
    {y : ℕ} (hy : 2 ≤ y) {delta : ℝ} (hdelta : 0 < delta) :
    smoothExponentialHarmonicSum (smoothDyadicSteps y) delta ≤
      Real.sqrt ((2 * (y : ℝ)) ^ delta) *
          (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) +
        2 * (2 * (y : ℝ)) ^ delta / (delta * Real.log y) := by
  refine (smoothExponentialHarmonicSum_dyadic_le_sourceScale hy hdelta).trans ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
      (smoothDyadicMidpointExponential_le_sqrt_source hy hdelta.le)
    by_cases hk : smoothDyadicSteps y / 2 = 0
    · simp [hk]
    · have hkOne : 1 ≤ smoothDyadicSteps y / 2 :=
        Nat.one_le_iff_ne_zero.mpr hk
      have hlog : 0 ≤ Real.log (smoothDyadicSteps y / 2 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast hkOne)
      linarith
  · exact le_refl _

theorem sum_smoothDyadicBlockEnvelope_eq (m : ℕ) (sigma : ℝ) :
    (∑ i ∈ Finset.range m, smoothDyadicBlockEnvelope i sigma) =
      smoothExponentialHarmonicSum m (1 - sigma) / Real.log 2 := by
  unfold smoothExponentialHarmonicSum
  calc
    (∑ i ∈ Finset.range m, smoothDyadicBlockEnvelope i sigma) =
        ∑ i ∈ Finset.range m,
          ((2 : ℝ) ^ ((i + 1 : ℕ) * (1 - sigma)) / (i + 1 : ℕ)) /
            Real.log 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [smoothDyadicBlockEnvelope_eq]
      ring
    _ = (∑ i ∈ Finset.range m,
          (2 : ℝ) ^ ((i + 1 : ℕ) * (1 - sigma)) / (i + 1 : ℕ)) /
        Real.log 2 := by rw [Finset.sum_div]

theorem sum_rpow_neg_div_log_Ico_dyadicBlock_le
    {y i : ℕ} (hi : i < smoothDyadicSteps y) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) :
    ∑ n ∈ Finset.Ico (smoothDyadicCutoff y i)
        (smoothDyadicCutoff y (i + 1)),
          (n : ℝ) ^ (-sigma) / Real.log n ≤
      smoothDyadicBlockEnvelope i sigma := by
  have hci := smoothDyadicCutoff_eq_pow_of_lt_steps hi
  have ha : 2 ≤ smoothDyadicCutoff y i := by
    rw [hci]
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
        (Nat.succ_le_succ (Nat.zero_le i)))
  have hab : smoothDyadicCutoff y i ≤ smoothDyadicCutoff y (i + 1) :=
    monotone_smoothDyadicCutoff y (Nat.le_succ i)
  have hub : smoothDyadicCutoff y (i + 1) ≤ 2 * smoothDyadicCutoff y i := by
    rw [hci]
    calc
      smoothDyadicCutoff y (i + 1) ≤ 2 ^ ((i + 1) + 1) := by
        exact min_le_right _ _
      _ = 2 * 2 ^ (i + 1) := by rw [pow_succ']
  have hlength :
      ((smoothDyadicCutoff y (i + 1) - smoothDyadicCutoff y i : ℕ) : ℝ) ≤
        (smoothDyadicCutoff y i : ℝ) := by
    exact_mod_cast (by omega :
      smoothDyadicCutoff y (i + 1) - smoothDyadicCutoff y i ≤
        smoothDyadicCutoff y i)
  have hlocal := sum_rpow_neg_div_log_Ico_le_card_mul
    (a := smoothDyadicCutoff y i) (b := smoothDyadicCutoff y (i + 1))
    ha hsigma
  rw [hci] at hlocal hlength ⊢
  refine hlocal.trans ?_
  unfold smoothDyadicBlockEnvelope
  have haPow : 2 ≤ 2 ^ (i + 1) := by simpa [hci] using ha
  have hlogPos : 0 < Real.log (((2 ^ (i + 1) : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two haPow))
  apply div_le_div_of_nonneg_right _ hlogPos.le
  calc
    ((smoothDyadicCutoff y (i + 1) - 2 ^ (i + 1) : ℕ) : ℝ) *
        (((2 ^ (i + 1) : ℕ) : ℝ) ^ (-sigma)) ≤
        ((2 ^ (i + 1) : ℕ) : ℝ) *
          (((2 ^ (i + 1) : ℕ) : ℝ) ^ (-sigma)) :=
      mul_le_mul_of_nonneg_right hlength (Real.rpow_nonneg (by positivity) _)
    _ = (((2 ^ (i + 1) : ℕ) : ℝ) ^ (-sigma)) *
        ((2 ^ (i + 1) : ℕ) : ℝ) := by ring
    _ = (((2 ^ (i + 1) : ℕ) : ℝ) ^ (1 - sigma)) :=
      rpow_neg_mul_self (by positivity)

/-- Each active dyadic interval majorant is controlled by the next dyadic
endpoint, while retaining its own logarithmic denominator. -/
theorem smoothPowerLogIntervalMajorant_dyadic_le
    {y i : ℕ} (hi : i < smoothDyadicSteps y) {sigma : ℝ}
    (hsigmaOne : sigma < 1) :
    smoothPowerLogIntervalMajorant
        (smoothDyadicCutoff y i) (smoothDyadicCutoff y (i + 1)) sigma ≤
      smoothDyadicIntervalEnvelope i sigma := by
  have hci := smoothDyadicCutoff_eq_pow_of_lt_steps hi
  have hupperNat : smoothDyadicCutoff y (i + 1) - 1 ≤ 2 ^ (i + 2) := by
    calc
      smoothDyadicCutoff y (i + 1) - 1 ≤ smoothDyadicCutoff y (i + 1) :=
        Nat.sub_le _ _
      _ ≤ 2 ^ ((i + 1) + 1) := by
        exact min_le_right _ _
      _ = 2 ^ (i + 2) := by congr 1
  have hupper :
      (((smoothDyadicCutoff y (i + 1) - 1 : ℕ) : ℝ) ^ (1 - sigma)) ≤
        (((2 ^ (i + 2) : ℕ) : ℝ) ^ (1 - sigma)) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hupperNat)
      (sub_nonneg.mpr hsigmaOne.le)
  have hlower :
      0 ≤ (((smoothDyadicCutoff y i - 1 : ℕ) : ℝ) ^ (1 - sigma)) :=
    Real.rpow_nonneg (by positivity) _
  have hnum :
      (((smoothDyadicCutoff y (i + 1) - 1 : ℕ) : ℝ) ^ (1 - sigma) -
          ((smoothDyadicCutoff y i - 1 : ℕ) : ℝ) ^ (1 - sigma)) ≤
        (((2 ^ (i + 2) : ℕ) : ℝ) ^ (1 - sigma)) := by
    linarith
  have hpowTwo : 2 ≤ 2 ^ (i + 1) := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
        (Nat.succ_le_succ (Nat.zero_le i)))
  have hlogPos : 0 < Real.log (((2 ^ (i + 1) : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hpowTwo))
  have hdenPos :
      0 < (1 - sigma) * Real.log (((2 ^ (i + 1) : ℕ) : ℝ)) :=
    mul_pos (sub_pos.mpr hsigmaOne) hlogPos
  unfold smoothPowerLogIntervalMajorant smoothDyadicIntervalEnvelope
  rw [hci]
  rw [div_div]
  exact div_le_div_of_nonneg_right (by simpa [hci] using hnum) hdenPos.le

/-- The concrete dyadic chain majorant is bounded by an entirely explicit
finite envelope sum. -/
theorem smoothPowerLogChainMajorant_dyadic_le
    {y : ℕ} {sigma : ℝ} (hsigmaOne : sigma < 1) :
    smoothPowerLogChainMajorant (smoothDyadicCutoff y)
        (smoothDyadicSteps y) sigma ≤
      ∑ i ∈ Finset.range (smoothDyadicSteps y),
        smoothDyadicIntervalEnvelope i sigma := by
  unfold smoothPowerLogChainMajorant
  apply Finset.sum_le_sum
  intro i hi
  exact smoothPowerLogIntervalMajorant_dyadic_le
    (Finset.mem_range.mp hi) hsigmaOne

/-- Concrete dyadic-chain bound for the critical power-log sum. -/
theorem sum_rpow_neg_div_log_Ico_le_dyadicChain
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      smoothPowerLogChainMajorant (smoothDyadicCutoff y)
        (smoothDyadicSteps y) sigma := by
  have hstart : 2 ≤ smoothDyadicCutoff y 0 := by
    rw [smoothDyadicCutoff_zero hy]
  have h := sum_rpow_neg_div_log_Ico_le_monotone_chain
    (smoothDyadicCutoff y) (monotone_smoothDyadicCutoff y)
    hstart (smoothDyadicSteps y) hsigma hsigmaOne
  rw [smoothDyadicCutoff_zero hy, smoothDyadicCutoff_steps hy] at h
  exact h

/-- Explicit dyadic-envelope bound with no abstract cutoff chain remaining. -/
theorem sum_rpow_neg_div_log_Ico_le_dyadicEnvelope
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ∑ i ∈ Finset.range (smoothDyadicSteps y),
        smoothDyadicIntervalEnvelope i sigma :=
  (sum_rpow_neg_div_log_Ico_le_dyadicChain hy hsigma hsigmaOne).trans
    (smoothPowerLogChainMajorant_dyadic_le hsigmaOne)

/-- Sharper critical-regime dyadic estimate.  Cardinality on each dyadic
block cancels the artificial `(1-sigma)⁻¹` loss. -/
theorem sum_rpow_neg_div_log_Ico_le_dyadicBlocks
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ∑ i ∈ Finset.range (smoothDyadicSteps y),
        smoothDyadicBlockEnvelope i sigma := by
  have hchain := sum_sum_Ico_monotone_chain
    (smoothDyadicCutoff y) (monotone_smoothDyadicCutoff y)
    (fun n => (n : ℝ) ^ (-sigma) / Real.log n) (smoothDyadicSteps y)
  rw [smoothDyadicCutoff_zero hy, smoothDyadicCutoff_steps hy] at hchain
  calc
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n =
        ∑ i ∈ Finset.range (smoothDyadicSteps y),
          ∑ n ∈ Finset.Ico (smoothDyadicCutoff y i)
            (smoothDyadicCutoff y (i + 1)),
              (n : ℝ) ^ (-sigma) / Real.log n := hchain.symm
    _ ≤ ∑ i ∈ Finset.range (smoothDyadicSteps y),
        smoothDyadicBlockEnvelope i sigma := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_rpow_neg_div_log_Ico_dyadicBlock_le
        (Finset.mem_range.mp hi) hsigma

/-- Critical-regime reduction to a single explicit exponential-harmonic
scalar sum. -/
theorem sum_rpow_neg_div_log_Ico_le_exponentialHarmonic
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      smoothExponentialHarmonicSum (smoothDyadicSteps y) (1 - sigma) /
        Real.log 2 := by
  rw [← sum_smoothDyadicBlockEnvelope_eq]
  exact sum_rpow_neg_div_log_Ico_le_dyadicBlocks hy hsigma

/-- Closed midpoint estimate for the original power-log sum on the concrete
saturated dyadic chain. -/
theorem sum_rpow_neg_div_log_Ico_le_dyadicMidpoint
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ((2 : ℝ) ^
            (((smoothDyadicSteps y / 2 : ℕ) : ℝ) * (1 - sigma)) *
            (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) +
          (((2 : ℝ) ^ (1 - sigma)) ^ (smoothDyadicSteps y + 1)) /
            (((smoothDyadicSteps y / 2 + 1 : ℕ) : ℝ) *
              ((1 - sigma) * Real.log 2))) /
        Real.log 2 := by
  refine (sum_rpow_neg_div_log_Ico_le_exponentialHarmonic hy hsigma).trans ?_
  exact div_le_div_of_nonneg_right
    (smoothExponentialHarmonicSum_le_midpoint_log
      (smoothDyadicSteps y) (sub_pos.mpr hsigmaOne))
    (Real.log_pos (by norm_num)).le

/-- Saddle-ready normalization of the two-scale split.  The two hypotheses
are precisely the elementary properties supplied by choosing `k` near a fixed
positive power of `y`. -/
theorem sum_rpow_neg_div_log_Ico_le_saddleScale
    {k y : ℕ} (hk : 2 ≤ k) (hky : k ≤ y) {sigma L : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1)
    (hsmall : (k : ℝ) ^ (1 - sigma) * Real.log y ≤
      (y : ℝ) ^ (1 - sigma))
    (hlog : Real.log y ≤ L * Real.log k) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
        (1 / Real.log 2 + L) := by
  have hdelta : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogK : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hk))
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two (le_trans hk hky)))
  have hsmall' :
      (k : ℝ) ^ (1 - sigma) ≤ (y : ℝ) ^ (1 - sigma) / Real.log y :=
    (le_div_iff₀ hlogY).2 hsmall
  have hA :
      (k : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2) ≤
        ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
          (1 / Real.log 2) := by
    calc
      (k : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2) =
          ((k : ℝ) ^ (1 - sigma) / (1 - sigma)) * (1 / Real.log 2) := by
        field_simp
      _ ≤ (((y : ℝ) ^ (1 - sigma) / Real.log y) / (1 - sigma)) *
          (1 / Real.log 2) := by
        gcongr
      _ = ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
          (1 / Real.log 2) := by ring
  have hinvLog : 1 / Real.log (k : ℝ) ≤ L / Real.log (y : ℝ) := by
    exact (div_le_div_iff₀ hlogK hlogY).2 (by simpa [mul_comm] using hlog)
  have hB :
      (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log k) ≤
        ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) * L := by
    calc
      (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log k) =
          ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) * (1 / Real.log k) := by
        field_simp
      _ ≤ ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) *
          (L / Real.log y) := by
        exact mul_le_mul_of_nonneg_left hinvLog
          (div_nonneg (Real.rpow_nonneg (by positivity) _) hdelta.le)
      _ = ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) * L := by ring
  refine (sum_rpow_neg_div_log_Ico_le_split hk hky hsigma hsigmaOne).trans ?_
  calc
    (k : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2) +
        (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log k) ≤
        ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
            (1 / Real.log 2) +
          ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) * L :=
      add_le_add hA hB
    _ = ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
        (1 / Real.log 2 + L) := by ring

/-- The standard dimensionless smoothness ratio `u = log X / log y`. -/
def smoothRankinRatio (X y : ℕ) : ℝ :=
  Real.log X / Real.log y

/-- The elementary Rankin saddle choice
`sigma = 1 - log u / log y`. -/
def smoothRankinSigma (X y : ℕ) : ℝ :=
  1 - Real.log (smoothRankinRatio X y) / Real.log y

theorem one_sub_smoothRankinSigma (X y : ℕ) :
    1 - smoothRankinSigma X y =
      Real.log (smoothRankinRatio X y) / Real.log y := by
  simp [smoothRankinSigma]

/-- At the standard saddle, the small exponent times `log y` is exactly
`log u`. -/
theorem one_sub_smoothRankinSigma_mul_log
    {X y : ℕ} (hy : 2 ≤ y) :
    (1 - smoothRankinSigma X y) * Real.log y =
      Real.log (smoothRankinRatio X y) := by
  have hlogYNe : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).ne'
  rw [one_sub_smoothRankinSigma]
  field_simp

theorem smoothRankinRatio_pos
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    0 < smoothRankinRatio X y := by
  exact div_pos
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hX)))
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy)))

/-- If `u<y`, the saddle parameter is positive. -/
theorem smoothRankinSigma_pos
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huY : smoothRankinRatio X y < y) :
    0 < smoothRankinSigma X y := by
  have huPos := smoothRankinRatio_pos hX hy
  have hyPos : (0 : ℝ) < y := by positivity
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))
  have hlogs : Real.log (smoothRankinRatio X y) < Real.log (y : ℝ) :=
    Real.strictMonoOn_log huPos hyPos (by simpa using huY)
  rw [smoothRankinSigma, sub_pos, div_lt_one hlogY]
  exact hlogs

/-- If `u>1`, the saddle parameter lies below one. -/
theorem smoothRankinSigma_lt_one
    {X y : ℕ} (hy : 2 ≤ y) (huOne : 1 < smoothRankinRatio X y) :
    smoothRankinSigma X y < 1 := by
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))
  have hlogU : 0 < Real.log (smoothRankinRatio X y) := Real.log_pos huOne
  unfold smoothRankinSigma
  have : 0 < Real.log (smoothRankinRatio X y) / Real.log y :=
    div_pos hlogU hlogY
  linarith

/-- At the standard saddle, the endpoint power is exactly `u`. -/
theorem rpow_one_sub_smoothRankinSigma
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (y : ℝ) ^ (1 - smoothRankinSigma X y) = smoothRankinRatio X y := by
  have hyPos : (0 : ℝ) < y := by positivity
  have hlogYNe : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))).ne'
  rw [Real.rpow_def_of_pos hyPos, one_sub_smoothRankinSigma]
  have hexp :
      Real.log (smoothRankinRatio X y) / Real.log y * Real.log y =
        Real.log (smoothRankinRatio X y) := by
    field_simp
  have hexp' :
      Real.log y * (Real.log (smoothRankinRatio X y) / Real.log y) =
        Real.log (smoothRankinRatio X y) := by
    simpa [mul_comm] using hexp
  rw [hexp', Real.exp_log (smoothRankinRatio_pos hX hy)]

/-- The dyadic scalar sum at the actual Rankin saddle, with its terminal term
written as `u / log u` up to the harmless factor `2^(1-sigma)`. -/
theorem smoothExponentialHarmonicSum_dyadic_le_rankinScale
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huOne : 1 < smoothRankinRatio X y) :
    smoothExponentialHarmonicSum (smoothDyadicSteps y)
        (1 - smoothRankinSigma X y) ≤
      (2 : ℝ) ^
          (((smoothDyadicSteps y / 2 : ℕ) : ℝ) *
            (1 - smoothRankinSigma X y)) *
          (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) +
        2 * (2 : ℝ) ^ (1 - smoothRankinSigma X y) *
          smoothRankinRatio X y / Real.log (smoothRankinRatio X y) := by
  have hsigmaOne := smoothRankinSigma_lt_one hy huOne
  have h := smoothExponentialHarmonicSum_dyadic_le_sourceScale hy
    (sub_pos.mpr hsigmaOne)
  rw [Real.mul_rpow (by norm_num) (by positivity),
    rpow_one_sub_smoothRankinSigma hX hy,
    one_sub_smoothRankinSigma_mul_log hy] at h
  convert h using 1
  all_goals ring

/-- Rankin-saddle scalar estimate with the prefix in its final square-root
form.  The remaining asymptotic comparison is now between
`sqrt u * log log y` and `u / log u`. -/
theorem smoothExponentialHarmonicSum_dyadic_le_rankinScale_sqrt
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huOne : 1 < smoothRankinRatio X y) :
    smoothExponentialHarmonicSum (smoothDyadicSteps y)
        (1 - smoothRankinSigma X y) ≤
      Real.sqrt ((2 : ℝ) ^ (1 - smoothRankinSigma X y) *
          smoothRankinRatio X y) *
          (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) +
        2 * (2 : ℝ) ^ (1 - smoothRankinSigma X y) *
          smoothRankinRatio X y / Real.log (smoothRankinRatio X y) := by
  have hsigmaOne := smoothRankinSigma_lt_one hy huOne
  have h := smoothExponentialHarmonicSum_dyadic_le_sourceScale_sqrt hy
    (sub_pos.mpr hsigmaOne)
  rw [Real.mul_rpow (by norm_num) (by positivity),
    rpow_one_sub_smoothRankinSigma hX hy,
    one_sub_smoothRankinSigma_mul_log hy] at h
  convert h using 1
  all_goals ring

/-- A concrete fourth-root criterion for absorbing two logarithmic factors
into a square root.  This is the finite inequality used to specialize the
Rankin prefix estimate to Tao's asymptotic regimes. -/
theorem two_mul_mul_log_le_sqrt_of_eight_mul_le_rpow_quarter
    {u L : ℝ} (hu : 0 < u) (hL : 0 ≤ L)
    (hscale : 8 * L ≤ u ^ (1 / 4 : ℝ)) :
    2 * L * Real.log u ≤ Real.sqrt u := by
  have hlog : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hu.le (by norm_num : (0 : ℝ) < 1 / 4)
    convert h using 1
    ring
  calc
    2 * L * Real.log u ≤ 2 * L * (4 * u ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) hL)
    _ = (8 * L) * u ^ (1 / 4 : ℝ) := by ring
    _ ≤ u ^ (1 / 4 : ℝ) * u ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hu.le _)
    _ = Real.sqrt u := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hu]
      norm_num

/-- The fourth root eventually dominates the explicit affine logarithmic
factor needed by the dyadic-prefix estimate. -/
theorem eventually_eight_mul_one_add_two_mul_log_le_rpow_quarter :
    ∀ᶠ u : ℝ in Filter.atTop,
      8 * (1 + 2 * Real.log u) ≤ u ^ (1 / 4 : ℝ) := by
  have hsmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 4)).def
      (by norm_num : (0 : ℝ) < 1 / 32)
  have hrootTop : Filter.Tendsto (fun u : ℝ => u ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hrootLarge := hrootTop.eventually (Filter.eventually_ge_atTop (16 : ℝ))
  filter_upwards [hsmall, hrootLarge,
    Filter.eventually_ge_atTop (1 : ℝ)] with u hu hroot huOne
  have hrootNonneg : 0 ≤ u ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (by linarith) _
  have hlogNonneg : 0 ≤ Real.log u := Real.log_nonneg huOne
  have hu' : Real.log u ≤ (1 / 32 : ℝ) * u ^ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogNonneg,
      abs_of_nonneg hrootNonneg] using hu
  nlinarith

/-- Source-facing fourth-root criterion for the remaining dyadic Rankin
prefix. -/
theorem smoothRankinPrefixCondition_of_eight_mul_le_rpow_quarter
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hgrowth :
      8 * (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) ≤
        smoothRankinRatio X y ^ (1 / 4 : ℝ)) :
    2 * (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) *
        Real.log (smoothRankinRatio X y) ≤
      Real.sqrt (smoothRankinRatio X y) := by
  have huPos := smoothRankinRatio_pos hX hy
  have hL : 0 ≤ 1 + Real.log (smoothDyadicSteps y / 2 : ℕ) := by
    by_cases hk : smoothDyadicSteps y / 2 = 0
    · simp [hk]
    · have hkOne : 1 ≤ smoothDyadicSteps y / 2 :=
        Nat.one_le_iff_ne_zero.mpr hk
      have hkOneR : (1 : ℝ) ≤
          (smoothDyadicSteps y / 2 : ℕ) := by exact_mod_cast hkOne
      have := Real.log_nonneg hkOneR
      linarith
  exact two_mul_mul_log_le_sqrt_of_eight_mul_le_rpow_quarter
    huPos hL hgrowth

/-- Continuous-log version of the fourth-root prefix criterion.  This removes
the natural dyadic depth from the hypothesis used in asymptotic regimes. -/
theorem smoothRankinPrefixCondition_of_logScale_le_rpow_quarter
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hgrowth :
      8 * (1 + Real.log (Real.log (2 * (y : ℝ)) / Real.log 2)) ≤
        smoothRankinRatio X y ^ (1 / 4 : ℝ)) :
    2 * (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) *
        Real.log (smoothRankinRatio X y) ≤
      Real.sqrt (smoothRankinRatio X y) := by
  apply smoothRankinPrefixCondition_of_eight_mul_le_rpow_quarter hX hy
  exact (mul_le_mul_of_nonneg_left
    (smoothDyadicPrefixLog_le_log_logScale hy) (by norm_num)).trans hgrowth

/-- If the continuous dyadic depth is at most `u²`, the universal eventual
fourth-root inequality supplies the remaining Rankin prefix condition. -/
theorem smoothRankinPrefixCondition_of_logScale_le_sq
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huOne : 1 < smoothRankinRatio X y)
    (hscale : Real.log (2 * (y : ℝ)) / Real.log 2 ≤
      smoothRankinRatio X y ^ (2 : ℕ))
    (hnumeric :
      8 * (1 + 2 * Real.log (smoothRankinRatio X y)) ≤
        smoothRankinRatio X y ^ (1 / 4 : ℝ)) :
    2 * (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) *
        Real.log (smoothRankinRatio X y) ≤
      Real.sqrt (smoothRankinRatio X y) := by
  let u : ℝ := smoothRankinRatio X y
  let t : ℝ := Real.log (2 * (y : ℝ)) / Real.log 2
  have huPos : 0 < u := by dsimp only [u]; linarith
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwoYPos : (0 : ℝ) < 2 * (y : ℝ) := by positivity
  have htwoLt : (2 : ℝ) < 2 * (y : ℝ) := by
    have : (1 : ℝ) < y := by exact_mod_cast hy
    nlinarith
  have hlogLt : Real.log (2 : ℝ) < Real.log (2 * (y : ℝ)) :=
    Real.strictMonoOn_log (by norm_num) htwoYPos htwoLt
  have htOne : (1 : ℝ) < t := by
    dsimp only [t]
    rw [lt_div_iff₀ hlogTwo]
    simpa using hlogLt
  have hlogScale : Real.log t ≤ 2 * Real.log u := by
    have hlog := Real.log_le_log (by linarith : 0 < t) (by simpa [u, t] using hscale)
    rw [Real.log_pow] at hlog
    simpa [u] using hlog
  apply smoothRankinPrefixCondition_of_logScale_le_rpow_quarter hX hy
  calc
    8 * (1 + Real.log t) ≤ 8 * (1 + 2 * Real.log u) := by nlinarith
    _ ≤ u ^ (1 / 4 : ℝ) := by simpa [u] using hnumeric

/-- Explicit absorption interface for the remaining midpoint prefix.  Once
`sqrt u` dominates the two logarithmic factors, the entire scalar sum has the
desired `u / log u` scale with absolute constant five. -/
theorem smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huOne : 1 < smoothRankinRatio X y)
    (hsigma : 0 ≤ smoothRankinSigma X y)
    (hprefix :
      2 * (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) *
          Real.log (smoothRankinRatio X y) ≤
        Real.sqrt (smoothRankinRatio X y)) :
    smoothExponentialHarmonicSum (smoothDyadicSteps y)
        (1 - smoothRankinSigma X y) ≤
      5 * smoothRankinRatio X y /
        Real.log (smoothRankinRatio X y) := by
  let u : ℝ := smoothRankinRatio X y
  let delta : ℝ := 1 - smoothRankinSigma X y
  let L : ℝ := 1 + Real.log (smoothDyadicSteps y / 2 : ℕ)
  have huPos : 0 < u := by dsimp only [u]; linarith
  have hlogU : 0 < Real.log u := Real.log_pos (by simpa [u] using huOne)
  have hsigmaOne := smoothRankinSigma_lt_one hy huOne
  have hdeltaNonneg : 0 ≤ delta := by dsimp only [delta]; linarith
  have hdeltaOne : delta ≤ 1 := by dsimp only [delta]; linarith
  have hL : 0 ≤ L := by
    dsimp only [L]
    by_cases hk : smoothDyadicSteps y / 2 = 0
    · simp [hk]
    · have hkOne : 1 ≤ smoothDyadicSteps y / 2 :=
        Nat.one_le_iff_ne_zero.mpr hk
      have hkOneR : (1 : ℝ) ≤
          (smoothDyadicSteps y / 2 : ℕ) := by exact_mod_cast hkOne
      have := Real.log_nonneg hkOneR
      linarith
  have haLeTwo : (2 : ℝ) ^ delta ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hdeltaOne
  have hsqrtFactor : Real.sqrt ((2 : ℝ) ^ delta * u) ≤
      2 * Real.sqrt u := by
    have hsqrtFour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    have hproduct : (2 : ℝ) ^ delta * u ≤ 4 * u := by
      have := mul_le_mul_of_nonneg_right haLeTwo huPos.le
      nlinarith
    calc
      Real.sqrt ((2 : ℝ) ^ delta * u) ≤ Real.sqrt (4 * u) :=
        Real.sqrt_le_sqrt hproduct
      _ = Real.sqrt 4 * Real.sqrt u :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) u
      _ = 2 * Real.sqrt u := by rw [hsqrtFour]
  have hprefix' : 2 * L * Real.log u ≤ Real.sqrt u := by
    simpa [u, L] using hprefix
  have hprefixBound : Real.sqrt ((2 : ℝ) ^ delta * u) * L ≤
      u / Real.log u := by
    rw [le_div_iff₀ hlogU]
    calc
      Real.sqrt ((2 : ℝ) ^ delta * u) * L * Real.log u =
          Real.sqrt ((2 : ℝ) ^ delta * u) * (L * Real.log u) := by ring
      _ ≤ (2 * Real.sqrt u) * (L * Real.log u) :=
        mul_le_mul_of_nonneg_right hsqrtFactor (mul_nonneg hL hlogU.le)
      _ = Real.sqrt u * (2 * L * Real.log u) := by ring
      _ ≤ Real.sqrt u * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hprefix' (Real.sqrt_nonneg u)
      _ = u := Real.mul_self_sqrt huPos.le
  have hterminalBound :
      2 * (2 : ℝ) ^ delta * u / Real.log u ≤
        4 * u / Real.log u := by
    apply div_le_div_of_nonneg_right _ hlogU.le
    have := mul_le_mul_of_nonneg_right haLeTwo huPos.le
    nlinarith
  have hmain := smoothExponentialHarmonicSum_dyadic_le_rankinScale_sqrt
    hX hy huOne
  change smoothExponentialHarmonicSum (smoothDyadicSteps y) delta ≤
      5 * u / Real.log u
  change smoothExponentialHarmonicSum (smoothDyadicSteps y) delta ≤
      _ at hmain
  exact hmain.trans (by
    calc
      Real.sqrt ((2 : ℝ) ^ delta * u) * L +
          2 * (2 : ℝ) ^ delta * u / Real.log u ≤
          u / Real.log u + 4 * u / Real.log u :=
        add_le_add hprefixBound hterminalBound
      _ = 5 * u / Real.log u := by ring)

/-- Complete scalar `u / log u` estimate under the more convenient
fourth-root growth condition used by the source-regime specializations. -/
theorem smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log_of_rpow_quarter
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huOne : 1 < smoothRankinRatio X y)
    (hsigma : 0 ≤ smoothRankinSigma X y)
    (hgrowth :
      8 * (1 + Real.log (smoothDyadicSteps y / 2 : ℕ)) ≤
        smoothRankinRatio X y ^ (1 / 4 : ℝ)) :
    smoothExponentialHarmonicSum (smoothDyadicSteps y)
        (1 - smoothRankinSigma X y) ≤
      5 * smoothRankinRatio X y /
        Real.log (smoothRankinRatio X y) := by
  exact smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log
    hX hy huOne hsigma
      (smoothRankinPrefixCondition_of_eight_mul_le_rpow_quarter hX hy hgrowth)

/-- Complete scalar estimate under a fourth-root comparison involving only
continuous logarithms of the source parameters. -/
theorem smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log_of_logScale
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huOne : 1 < smoothRankinRatio X y)
    (hsigma : 0 ≤ smoothRankinSigma X y)
    (hgrowth :
      8 * (1 + Real.log (Real.log (2 * (y : ℝ)) / Real.log 2)) ≤
        smoothRankinRatio X y ^ (1 / 4 : ℝ)) :
    smoothExponentialHarmonicSum (smoothDyadicSteps y)
        (1 - smoothRankinSigma X y) ≤
      5 * smoothRankinRatio X y /
        Real.log (smoothRankinRatio X y) := by
  exact smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log
    hX hy huOne hsigma
      (smoothRankinPrefixCondition_of_logScale_le_rpow_quarter hX hy hgrowth)

/-- Finite regime interface: a quadratic upper bound for the continuous
dyadic depth and the universal scalar fourth-root inequality imply the full
`5u / log u` estimate. -/
theorem smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log_of_logScale_le_sq
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huOne : 1 < smoothRankinRatio X y)
    (hsigma : 0 ≤ smoothRankinSigma X y)
    (hscale : Real.log (2 * (y : ℝ)) / Real.log 2 ≤
      smoothRankinRatio X y ^ (2 : ℕ))
    (hnumeric :
      8 * (1 + 2 * Real.log (smoothRankinRatio X y)) ≤
        smoothRankinRatio X y ^ (1 / 4 : ℝ)) :
    smoothExponentialHarmonicSum (smoothDyadicSteps y)
        (1 - smoothRankinSigma X y) ≤
      5 * smoothRankinRatio X y /
        Real.log (smoothRankinRatio X y) := by
  exact smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log
    hX hy huOne hsigma
      (smoothRankinPrefixCondition_of_logScale_le_sq
        hX hy huOne hscale hnumeric)

/-- Asymptotic regime consumer for the scalar Rankin estimate.  Any natural
parameter sequences for which `u → ∞` and the continuous dyadic depth is
eventually at most `u²` satisfy the complete estimate, once the elementary
saddle range hypotheses hold eventually. -/
theorem eventually_smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log
    (X y : ℕ → ℕ)
    (hX : ∀ᶠ n in Filter.atTop, 2 ≤ X n)
    (hy : ∀ᶠ n in Filter.atTop, 2 ≤ y n)
    (huOne : ∀ᶠ n in Filter.atTop, 1 < smoothRankinRatio (X n) (y n))
    (hsigma : ∀ᶠ n in Filter.atTop, 0 ≤ smoothRankinSigma (X n) (y n))
    (huTop : Filter.Tendsto
      (fun n => smoothRankinRatio (X n) (y n)) Filter.atTop Filter.atTop)
    (hscale : ∀ᶠ n in Filter.atTop,
      Real.log (2 * (y n : ℝ)) / Real.log 2 ≤
        smoothRankinRatio (X n) (y n) ^ (2 : ℕ)) :
    ∀ᶠ n in Filter.atTop,
      smoothExponentialHarmonicSum (smoothDyadicSteps (y n))
          (1 - smoothRankinSigma (X n) (y n)) ≤
        5 * smoothRankinRatio (X n) (y n) /
          Real.log (smoothRankinRatio (X n) (y n)) := by
  have hnumeric := huTop.eventually
    eventually_eight_mul_one_add_two_mul_log_le_rpow_quarter
  filter_upwards [hX, hy, huOne, hsigma, hscale, hnumeric] with
    n hnX hny hnu hnsigma hnscale hnnumeric
  exact smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log_of_logScale_le_sq
    hnX hny hnu hnsigma hnscale hnnumeric

/-- The negative term in the Rankin exponent becomes exactly `-u log u`. -/
theorem smoothRankin_saving_identity
    {X y : ℕ} (hy : 2 ≤ y) :
    -(1 - smoothRankinSigma X y) * Real.log X =
      -smoothRankinRatio X y * Real.log (smoothRankinRatio X y) := by
  have hlogYNe : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))).ne'
  rw [one_sub_smoothRankinSigma]
  unfold smoothRankinRatio
  field_simp

/-- Integer cutoff obtained by flooring the real quotient `y / R`. -/
def smoothSaddleFloorCutoff (y : ℕ) (R : ℝ) : ℕ :=
  ⌊(y : ℝ) / R⌋₊

/-- The canonical real divisor for the power-log saddle split. -/
def smoothSaddleDivisor (y : ℕ) (sigma : ℝ) : ℝ :=
  Real.log y ^ (1 / (1 - sigma))

theorem smoothSaddleDivisor_pos
    {y : ℕ} (hy : 2 ≤ y) (sigma : ℝ) : 0 < smoothSaddleDivisor y sigma := by
  unfold smoothSaddleDivisor
  exact Real.rpow_pos_of_pos
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))) _

theorem one_le_smoothSaddleDivisor
    {y : ℕ} {sigma : ℝ} (hlogOne : 1 ≤ Real.log (y : ℝ)) (hsigma : sigma < 1) :
    1 ≤ smoothSaddleDivisor y sigma := by
  unfold smoothSaddleDivisor
  exact Real.one_le_rpow hlogOne (by positivity)

/-- The canonical divisor was chosen so that its `(1-sigma)` power is exactly
`log y`. -/
theorem smoothSaddleDivisor_rpow_one_sub
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hsigma : sigma < 1) :
    smoothSaddleDivisor y sigma ^ (1 - sigma) = Real.log y := by
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))
  have hdeltaNe : 1 - sigma ≠ 0 := (sub_pos.mpr hsigma).ne'
  unfold smoothSaddleDivisor
  rw [← Real.rpow_mul hlogPos.le]
  have hexp : (1 / (1 - sigma)) * (1 - sigma) = 1 := by
    field_simp
  rw [hexp, Real.rpow_one]

/-- At the standard Rankin saddle, the canonical divisor has the explicit
exponent `log y / log u`. -/
theorem smoothSaddleDivisor_at_rankinSigma
    {X y : ℕ} (hy : 2 ≤ y) (huOne : 1 < smoothRankinRatio X y) :
    smoothSaddleDivisor y (smoothRankinSigma X y) =
      Real.log y ^
        (Real.log y / Real.log (smoothRankinRatio X y)) := by
  have hlogYNe : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))).ne'
  have hlogUNe : Real.log (smoothRankinRatio X y) ≠ 0 :=
    (Real.log_pos huOne).ne'
  unfold smoothSaddleDivisor
  rw [one_sub_smoothRankinSigma]
  congr 1
  field_simp

/-- Consequently the small-range comparison required by the normalized split
holds with equality before flooring. -/
theorem smoothSaddleQuotient_rpow_mul_log
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hsigma : sigma < 1) :
    ((y : ℝ) / smoothSaddleDivisor y sigma) ^ (1 - sigma) * Real.log y =
      (y : ℝ) ^ (1 - sigma) := by
  have hR := smoothSaddleDivisor_pos hy sigma
  have hlogNe : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))).ne'
  rw [Real.div_rpow (Nat.cast_nonneg y) hR.le,
    smoothSaddleDivisor_rpow_one_sub hy hsigma]
  field_simp

/-- If the real saddle divisor is at most half of `sqrt y`, the logarithm of
the quotient after the factor-two floor loss is at least half of `log y`. -/
theorem log_self_le_two_mul_log_div_two_mul
    {y : ℕ} (hy : 1 ≤ y) {R : ℝ} (hR : 0 < R)
    (hhalf : 2 * R ≤ Real.sqrt y) :
    Real.log y ≤ 2 * Real.log ((y : ℝ) / (2 * R)) := by
  have hyPos : (0 : ℝ) < y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy)
  have hdenPos : 0 < 2 * R := mul_pos (by norm_num) hR
  have hsqrtLe : Real.sqrt (y : ℝ) ≤ (y : ℝ) / (2 * R) := by
    rw [le_div_iff₀ hdenPos]
    calc
      Real.sqrt (y : ℝ) * (2 * R) = (2 * R) * Real.sqrt y := by ring
      _ ≤ Real.sqrt y * Real.sqrt y :=
        mul_le_mul_of_nonneg_right hhalf (Real.sqrt_nonneg _)
      _ = (y : ℝ) := Real.mul_self_sqrt hyPos.le
  have hquotPos : 0 < (y : ℝ) / (2 * R) := div_pos hyPos hdenPos
  have hlogs : Real.log (Real.sqrt (y : ℝ)) ≤
      Real.log ((y : ℝ) / (2 * R)) :=
    Real.strictMonoOn_log.monotoneOn (Real.sqrt_pos.2 hyPos) hquotPos hsqrtLe
  rw [Real.log_sqrt hyPos.le] at hlogs
  linarith

/-- A half-square-root bound on the divisor forces the real saddle quotient
to be at least four. -/
theorem four_le_div_of_two_mul_le_sqrt
    {y : ℕ} (hy : 4 ≤ y) {R : ℝ} (hR : 0 < R)
    (hhalf : 2 * R ≤ Real.sqrt y) :
    4 ≤ (y : ℝ) / R := by
  have hyNonneg : (0 : ℝ) ≤ y := by positivity
  have htwoSqrt : (2 : ℝ) ≤ Real.sqrt y := by
    exact Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hy)
  have hprod : (2 * R) * 2 ≤ Real.sqrt y * Real.sqrt y :=
    mul_le_mul hhalf htwoSqrt (by norm_num) (Real.sqrt_nonneg _)
  have hsqrtSq : Real.sqrt (y : ℝ) * Real.sqrt y = y :=
    Real.mul_self_sqrt hyNonneg
  rw [hsqrtSq] at hprod
  exact (le_div_iff₀ hR).2 (by nlinarith)

/-- The actual integer cutoff used by the canonical saddle split. -/
def smoothCanonicalSaddleCutoff (y : ℕ) (sigma : ℝ) : ℕ :=
  smoothSaddleFloorCutoff y (smoothSaddleDivisor y sigma)

/-- Quantitative floor transfer for the saddle cutoff.  The real quotient
conditions imply all four natural/logarithmic hypotheses required by
`sum_rpow_neg_div_log_Ico_le_saddleScale`. -/
theorem smoothSaddleFloorCutoff_conditions
    {y : ℕ} {R sigma L : ℝ} (hR : 0 < R)
    (hquotFour : 4 ≤ (y : ℝ) / R) (hquotY : (y : ℝ) / R ≤ y)
    (hsigma : sigma < 1)
    (hsmall : ((y : ℝ) / R) ^ (1 - sigma) * Real.log y ≤
      (y : ℝ) ^ (1 - sigma))
    (hL : 0 ≤ L)
    (hlog : Real.log y ≤ L * Real.log ((y : ℝ) / (2 * R))) :
    2 ≤ smoothSaddleFloorCutoff y R ∧
      smoothSaddleFloorCutoff y R ≤ y ∧
      (smoothSaddleFloorCutoff y R : ℝ) ^ (1 - sigma) * Real.log y ≤
        (y : ℝ) ^ (1 - sigma) ∧
      Real.log y ≤ L * Real.log (smoothSaddleFloorCutoff y R) := by
  let q : ℝ := (y : ℝ) / R
  let k : ℕ := smoothSaddleFloorCutoff y R
  have hqFour : 4 ≤ q := by simpa [q] using hquotFour
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hqFour
  have hk : k = ⌊q⌋₊ := by rfl
  have hkTwo : 2 ≤ k := by
    rw [hk]
    exact Nat.le_floor (show (2 : ℝ) ≤ q by linarith [hqFour])
  have hkCastLe : (k : ℝ) ≤ q := by
    rw [hk]
    exact Nat.floor_le hqPos.le
  have hky : k ≤ y := by
    have hkCastY : (k : ℝ) ≤ (y : ℝ) :=
      hkCastLe.trans (by simpa [q] using hquotY)
    exact_mod_cast hkCastY
  have hyOne : (1 : ℝ) ≤ y := by exact_mod_cast (le_trans (by norm_num) (hkTwo.trans hky))
  have hkPower : (k : ℝ) ^ (1 - sigma) ≤ q ^ (1 - sigma) :=
    Real.rpow_le_rpow (by positivity) hkCastLe (sub_nonneg.mpr hsigma.le)
  have hkSmall : (k : ℝ) ^ (1 - sigma) * Real.log y ≤
      (y : ℝ) ^ (1 - sigma) := by
    refine (mul_le_mul_of_nonneg_right hkPower (Real.log_nonneg hyOne)).trans ?_
    simpa [q] using hsmall
  have hkLower : q / 2 ≤ (k : ℝ) := by
    have hfloor := Nat.lt_floor_add_one q
    rw [← hk] at hfloor
    linarith [hqFour]
  have hqHalfPos : 0 < q / 2 := by positivity
  have hkPos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hkTwo)
  have hlogLower : Real.log (q / 2) ≤ Real.log (k : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hqHalfPos hkPos hkLower
  have hkLog : Real.log y ≤ L * Real.log (k : ℝ) := by
    refine hlog.trans ?_
    have hrewrite : (y : ℝ) / (2 * R) = q / 2 := by
      dsimp [q]
      field_simp
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left hlogLower hL
  simpa [k] using ⟨hkTwo, hky, hkSmall, hkLog⟩

/-- The canonical divisor automatically discharges the power comparison in
the normalized split; only quotient size and logarithmic comparability remain. -/
theorem sum_rpow_neg_div_log_Ico_le_canonicalSaddleCutoff
    {y : ℕ} (hy : 2 ≤ y) {sigma L : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1)
    (hquotFour : 4 ≤ (y : ℝ) / smoothSaddleDivisor y sigma)
    (hquotY : (y : ℝ) / smoothSaddleDivisor y sigma ≤ y)
    (hL : 0 ≤ L)
    (hlog : Real.log y ≤ L * Real.log
      ((y : ℝ) / (2 * smoothSaddleDivisor y sigma))) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
        (1 / Real.log 2 + L) := by
  obtain ⟨hk, hky, hsmall, hklog⟩ := smoothSaddleFloorCutoff_conditions
    (smoothSaddleDivisor_pos hy sigma) hquotFour hquotY hsigmaOne
    (smoothSaddleQuotient_rpow_mul_log hy hsigmaOne).le hL hlog
  exact sum_rpow_neg_div_log_Ico_le_saddleScale hk hky hsigma hsigmaOne hsmall hklog

/-- Canonical cutoff estimate with `L=2`.  The remaining analytic hypothesis
is the transparent saddle separation `2R ≤ sqrt y`. -/
theorem sum_rpow_neg_div_log_Ico_le_canonicalSaddleCutoff_two
    {y : ℕ} (hy : 4 ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1)
    (hlogOne : 1 ≤ Real.log (y : ℝ))
    (hhalf : 2 * smoothSaddleDivisor y sigma ≤ Real.sqrt y) :
    ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n ≤
      ((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
        (1 / Real.log 2 + 2) := by
  apply sum_rpow_neg_div_log_Ico_le_canonicalSaddleCutoff
    (by omega) hsigma hsigmaOne
    (four_le_div_of_two_mul_le_sqrt hy
      (smoothSaddleDivisor_pos (by omega) sigma) hhalf)
  · exact div_le_self (Nat.cast_nonneg y)
      (one_le_smoothSaddleDivisor hlogOne hsigmaOne)
  · norm_num
  · exact log_self_le_two_mul_log_div_two_mul
      (by omega) (smoothSaddleDivisor_pos (by omega) sigma) hhalf

/-- Fully explicit, if deliberately coarse, bound for the weighted prime sum.
It is a useful unconditional baseline and the starting point for the sharper
square-root range split. -/
theorem primeRpowSum_le_explicit_crude
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
        smoothPrimeCountingConstant * sigma *
          ((y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2)) := by
  refine (primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    hy hsigma hsigmaOne.le).trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left
      (sum_rpow_neg_div_log_Ico_le hy hsigma hsigmaOne)
      (mul_nonneg smoothPrimeCountingConstant_pos.le hsigma)) _

/-- Weighted-prime bound retaining the two-scale logarithmic gain. -/
theorem primeRpowSum_le_explicit_split
    {k y : ℕ} (hk : 2 ≤ k) (hky : k ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
        smoothPrimeCountingConstant * sigma *
          ((k : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2) +
            (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log k)) := by
  refine (primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    (le_trans hk hky) hsigma hsigmaOne.le).trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left
      (sum_rpow_neg_div_log_Ico_le_split hk hky hsigma hsigmaOne)
      (mul_nonneg smoothPrimeCountingConstant_pos.le hsigma)) _

/-- Weighted-prime estimate at the normalized saddle scale, conditional only
on the two elementary cutoff comparisons. -/
theorem primeRpowSum_le_saddleScale
    {k y : ℕ} (hk : 2 ≤ k) (hky : k ≤ y) {sigma L : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1)
    (hsmall : (k : ℝ) ^ (1 - sigma) * Real.log y ≤
      (y : ℝ) ^ (1 - sigma))
    (hlog : Real.log y ≤ L * Real.log k) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
        smoothPrimeCountingConstant * sigma *
          (((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
            (1 / Real.log 2 + L)) := by
  refine (primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    (le_trans hk hky) hsigma hsigmaOne.le).trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left
      (sum_rpow_neg_div_log_Ico_le_saddleScale
        hk hky hsigma hsigmaOne hsmall hlog)
      (mul_nonneg smoothPrimeCountingConstant_pos.le hsigma)) _

/-- Weighted-prime estimate driven by an arbitrary monotone cutoff chain.
This is the source-facing finite interface for the critical multi-scale
argument. -/
theorem primeRpowSum_le_monotoneChain
    (c : ℕ → ℕ) (hc : Monotone c) (hcStart : c 0 = 2) (m : ℕ)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    (∑ p ∈ (Finset.Icc 2 (c m)).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (c m : ℝ) ^ (1 - sigma) /
          Real.log (c m) +
        smoothPrimeCountingConstant * sigma *
          smoothPowerLogChainMajorant c m sigma := by
  have hc0 : 2 ≤ c 0 := by rw [hcStart]
  have hcm : 2 ≤ c m := hc0.trans (hc (Nat.zero_le m))
  refine (primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    hcm hsigma hsigmaOne.le).trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left
      (by
        simpa [hcStart] using
          (sum_rpow_neg_div_log_Ico_le_monotone_chain
            c hc hc0 m hsigma hsigmaOne))
      (mul_nonneg smoothPrimeCountingConstant_pos.le hsigma)) _

/-- Weighted-prime estimate for the concrete saturated dyadic chain. -/
theorem primeRpowSum_le_dyadicChain
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
        smoothPrimeCountingConstant * sigma *
          smoothPowerLogChainMajorant (smoothDyadicCutoff y)
            (smoothDyadicSteps y) sigma := by
  have h := primeRpowSum_le_monotoneChain
    (smoothDyadicCutoff y) (monotone_smoothDyadicCutoff y)
    (smoothDyadicCutoff_zero hy) (smoothDyadicSteps y) hsigma hsigmaOne
  rw [smoothDyadicCutoff_steps hy] at h
  exact h

/-- Weighted-prime estimate with the sharp explicit dyadic block sum. -/
theorem primeRpowSum_le_dyadicBlocks
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaOne : sigma < 1) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
        smoothPrimeCountingConstant * sigma *
          (∑ i ∈ Finset.range (smoothDyadicSteps y),
            smoothDyadicBlockEnvelope i sigma) := by
  refine (primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    hy hsigma hsigmaOne.le).trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left
      (sum_rpow_neg_div_log_Ico_le_dyadicBlocks hy hsigma)
      (mul_nonneg smoothPrimeCountingConstant_pos.le hsigma)) _

/-- The normalized weighted-prime estimate with the canonical floored cutoff;
the exact power comparison is discharged by construction. -/
theorem primeRpowSum_le_canonicalSaddleScale
    {y : ℕ} (hy : 2 ≤ y) {sigma L : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1)
    (hquotFour : 4 ≤ (y : ℝ) / smoothSaddleDivisor y sigma)
    (hquotY : (y : ℝ) / smoothSaddleDivisor y sigma ≤ y)
    (hL : 0 ≤ L)
    (hlog : Real.log y ≤ L * Real.log
      ((y : ℝ) / (2 * smoothSaddleDivisor y sigma))) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
        smoothPrimeCountingConstant * sigma *
          (((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
            (1 / Real.log 2 + L)) := by
  refine (primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    hy hsigma hsigmaOne.le).trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left
      (sum_rpow_neg_div_log_Ico_le_canonicalSaddleCutoff
        hy hsigma hsigmaOne hquotFour hquotY hL hlog)
      (mul_nonneg smoothPrimeCountingConstant_pos.le hsigma)) _

/-- Canonical weighted-prime saddle estimate with the fixed comparison
factor `L=2`.  The square-root separation also supplies the cutoff-size
condition. -/
theorem primeRpowSum_le_canonicalSaddleScale_two
    {y : ℕ} (hy : 4 ≤ y) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma < 1)
    (hlogOne : 1 ≤ Real.log (y : ℝ))
    (hhalf : 2 * smoothSaddleDivisor y sigma ≤ Real.sqrt y) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) ≤
      smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
        smoothPrimeCountingConstant * sigma *
          (((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
            (1 / Real.log 2 + 2)) := by
  refine (primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    (by omega) hsigma hsigmaOne.le).trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left
      (sum_rpow_neg_div_log_Ico_le_canonicalSaddleCutoff_two
        hy hsigma hsigmaOne hlogOne hhalf)
      (mul_nonneg smoothPrimeCountingConstant_pos.le hsigma)) _

/-- The source-convention smooth-number Rankin bound after the weighted prime
sum has been discharged by explicit Chebyshev and finite Abel summation.  Only
the elementary finite expression displayed here remains to be estimated and
the parameter `sigma` optimized. -/
theorem psiNat_cast_le_self_mul_exp_chebyshevRankinExponent
    {X y : ℕ} {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          ((y : ℝ) ^ (-sigma) * chebyshevPrimeCountingMajorant y +
            ∑ n ∈ Finset.Ico 2 y,
              ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
                chebyshevPrimeCountingMajorant n)) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_chebyshevMajorant y hsigma.le

/-- Final finite Rankin reduction with the prime-counting input normalized to
the standard explicit shape `C n / log n`. -/
theorem psiNat_cast_le_self_mul_exp_logarithmicRankinExponent
    {X y : ℕ} {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          ((y : ℝ) ^ (-sigma) * logarithmicPrimeCountingMajorant y +
            ∑ n ∈ Finset.Ico 2 y,
              ((n : ℝ) ^ (-sigma) - (n + 1 : ℕ) ^ (-sigma)) *
                logarithmicPrimeCountingMajorant n)) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_logarithmicPrimeCountingMajorant y hsigma.le

/-- Rankin's bound with the weighted prime contribution reduced to the
first-order finite sum that is ready for integral comparison. -/
theorem psiNat_cast_le_self_mul_exp_logarithmicFirstOrderRankinExponent
    {X y : ℕ} {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          ((y : ℝ) ^ (-sigma) * logarithmicPrimeCountingMajorant y +
            ∑ n ∈ Finset.Ico 2 y,
              ((n : ℝ) ^ (-sigma) * (sigma / n)) *
                logarithmicPrimeCountingMajorant n)) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_logarithmicPrimeCountingMajorant_firstOrder
    y hsigma.le hsigmaOne

/-- Source-facing Rankin estimate whose sole non-elementary finite term is the
canonical power-log sum. -/
theorem psiNat_cast_le_self_mul_exp_powerLogRankinExponent
    {X y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
            smoothPrimeCountingConstant * sigma *
              ∑ n ∈ Finset.Ico 2 y, (n : ℝ) ^ (-sigma) / Real.log n)) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_endpoint_add_const_mul_sum_rpow_div_log
    hy hsigma.le hsigmaOne

/-- A completely closed elementary Rankin estimate.  It is coarser than the
eventual saddle bound sought in Proposition 2.1 because it uses `log 2`
uniformly, but contains no unevaluated finite sum. -/
theorem psiNat_cast_le_self_mul_exp_explicitCrudeRankinExponent
    {X y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma)
    (hsigmaOne : sigma < 1) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
            smoothPrimeCountingConstant * sigma *
              ((y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2)))) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_explicit_crude hy hsigma.le hsigmaOne

/-- Source-facing two-scale Rankin estimate.  Choosing `k` near a fixed power
of `y` makes the first term power-smaller and the second denominator comparable
to `log y`, which is the precise input for the remaining saddle optimization. -/
theorem psiNat_cast_le_self_mul_exp_explicitSplitRankinExponent
    {X k y : ℕ} (hk : 2 ≤ k) (hky : k ≤ y) {sigma : ℝ}
    (hX : 1 ≤ X) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
            smoothPrimeCountingConstant * sigma *
              ((k : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log 2) +
                (y : ℝ) ^ (1 - sigma) / ((1 - sigma) * Real.log k)))) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_explicit_split hk hky hsigma.le hsigmaOne

/-- Source-facing saddle-scale Rankin estimate.  Once a concrete cutoff `k`
satisfies the two displayed elementary comparisons, the full prime
contribution has the correct growing `log y` denominator. -/
theorem psiNat_cast_le_self_mul_exp_saddleScaleRankinExponent
    {X k y : ℕ} (hk : 2 ≤ k) (hky : k ≤ y) {sigma L : ℝ}
    (hX : 1 ≤ X) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hsmall : (k : ℝ) ^ (1 - sigma) * Real.log y ≤
      (y : ℝ) ^ (1 - sigma))
    (hlog : Real.log y ≤ L * Real.log k) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
            smoothPrimeCountingConstant * sigma *
              (((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
                (1 / Real.log 2 + L)))) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_saddleScale hk hky hsigma.le hsigmaOne hsmall hlog

/-- Source-facing Rankin estimate whose weighted-prime contribution is
controlled by an arbitrary monotone cutoff chain. -/
theorem psiNat_cast_le_self_mul_exp_monotoneChainRankinExponent
    {X : ℕ} (c : ℕ → ℕ) (hc : Monotone c) (hcStart : c 0 = 2) (m : ℕ)
    {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma)
    (hsigmaOne : sigma < 1) :
    (psiNat X (c m) : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (c m : ℝ) ^ (1 - sigma) /
              Real.log (c m) +
            smoothPrimeCountingConstant * sigma *
              smoothPowerLogChainMajorant c m sigma)) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_monotoneChain
    c hc hcStart m hsigma.le hsigmaOne

/-- Source-facing Rankin estimate for the concrete saturated dyadic chain. -/
theorem psiNat_cast_le_self_mul_exp_dyadicChainRankinExponent
    {X y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hX : 1 ≤ X)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) /
              Real.log y +
            smoothPrimeCountingConstant * sigma *
              smoothPowerLogChainMajorant
                (smoothDyadicCutoff y) (smoothDyadicSteps y) sigma)) := by
  have h := psiNat_cast_le_self_mul_exp_monotoneChainRankinExponent
    (smoothDyadicCutoff y) (monotone_smoothDyadicCutoff y)
    (smoothDyadicCutoff_zero hy) (smoothDyadicSteps y) hX hsigma hsigmaOne
  rw [smoothDyadicCutoff_steps hy] at h
  exact h

/-- Source-facing Rankin estimate with the sharp explicit dyadic block sum. -/
theorem psiNat_cast_le_self_mul_exp_dyadicBlocksRankinExponent
    {X y : ℕ} (hy : 2 ≤ y) {sigma : ℝ} (hX : 1 ≤ X)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) /
              Real.log y +
            smoothPrimeCountingConstant * sigma *
              (∑ i ∈ Finset.range (smoothDyadicSteps y),
                smoothDyadicBlockEnvelope i sigma))) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_dyadicBlocks hy hsigma.le hsigmaOne

/-- Source-facing Rankin estimate with the canonical integer cutoff.  Its
power comparison is now definitional; the remaining assumptions are only the
large-quotient and logarithmic-comparability conditions for Tao's regimes. -/
theorem psiNat_cast_le_self_mul_exp_canonicalSaddleRankinExponent
    {X y : ℕ} (hy : 2 ≤ y) {sigma L : ℝ} (hX : 1 ≤ X)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hquotFour : 4 ≤ (y : ℝ) / smoothSaddleDivisor y sigma)
    (hquotY : (y : ℝ) / smoothSaddleDivisor y sigma ≤ y)
    (hL : 0 ≤ L)
    (hlog : Real.log y ≤ L * Real.log
      ((y : ℝ) / (2 * smoothSaddleDivisor y sigma))) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
            smoothPrimeCountingConstant * sigma *
              (((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
                (1 / Real.log 2 + L)))) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_canonicalSaddleScale
    hy hsigma.le hsigmaOne hquotFour hquotY hL hlog

/-- Canonical source-facing Rankin estimate with the fixed constant `L=2`.
After the exact divisor choice and floor transfer, its sole saddle-size
hypothesis is `2 * smoothSaddleDivisor y sigma ≤ sqrt y`. -/
theorem psiNat_cast_le_self_mul_exp_canonicalSaddleRankinExponent_two
    {X y : ℕ} (hy : 4 ≤ y) {sigma : ℝ} (hX : 1 ≤ X)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hlogOne : 1 ≤ Real.log (y : ℝ))
    (hhalf : 2 * smoothSaddleDivisor y sigma ≤ Real.sqrt y) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          (smoothPrimeCountingConstant * (y : ℝ) ^ (1 - sigma) / Real.log y +
            smoothPrimeCountingConstant * sigma *
              (((y : ℝ) ^ (1 - sigma) / (1 - sigma) / Real.log y) *
                (1 / Real.log 2 + 2)))) := by
  have hfactor : 0 ≤ (1 - (2 : ℝ) ^ (-sigma))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  refine (psiNat_cast_le_self_mul_exp_rankinExponent hX hsigma).trans ?_
  gcongr
  exact primeRpowSum_le_canonicalSaddleScale_two
    hy hsigma.le hsigmaOne hlogOne hhalf

/-- The explicit positive error left after optimizing the elementary Rankin
saddle and compressing the dyadic prime-sum contribution. -/
def smoothDyadicSaddleError (X y : ℕ) : ℝ :=
  (1 - (2 : ℝ) ^ (-smoothRankinSigma X y))⁻¹ *
    (smoothPrimeCountingConstant * smoothRankinRatio X y / Real.log y +
      smoothPrimeCountingConstant * smoothRankinSigma X y *
        ((5 * smoothRankinRatio X y /
          Real.log (smoothRankinRatio X y)) / Real.log 2))

/-- Finite optimized Rankin interface after the dyadic scalar sum has been
compressed.  The negative exponent is exactly `-u log u`, while every
positive contribution is displayed at the lower order `u / log u` scale. -/
theorem psiNat_cast_le_self_mul_exp_dyadicSaddleRankinExponent
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (huOne : 1 < smoothRankinRatio X y)
    (hsigma : 0 < smoothRankinSigma X y)
    (hscalar :
      smoothExponentialHarmonicSum (smoothDyadicSteps y)
          (1 - smoothRankinSigma X y) ≤
        5 * smoothRankinRatio X y /
          Real.log (smoothRankinRatio X y)) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-smoothRankinRatio X y * Real.log (smoothRankinRatio X y) +
        smoothDyadicSaddleError X y) := by
  have hsigmaOne : smoothRankinSigma X y < 1 :=
    smoothRankinSigma_lt_one hy huOne
  have h := psiNat_cast_le_self_mul_exp_dyadicBlocksRankinExponent
    hy (by omega : 1 ≤ X) hsigma hsigmaOne
  rw [smoothRankin_saving_identity hy,
    rpow_one_sub_smoothRankinSigma hX hy,
    sum_smoothDyadicBlockEnvelope_eq] at h
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hsum :
      smoothExponentialHarmonicSum (smoothDyadicSteps y)
          (1 - smoothRankinSigma X y) / Real.log 2 ≤
        (5 * smoothRankinRatio X y /
          Real.log (smoothRankinRatio X y)) / Real.log 2 :=
    div_le_div_of_nonneg_right hscalar hlogTwo.le
  have hfactor : 0 ≤
      (1 - (2 : ℝ) ^ (-smoothRankinSigma X y))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma)).le
  have hcoefficient : 0 ≤
      smoothPrimeCountingConstant * smoothRankinSigma X y :=
    mul_nonneg smoothPrimeCountingConstant_pos.le hsigma.le
  refine h.trans ?_
  unfold smoothDyadicSaddleError
  gcongr

end

end Tao2026
