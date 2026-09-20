import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Finset.Interval
import TaoTrudgianYang2025.AdditiveEnergy

/-!
# Large-value patterns

This module formalizes the tuple in `large-pattern-def`.  The integer points
of the real dyadic interval are carried as data together with an exact
membership specification; this avoids silently rounding either endpoint.
The coefficients have the paper's `n⁻ⁱᵗ` sign convention.
-/

open Complex

noncomputable section

namespace TaoTrudgianYang2025

/-- The complex phase `n⁻ⁱᵗ`, written without an ambiguous natural-power
coercion. -/
def dirichletPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.cpow (n : ℂ) (-(Complex.I * (t : ℂ)))

/-- A finite set of real ordinates is one-separated. -/
def IsOneSeparated (W : Finset ℝ) : Prop :=
  ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|

/-- The source large-value pattern, including the exact dyadic integer
support, interval length, coefficient normalization, separation, and lower
large-value threshold. -/
structure LargeValuePattern where
  N : ℝ
  scale : ℕ
  T : ℝ
  V : ℝ
  coeff : ℕ → ℂ
  indices : Finset ℕ
  intervalLeft : ℝ
  intervalRight : ℝ
  ordinates : Finset ℝ
  N_eq_scale : N = (scale : ℝ)
  one_lt_N : 1 < N
  T_pos : 0 < T
  V_pos : 0 < V
  mem_indices_iff : ∀ n : ℕ,
    n ∈ indices ↔ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N
  coeff_one_bounded : ∀ n ∈ indices, ‖coeff n‖ ≤ 1
  interval_length : intervalRight - intervalLeft = T
  ordinates_in_interval : ∀ t ∈ ordinates,
    intervalLeft ≤ t ∧ t ≤ intervalRight
  ordinates_oneSeparated : IsOneSeparated ordinates
  large : ∀ t ∈ ordinates,
    V ≤ ‖∑ n ∈ indices, coeff n * dirichletPhase n t‖

/-- The active interval of a zeta pattern is an integer interval. -/
def IsIntegerInterval (I : Finset ℕ) : Prop :=
  ∃ a b : ℕ, I = Finset.Icc a b

/-- A zeta large-value pattern: the ordinate interval is `[T,2T]` and the
coefficients on the dyadic block are the indicator of an integer interval
contained in that block. -/
structure ZetaLargeValuePattern extends LargeValuePattern where
  active : Finset ℕ
  active_isInterval : IsIntegerInterval active
  active_subset : active ⊆ indices
  coeff_eq_indicator : ∀ n ∈ indices,
    coeff n = if n ∈ active then 1 else 0
  intervalLeft_eq : intervalLeft = T
  intervalRight_eq : intervalRight = 2 * T

theorem LargeValuePattern.ordinate_card_le_of_mem_Icc
    (P : LargeValuePattern) :
    ∀ t ∈ P.ordinates, P.intervalLeft ≤ t ∧ t ≤ P.intervalRight :=
  P.ordinates_in_interval

theorem LargeValuePattern.ordinate_card_cast_le
    (P : LargeValuePattern) :
    (P.ordinates.card : ℝ) ≤ P.T + 1 := by
  have hlength : 0 ≤ P.intervalRight - P.intervalLeft := by
    rw [P.interval_length]
    exact P.T_pos.le
  simpa [P.interval_length] using
    oneSeparated_card_cast_le_interval_length_add_one P.ordinates
      P.ordinates_oneSeparated hlength P.ordinates_in_interval

/-- The stored support is exactly the natural dyadic interval determined by
the integral scale. -/
theorem LargeValuePattern.indices_eq_dyadicInterval
    (P : LargeValuePattern) :
    P.indices = Finset.Icc P.scale (2 * P.scale) := by
  ext n
  rw [P.mem_indices_iff, P.N_eq_scale]
  simp only [Finset.mem_Icc]
  norm_cast

/-- Every index in a large-value pattern is positive. -/
theorem LargeValuePattern.index_pos
    (P : LargeValuePattern) {n : ℕ} (hn : n ∈ P.indices) :
    0 < n := by
  have hnLower := (P.mem_indices_iff n).mp hn |>.1
  have hNPos : 0 < P.N := lt_trans zero_lt_one P.one_lt_N
  exact_mod_cast lt_of_lt_of_le hNPos hnLower

/-- The dyadic support contains exactly `scale + 1` natural numbers. -/
theorem LargeValuePattern.indices_card (P : LargeValuePattern) :
    P.indices.card = P.scale + 1 := by
  rw [P.indices_eq_dyadicInterval]
  simp
  omega

/-- The real scale is bounded by the support cardinality. -/
theorem LargeValuePattern.N_le_indices_card_cast (P : LargeValuePattern) :
    P.N ≤ (P.indices.card : ℝ) := by
  rw [P.indices_card, Nat.cast_add, Nat.cast_one, P.N_eq_scale]
  linarith

/-- The support cardinality is at most twice the real scale. -/
theorem LargeValuePattern.indices_card_cast_le_two_mul_N
    (P : LargeValuePattern) :
    (P.indices.card : ℝ) ≤ 2 * P.N := by
  rw [P.indices_card, Nat.cast_add, Nat.cast_one, P.N_eq_scale]
  have h : (1 : ℝ) < P.scale := by simpa [P.N_eq_scale] using P.one_lt_N
  linarith

/-- The unweighted Dirichlet phase has unit norm on the dyadic support. -/
theorem LargeValuePattern.norm_dirichletPhase
    (P : LargeValuePattern) {n : ℕ} (hn : n ∈ P.indices) (t : ℝ) :
    ‖dirichletPhase n t‖ = 1 := by
  simpa [dirichletPhase] using
    Complex.norm_natCast_cpow_of_pos (P.index_pos hn)
      (-(Complex.I * (t : ℂ)))

/-- At zero frequency every unweighted Dirichlet phase is one. -/
theorem dirichletPhase_zero (n : ℕ) : dirichletPhase n 0 = 1 := by
  simp [dirichletPhase]

end TaoTrudgianYang2025
