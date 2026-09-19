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

end TaoTrudgianYang2025
