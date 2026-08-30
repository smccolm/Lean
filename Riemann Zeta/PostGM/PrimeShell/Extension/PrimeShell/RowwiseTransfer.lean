import PrimeShell.F1Verdict

namespace PrimeShell

noncomputable section

open scoped BigOperators

/-- One literal row of the dyadic von-Mangoldt correlation, including the
right endpoint and the exact Zeta23 coefficient normalization. -/
def dyadicLambdaRow (N n h : ℕ) : ℝ :=
  if n + h ∈ Finset.Ioc N (2 * N) then dyadicLambdaWeight n h else 0

/-- The cumulative information needed at one starting point `n`.  Unlike
the rejected collapsed prefix, the `n` coordinate is retained. -/
def dyadicLambdaRowPrefix (N n H : ℕ) : ℝ :=
  cumulativePrefix (dyadicLambdaRow N n) H

/-- Exact row-wise form of the source shift sum. -/
theorem dyadicShiftSum_eq_sum_rows
    (Φ : ℝ → ℝ) (T : ℝ) (N H : ℕ) :
    dyadicShiftSum Φ T N H =
      ∑ n ∈ Finset.Ioc N (2 * N),
        ∑ h ∈ Finset.Icc 1 H,
          dyadicShiftKernel Φ T n h * dyadicLambdaRow N n h := by
  unfold dyadicShiftSum dyadicLambdaRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N)
  · simp only [hmem, if_true]
    ring
  · simp [hmem]

/-- Exact two-dimensional Abel transfer.  It applies summation by parts in
`h` separately for every dyadic starting point, so no kernel row is
collapsed and the concrete F1 obstruction is avoided. -/
theorem dyadicShiftSum_eq_rowwise_abel
    (Φ : ℝ → ℝ) (T : ℝ) (N : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    dyadicShiftSum Φ T N H =
      ∑ n ∈ Finset.Ioc N (2 * N),
        (dyadicShiftKernel Φ T n H * dyadicLambdaRowPrefix N n H +
          ∑ h ∈ Finset.Icc 1 (H - 1),
            (dyadicShiftKernel Φ T n h -
                dyadicShiftKernel Φ T n (h + 1)) *
              dyadicLambdaRowPrefix N n h) := by
  rw [dyadicShiftSum_eq_sum_rows]
  apply Finset.sum_congr rfl
  intro n hn
  exact finite_abel_identity
    (fun h => dyadicShiftKernel Φ T n h)
    (dyadicLambdaRow N n) hH

/-- A finite, row-local arithmetic interface.  It is strictly narrower
than a trace estimate: it mentions only prefixes of the actual weighted
von-Mangoldt row and an explicit nonnegative error budget. -/
def RowwisePrefixBudget (N H : ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ n ∈ Finset.Ioc N (2 * N), 0 ≤ B n ∧
    ∀ J : ℕ, J ≤ H → |dyadicLambdaRowPrefix N n J| ≤ B n

/-- Complete quantitative consumer for the row-local interface.  The right
side retains every literal kernel endpoint and discrete variation. -/
theorem abs_dyadicShiftSum_le_of_rowwise_prefix_budget
    (Φ : ℝ → ℝ) (T : ℝ) (N : ℕ) {H : ℕ} (hH : 1 ≤ H)
    (B : ℕ → ℝ) (hB : RowwisePrefixBudget N H B) :
    |dyadicShiftSum Φ T N H| ≤
      ∑ n ∈ Finset.Ioc N (2 * N),
        B n *
          (|dyadicShiftKernel Φ T n H| +
            scalarKernelTotalVariation
              (fun h => dyadicShiftKernel Φ T n h) H) := by
  rw [dyadicShiftSum_eq_sum_rows]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro n hn
  exact abs_weighted_sum_le_of_prefix_bound
    (fun h => dyadicShiftKernel Φ T n h)
    (dyadicLambdaRow N n) hH
    (fun J hJ => (hB n hn).2 J hJ)

end

end PrimeShell
