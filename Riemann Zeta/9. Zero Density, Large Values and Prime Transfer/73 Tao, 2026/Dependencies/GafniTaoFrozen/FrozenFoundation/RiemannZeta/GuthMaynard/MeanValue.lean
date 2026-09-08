import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannZeta.GuthMaynard.Separated

open Complex Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard


/--
The discrete Dirichlet-polynomial mean-value input used in Section 13.1.

The existentially quantified `C` is an absolute constant: it is chosen before
the polynomial length, height, separated set, and coefficients. This represents
the implied constant in the paper's `≲` notation rather than incorrectly fixing
that constant to one.
-/
def MontgomeryMeanValue : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
      0 < N → 1 ≤ T →
      IsSeparated 1 W →
      InBaseInterval T W →
      ∑ t ∈ W, ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 ≤
        C * (T + (N : ℝ)) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2

lemma mean_value_pos (N : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) :
  0 ≤ ∑ t ∈ W, ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 := by
  apply Finset.sum_nonneg
  intros
  positivity

lemma l2_norm_sq_nonneg (N : ℕ) (a : ℕ → ℂ) :
  0 ≤ ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 := by
  apply Finset.sum_nonneg
  intros
  positivity

lemma l2_norm_sq_zero_iff (N : ℕ) (a : ℕ → ℂ) :
  ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 = 0 ↔ ∀ n ∈ Ioc N (2 * N), a n = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)]
  apply forall_congr'
  intro n
  apply forall_congr'
  intro _
  rw [sq_eq_zero_iff, norm_eq_zero]

lemma montgomery_mean_value_rhs_nonneg (C : ℝ) (N : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) :
    0 ≤ C * (T + (N : ℝ)) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 := by
  have h1 : 0 ≤ T + (N : ℝ) := add_nonneg hT (Nat.cast_nonneg N)
  have h2 : 0 ≤ ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 := l2_norm_sq_nonneg N a
  positivity

end RiemannZeta.GuthMaynard
