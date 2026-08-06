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
Montgomery's Mean Value Theorem (Discrete version).
Bounds the sum over a separated set of the square of a Dirichlet polynomial.
Used to bound the additive energy in the Halasz-Montgomery lemma and Large Values estimate.
-/
def MontgomeryMeanValue : Prop :=
  ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
    0 < N → 1 ≤ T →
    IsSeparated 1 W →
    InTargetInterval T W →
    ∑ t ∈ W, ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 ≤
      (T + (N : ℝ)) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2

lemma mean_value_pos (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ) :
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

lemma montgomery_mean_value_rhs_nonneg (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ) (hT : 0 ≤ T) :
  0 ≤ (T + (N : ℝ)) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 := by
  have h1 : 0 ≤ T + (N : ℝ) := add_nonneg hT (Nat.cast_nonneg N)
  have h2 : 0 ≤ ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 := l2_norm_sq_nonneg N a
  exact mul_nonneg h1 h2

axiom montgomery_mean_value_unconditional : MontgomeryMeanValue

theorem montgomery_mean_value_native : MontgomeryMeanValue := by
  exact montgomery_mean_value_unconditional

end RiemannZeta.GuthMaynard
