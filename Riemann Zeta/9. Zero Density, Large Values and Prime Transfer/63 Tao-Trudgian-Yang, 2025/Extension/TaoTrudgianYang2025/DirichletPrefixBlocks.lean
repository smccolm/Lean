import TaoTrudgianYang2025.DirichletMeanSquareTranslation
import GuthMaynard.ClassicalLargeValues

/-!
# Exact dyadic decomposition of the complete Dirichlet prefix

The first coefficient is kept explicitly; the remaining positive indices
are partitioned into the actual native mean-square blocks.
-/

noncomputable section

open Complex MeasureTheory
open scoped Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def dirichletPrefix (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, a n*Complex.exp (-(I*(t:ℂ)*(Real.log n:ℂ)))

theorem continuous_dirichletPrefix (N : ℕ) (a : ℕ → ℂ) :
    Continuous (dirichletPrefix N a) := by
  unfold dirichletPrefix
  fun_prop

theorem dirichletPrefix_one (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix 1 a t = a 1 := by
  simp [dirichletPrefix]

theorem dirichletPrefix_double (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix (2*N) a t = dirichletPrefix N a t+dirichletTime N a t := by
  exact (Finset.sum_Ioc_consecutive
    (fun n : ℕ => a n*Complex.exp (-(I*(t:ℂ)*(Real.log n:ℂ))))
    (Nat.zero_le N) (by omega : N ≤ 2*N)).symm

theorem dirichletPrefix_pow_two (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix (2^M) a t =
      a 1+∑ j ∈ Finset.range M, dirichletTime (2^j) a t := by
  induction M with
  | zero => simp [dirichletPrefix_one]
  | succ M ih =>
    rw [pow_succ, Nat.mul_comm (2^M) 2,dirichletPrefix_double,ih,
      Finset.sum_range_succ,add_assoc]

theorem norm_dirichletPrefix_pow_two_sq_le (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖dirichletPrefix (2^M) a t‖^2 ≤
      2*((M:ℝ)+1)*(‖a 1‖^2+∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) := by
  let S : ℂ := ∑ j ∈ Finset.range M, dirichletTime (2^j) a t
  let Q : ℝ := ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : ‖S‖^2 ≤ (M:ℝ)*Q := by
    simpa [S,Q] using norm_sum_mul_sq_le (Finset.range M)
      (fun _ => (1:ℂ)) (fun j => dirichletTime (2^j) a t)
  rw [dirichletPrefix_pow_two]
  change ‖a 1+S‖^2 ≤ 2*((M:ℝ)+1)*(‖a 1‖^2+Q)
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (a 1) S) 2
  have hM : 0 ≤ (M:ℝ) := Nat.cast_nonneg M
  nlinarith [sq_nonneg (‖a 1‖-‖S‖),mul_nonneg hM (sq_nonneg ‖a 1‖)]

end TaoTrudgianYang2025
