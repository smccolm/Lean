import GuthMaynard.MeanValueProof

/-!
# Translation of the actual Dirichlet-block mean square

The coefficient twist has modulus one. Consequently the continuous
mean square is uniform over every real interval of a fixed length,
including negative intervals needed by the reflected zeta source.
-/

noncomputable section

open Complex MeasureTheory
open scoped Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem dirichletTime_shift (N : ℕ) (a : ℕ → ℂ) (v t : ℝ) :
    dirichletTime N a (t+v) = dirichletTime N (endpointTwist v a) t := by
  unfold dirichletTime
  apply Finset.sum_congr rfl
  intro n _
  rw [endpointTwist,mul_assoc (a n),← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

theorem integral_norm_sq_dirichletTime_interval_le
    (N : ℕ) (a : ℕ → ℂ) {A B : ℝ} (hN : 0 < N) (hAB : A ≤ B) :
    (∫ t : ℝ in A..B, ‖dirichletTime N a t‖^2) ≤
      (B-A+2*(5*Real.pi+1)*(N:ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 := by
  have h := integral_norm_sq_dirichletTime_le N (B-A) (endpointTwist A a)
    hN (sub_nonneg.mpr hAB)
  have heq :
      (∫ t : ℝ in A..B, ‖dirichletTime N a t‖^2) =
        ∫ t : ℝ in 0..B-A, ‖dirichletTime N (endpointTwist A a) t‖^2 := by
    have ht := intervalIntegral.integral_comp_add_right
      (fun t : ℝ => ‖dirichletTime N a t‖^2) A (a := 0) (b := B-A)
    simpa only [dirichletTime_shift,zero_add,sub_add_cancel] using ht.symm
  rw [heq]
  simpa only [norm_endpointTwist] using h

theorem integral_norm_sq_dirichletTime_reflected_le
    (N : ℕ) (a : ℕ → ℂ) (u : ℝ) {H : ℝ} (hN : 0 < N) (hH : 0 ≤ H) :
    (∫ t : ℝ in H..2*H, ‖dirichletTime N a (u-t)‖^2) ≤
      (H+2*(5*Real.pi+1)*(N:ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => ‖dirichletTime N a t‖^2) u]
  have h := integral_norm_sq_dirichletTime_interval_le N a hN
    (show u-2*H ≤ u-H by linarith)
  have heq : u-H-(u-2*H) = H := by ring
  simpa only [heq] using h

end TaoTrudgianYang2025
