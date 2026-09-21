import TaoTrudgianYang2025.ZetaFourthCoefficientMass

/-!
# Mean square of the actual finite ordinary-divisor polynomial

Every coefficient-mass premise of the complete-prefix bound is discharged.
The estimate is uniform in the contour's imaginary translation.
-/

noncomputable section

open Complex MeasureTheory
open scoped Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_integral_sq_fourthPolynomial_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ,
      ∀ H : ℝ, 0 ≤ H → ∀ u : ℝ,
      (∫ t : ℝ in H..2*H,
        ‖dirichletPrefix (2^M) (zetaFourthCoeff c) (u-t)‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε := by
  obtain ⟨C,hC,hcoeff⟩ := exists_sum_sq_zetaFourthCoeff_dyadic_le hε
  refine ⟨2*C,by linarith,?_⟩
  intro c hc M H hH u
  let L : ℝ := C*((2:ℝ)^M)^ε
  have hpow : 1 ≤ ((2:ℝ)^M)^ε :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hε.le
  have hone : ‖zetaFourthCoeff c 1‖^2 ≤ L := by
    simp only [zetaFourthCoeff_one,norm_one,one_pow]
    dsimp [L]
    nlinarith
  have hmass : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖zetaFourthCoeff c n‖^2) ≤ L := by
    intro j hj
    have hjM : j+1 ≤ M := Finset.mem_range.mp hj
    have hsize : 2*((2^j:ℕ):ℝ) ≤ (2:ℝ)^M := by
      norm_cast
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) hjM
    apply (hcoeff c hc (2^j) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hsize hε.le) (by linarith)
  calc
    _ ≤ 2*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*L :=
      integral_norm_sq_dirichletPrefix_reflected_le M (zetaFourthCoeff c) u hH hone hmass
    _ = _ := by dsimp [L]; ring

theorem exists_integral_sq_fourthDivisorSum_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ,
      ∀ H : ℝ, 0 ≤ H → ∀ u : ℝ,
      (∫ t : ℝ in H..2*H,
        ‖∑ n ∈ Finset.range (2^M+1),
          divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε := by
  simpa only [sum_fourth_divisorTerm_eq_prefix] using
    exists_integral_sq_fourthPolynomial_le hε

end TaoTrudgianYang2025
