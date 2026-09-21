import TaoTrudgianYang2025.ZetaFourthTerm
import TaoTrudgianYang2025.DirichletPrefixMeanSquare

/-!
# Actual ordinary-divisor coefficients of the fourth-moment prefix

The complex phase is kept with its reflected sign. The complete finite
source is exactly the Dirichlet prefix evaluated at u-t.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaFourthCoeff (c : ℝ) (n : ℕ) : ℂ :=
  divisorDirichletTerm ((1/2+c:ℝ):ℂ) n

theorem zetaFourthCoeff_zero (c : ℝ) : zetaFourthCoeff c 0 = 0 := by
  simp [zetaFourthCoeff,divisorDirichletTerm]

theorem zetaFourthCoeff_one (c : ℝ) : zetaFourthCoeff c 1 = 1 := by
  simp [zetaFourthCoeff,divisorDirichletTerm_eq_divisorWeight_mul_cpow,divisorWeight]

theorem norm_zetaFourthCoeff (c : ℝ) (n : ℕ) :
    ‖zetaFourthCoeff c n‖ = (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c)) := by
  simpa [zetaFourthCoeff,afeCriticalPoint] using norm_fourth_divisorTerm_vertical 0 c 0 n

theorem fourth_divisorTerm_eq_coeff_phase (t c u : ℝ) (n : ℕ) :
    divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n =
      zetaFourthCoeff c n*Complex.exp (-(I*((u-t):ℂ)*(Real.log n:ℂ))) := by
  by_cases hn : n = 0
  · subst n
    simp [divisorDirichletTerm,zetaFourthCoeff_zero]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  rw [zetaFourthCoeff,divisorDirichletTerm_eq_divisorWeight_mul_cpow,
    divisorDirichletTerm_eq_divisorWeight_mul_cpow,
    Complex.cpow_def_of_ne_zero hnC,Complex.cpow_def_of_ne_zero hnC,
    mul_assoc (divisorWeight n),← Complex.exp_add]
  congr 1
  congr 1
  rw [← Complex.natCast_log]
  dsimp [afeCriticalPoint]
  push_cast
  ring

theorem sum_fourth_divisorTerm_eq_prefix (t c u : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N+1),
      divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n) =
        dirichletPrefix N (zetaFourthCoeff c) (u-t) := by
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N,
        divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n := by
      symm
      apply Finset.sum_subset
      · intro n hn
        simp only [Finset.mem_Ioc,Finset.mem_range] at *
        omega
      · intro n hn hnot
        have hn0 : n = 0 := by
          simp only [Finset.mem_Ioc,Finset.mem_range] at *
          omega
        subst n
        simp [divisorDirichletTerm]
    _ = _ := by
      simp only [fourth_divisorTerm_eq_coeff_phase,dirichletPrefix,Complex.ofReal_sub]

end TaoTrudgianYang2025
