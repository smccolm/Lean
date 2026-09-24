import TaoTrudgianYang2025.ClassicalReflectedSourceData

/-!
# Literal reflected coefficients as a fixed-line polynomial

The reflected weight is not replaced by arbitrary bounded coefficients.
Its exact right-endpoint normalization is retained when it is identified
with the existing fixed-line polynomial at real parameter -sigma.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalReflectedCoeff_eq_scaled_line
    (sigma : ℝ) (M n : ℕ) (hn : 0 < n) :
    normalizedTypeIReflectedCoeff sigma M n =
      (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) *
        classicalZetaLongLineCoeff M (-sigma) n := by
  by_cases hnM : n ≤ M
  · rw [normalizedTypeIReflectedCoeff, if_pos ⟨by omega, hnM⟩,
      classicalZetaLongLineCoeff, if_pos hnM]
    simp only [Complex.ofReal_neg, neg_neg]
    have hpow := Complex.ofReal_cpow (Nat.cast_nonneg n) sigma
    simp only [Complex.ofReal_natCast] at hpow
    rw [← hpow, Real.rpow_neg (Nat.cast_nonneg M)]
    push_cast
    ring
  · simp [normalizedTypeIReflectedCoeff, classicalZetaLongLineCoeff, hnM]

theorem dirichletPoly_reflected_eq_scaled_line
    (sigma t : ℝ) (N M : ℕ) :
    dirichletPoly N (normalizedTypeIReflectedCoeff sigma M) t =
      (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) *
        dirichletPoly N (classicalZetaLongLineCoeff M (-sigma)) t := by
  unfold dirichletPoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Nat.zero_le N).trans_lt (Finset.mem_Ioc.mp hn).1
  rw [classicalReflectedCoeff_eq_scaled_line sigma M n hnpos]
  ring

theorem norm_dirichletPoly_reflected_eq_scaled_line
    (sigma t : ℝ) (N M : ℕ) :
    ‖dirichletPoly N (normalizedTypeIReflectedCoeff sigma M) t‖ =
      (M : ℝ) ^ (-sigma) *
        ‖dirichletPoly N (classicalZetaLongLineCoeff M (-sigma)) t‖ := by
  rw [dirichletPoly_reflected_eq_scaled_line, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg M) _)]


theorem rpow_mul_norm_reflected_eq_norm_line
    (sigma t : ℝ) (N M : ℕ) (hM : 0 < M) :
    (M : ℝ) ^ sigma *
        ‖dirichletPoly N (normalizedTypeIReflectedCoeff sigma M) t‖ =
      ‖dirichletPoly N (classicalZetaLongLineCoeff M (-sigma)) t‖ := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [norm_dirichletPoly_reflected_eq_scaled_line, ← mul_assoc,
    ← Real.rpow_add hMpos, add_neg_cancel, Real.rpow_zero, one_mul]


end TaoTrudgianYang2025
