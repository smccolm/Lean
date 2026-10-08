import Dubon2026.RealIwasawaMeasure

/-! # Exact elementary matrices and commutators in the actual real special linear group -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The actual real upper unipotent matrix. -/
def realUpperUnipotent (t : ℝ) : SL(2, ℝ) := ⟨!![1, t; 0, 1], by simp⟩

/-- The actual real lower unipotent matrix. -/
def realLowerUnipotent (t : ℝ) : SL(2, ℝ) := ⟨!![1, 0; t, 1], by simp⟩

/-- The actual determinant-one real diagonal matrix. -/
def realDiagonal (a : ℝ) (ha : a ≠ 0) : SL(2, ℝ) := ⟨!![a, 0; 0, a⁻¹], by simp [ha]⟩

/-- The actual Weyl matrix interchanging the coordinate axes. -/
def realWeyl : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp⟩

/-- Every original upper unipotent matrix is a literal commutator of actual real matrices. -/
theorem realUpperUnipotent_commutator (t : ℝ) :
    realDiagonal 2 (by norm_num) * realUpperUnipotent (t / 3) *
      (realDiagonal 2 (by norm_num))⁻¹ * (realUpperUnipotent (t / 3))⁻¹ =
        realUpperUnipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realUpperUnipotent, realDiagonal, coe_mul, coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Every original lower unipotent matrix is a literal commutator of actual real matrices. -/
theorem realLowerUnipotent_commutator (t : ℝ) :
    realDiagonal 2 (by norm_num) * realLowerUnipotent (-4 * t / 3) *
      (realDiagonal 2 (by norm_num))⁻¹ * (realLowerUnipotent (-4 * t / 3))⁻¹ =
        realLowerUnipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realLowerUnipotent, realDiagonal, coe_mul, coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The genuine Weyl matrix is the exact product of three original elementary matrices. -/
theorem realWeyl_eq_unipotents :
    realWeyl = realUpperUnipotent (-1) * realLowerUnipotent 1 * realUpperUnipotent (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realWeyl, realUpperUnipotent, realLowerUnipotent, coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Every actual nonzero real diagonal matrix is the precise finite elementary word. -/
theorem realDiagonal_eq_unipotents (a : ℝ) (ha : a ≠ 0) :
    realDiagonal a ha = realUpperUnipotent a * realLowerUnipotent (-a⁻¹) *
      realUpperUnipotent a * realWeyl := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realDiagonal, realUpperUnipotent, realLowerUnipotent, realWeyl,
      coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha]

/-- Gaussian elimination is exact for the original real matrix with nonzero first entry. -/
theorem realSL2_gauss (g : SL(2, ℝ)) (ha : g 0 0 ≠ 0) :
    g = realLowerUnipotent (g 1 0 / g 0 0) * realDiagonal (g 0 0) ha *
      realUpperUnipotent (g 0 1 / g 0 0) := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realLowerUnipotent, realDiagonal, realUpperUnipotent, coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, ha]
  all_goals field_simp [ha]
  all_goals nlinarith [hd]

/-- If the first original entry vanishes, the Weyl translate has nonzero first entry. -/
theorem realWeyl_mul_first_ne_zero (g : SL(2, ℝ)) (ha : g 0 0 = 0) :
    (realWeyl * g) 0 0 ≠ 0 := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hc : g 1 0 ≠ 0 := by intro hc; simp [ha, hc] at hd
  simpa [realWeyl, coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using hc

end
end Dubon2026
