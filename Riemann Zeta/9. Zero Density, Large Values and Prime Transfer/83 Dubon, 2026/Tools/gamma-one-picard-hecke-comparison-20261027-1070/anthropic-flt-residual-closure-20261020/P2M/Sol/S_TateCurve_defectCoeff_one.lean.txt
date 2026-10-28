import Definitions.Def_TateCurve_Defect
import P2M.Util
namespace P2MW.S_TateCurve_defectCoeff_one
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) : defectCoeff u 1 = 0 := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hP1 : xCoeffFull u 1 = u + u⁻¹ - 2 := by
    rw [xCoeffFull_succ, xCoeff, Nat.divisors_one, Finset.sum_singleton, xDivTerm]
    push_cast; ring
  have hQ1 : yCoeffFull u 1 = 1 - u⁻¹ := by
    rw [yCoeffFull_succ, yCoeff, Nat.divisors_one, Finset.sum_singleton, yDivTerm]
    norm_num [show Nat.choose 1 2 = 0 from rfl]; ring
  have hA41 : a₄Coeff (K := K) 1 = -5 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, a₄Coeff_succ]
    norm_num [Nat.divisors_one]
  have hA61 : a₆Coeff (K := K) 1 = -1 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, a₆Coeff_succ]
    norm_num [Nat.divisors_one, b_one]
  simp only [defectCoeff, cauchyMul_one, cauchyMul_zero, hP1, hQ1, hA41, hA61, xCoeffFull_zero,
    yCoeffFull_zero, a₄Coeff_zero, xfun, yfun]
  field_simp
  ring
