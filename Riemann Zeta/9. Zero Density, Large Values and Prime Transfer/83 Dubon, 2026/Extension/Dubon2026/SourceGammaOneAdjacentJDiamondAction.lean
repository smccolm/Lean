import Dubon2026.SourceGammaOneAdjacentJDiamondMatrix

/-! DUB-17/18 -> original Gamma1 norm reduction -> the diamond convention
of the reverse map. The literal integral matrix calculation identifies
double dilation around the coprime lift with the actual diamond matrix
on the upper half-plane. Native scalar matrices act trivially. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

theorem adjacentJDiamondMatrix_gl (p : ℕ) [NeZero p] (γ : SL(2, ℤ))
    (hd : (p : ℤ) ∣ γ 1 1) :
    levelRaiseMatrix p * mapGL ℝ γ * levelRaiseMatrix p =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 (p : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne p))) *
          mapGL ℝ (adjacentJDiamondMatrix p γ hd) := by
  have he : (p : ℝ) * ((γ 1 1 / (p : ℤ) : ℤ) : ℝ) = (γ 1 1 : ℝ) := by
    rw [mul_comm, ← Int.cast_natCast (R := ℝ), ← Int.cast_mul, Int.ediv_mul_cancel hd]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, mapGL_coe_matrix,
    Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [levelRaiseMatrix, adjacentJDiamondMatrix, Matrix.GeneralLinearGroup.scalar,
      Matrix.natCast_apply, he, mul_comm]

theorem adjacentJDiamondMatrix_smul (p : ℕ) [NeZero p] (γ : SL(2, ℤ))
    (hd : (p : ℤ) ∣ γ 1 1) (τ : ℍ) :
    levelRaiseMatrix p • (γ • (levelRaiseMatrix p • τ)) =
      adjacentJDiamondMatrix p γ hd • τ := by
  change levelRaiseMatrix p • (mapGL ℝ γ • (levelRaiseMatrix p • τ)) = _
  rw [← mul_smul, ← mul_smul, adjacentJDiamondMatrix_gl p γ hd,
    mul_smul, glScalar_smul]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne
