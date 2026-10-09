import Dubon2026.DualMatrixStrictUnits

/-! # Actual strict conjugation and its adjoint coboundary -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original lift conjugated by the literal strict matrix `I + epsilon X`. -/
def matrixFirstOrderConjugate (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) (X : Matrix ι ι R) : MatrixFirstOrderLift ρ := by
  refine ⟨{
    toFun := fun g => dualMatrixStrictUnit X * τ.val g * (dualMatrixStrictUnit X)⁻¹
    map_one' := by simp
    map_mul' := by intros; simp [map_mul, mul_assoc] }, ?_⟩
  apply MonoidHom.ext
  intro g
  change dualMatrixReduction (dualMatrixStrictUnit X * τ.val g *
    (dualMatrixStrictUnit X)⁻¹) = ρ g
  simp only [map_mul, map_inv, dualMatrixStrictUnit_reduction, one_mul, inv_one, mul_one]
  exact DFunLike.congr_fun τ.property g

/-- The original strict conjugation has its literal matrix value at every group element. -/
theorem matrixFirstOrderConjugate_apply (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) (X : Matrix ι ι R) (g : G) :
    (matrixFirstOrderConjugate ρ τ X).val g =
      dualMatrixStrictUnit X * τ.val g * (dualMatrixStrictUnit X)⁻¹ := rfl

/-- Strict conjugation changes the actual original cocycle by the displayed adjoint coboundary. -/
theorem matrixFirstOrderConjugate_cocycle (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) (X : Matrix ι ι R) (g : G) :
    matrixFirstOrderCocycle ρ (matrixFirstOrderConjugate ρ τ X) g =
      matrixFirstOrderCocycle ρ τ g + X - (ρ g).val * X * (ρ g⁻¹).val := by
  change dualMatrixInfinitesimal (dualMatrixStrictUnit X * τ.val g *
    (dualMatrixStrictUnit X)⁻¹) = _
  rw [dualMatrixInfinitesimal_strictConjugate,
    show dualMatrixReduction (τ.val g) = ρ g from DFunLike.congr_fun τ.property g,
    map_inv]
  rfl

/-- The difference between the original cocycle and its strictly conjugated cocycle is the actual degree-zero coboundary of the original matrix. -/
theorem matrixFirstOrderConjugate_coboundary (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) (X : Matrix ι ι R) :
    (fun g => matrixFirstOrderCocycle ρ τ g -
      matrixFirstOrderCocycle ρ (matrixFirstOrderConjugate ρ τ X) g) =
        groupCohomology.d₀₁ (matrixAdjointRep ρ) X := by
  funext g
  rw [matrixFirstOrderConjugate_cocycle]
  change _ = (ρ g).val * X * (ρ g⁻¹).val - X
  abel

end
end Dubon2026
