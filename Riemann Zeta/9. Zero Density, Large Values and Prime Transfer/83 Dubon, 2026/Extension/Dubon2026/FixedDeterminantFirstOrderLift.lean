import Dubon2026.FirstOrderMatrixDeterminant

/-! # Original fixed-determinant lifts and exact trace-zero adjoint cocycles -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original first-order determinant is fixed exactly when every value of its original adjoint cocycle has trace zero. -/
theorem matrixFirstOrderLift_fixedDeterminant_iff (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) :
    (∀ g, Matrix.det (τ.val g).val =
      TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ↔
        ∀ g, Matrix.trace (matrixFirstOrderCocycle ρ τ g) = 0 := by
  have hr (g : G) : dualMatrixReduction (τ.val g) = ρ g :=
    DFunLike.congr_fun τ.property g
  constructor
  · intro h g
    have he := congrArg TrivSqZeroExt.snd (h g)
    rw [dualMatrixUnit_det, hr] at he
    have hu : IsUnit (Matrix.det (ρ g).val) := (GeneralLinearGroup.det (ρ g)).isUnit
    apply hu.mul_right_cancel
    simpa only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_inl, zero_mul] using he
  · intro h g
    rw [dualMatrixUnit_det, hr]
    change (Matrix.det (ρ g).val,
      Matrix.trace (matrixFirstOrderCocycle ρ τ g) * Matrix.det (ρ g).val) = _
    rw [h, zero_mul]
    rfl

/-- The actual fixed-determinant fiber of original first-order lifts. -/
def MatrixFixedDeterminantLift (ρ : G →* GeneralLinearGroup ι R) :=
  {τ : MatrixFirstOrderLift ρ // ∀ g, Matrix.det (τ.val g).val =
    TrivSqZeroExt.inl (Matrix.det (ρ g).val)}

/-- The original fixed-determinant fiber is equivalent to the actual trace-zero subspace of original adjoint cocycles. -/
def matrixFixedDeterminantLiftEquiv (ρ : G →* GeneralLinearGroup ι R) :
    MatrixFixedDeterminantLift ρ ≃
      {c : groupCohomology.cocycles₁ (matrixAdjointRep ρ) // ∀ g, Matrix.trace (c g) = 0} where
  toFun τ := ⟨matrixFirstOrderCocycle ρ τ.val,
    (matrixFirstOrderLift_fixedDeterminant_iff ρ τ.val).mp τ.property⟩
  invFun c := ⟨firstOrderLiftFromCocycle ρ c.val,
    (matrixFirstOrderLift_fixedDeterminant_iff ρ _).mpr (by
      rw [matrixFirstOrderCocycle_fromCocycle]
      exact c.property)⟩
  left_inv τ := by
    apply Subtype.ext
    exact firstOrderLiftFromCocycle_cocycle ρ τ.val
  right_inv c := by
    apply Subtype.ext
    exact matrixFirstOrderCocycle_fromCocycle ρ c.val

/-- Every original adjoint coboundary has trace zero at every original group element. -/
theorem matrixAdjointCoboundary_trace_zero (ρ : G →* GeneralLinearGroup ι R)
    (X : Matrix ι ι R) (g : G) :
    Matrix.trace (groupCohomology.d₀₁ (matrixAdjointRep ρ) X g) = 0 := by
  change Matrix.trace ((ρ g).val * X * (ρ g⁻¹).val - X) = 0
  rw [Matrix.trace_sub, map_inv, Matrix.trace_units_conj, sub_self]

end
end Dubon2026
