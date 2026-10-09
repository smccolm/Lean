import Dubon2026.DualMatrixInfinitesimal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # The actual matrix adjoint representation and first-order cocycles -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original general-linear representation acts on original matrices by its actual conjugation operators. -/
def matrixAdjointRepresentation (ρ : G →* GeneralLinearGroup ι R) :
    Representation R G (Matrix ι ι R) where
  toFun g :=
    { toFun := fun X => (ρ g).val * X * (ρ g⁻¹).val
      map_add' X Y := by simp [mul_add, add_mul]
      map_smul' a X := by simp }
  map_one' := by
    apply LinearMap.ext
    intro X
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro X
    simp [_root_.mul_inv_rev, map_mul, mul_assoc]

/-- The original adjoint representation as an actual object of Mathlib's representation category. -/
abbrev matrixAdjointRep (ρ : G →* GeneralLinearGroup ι R) : Rep R G :=
  Rep.of (matrixAdjointRepresentation ρ)

/-- The original matrix adjoint action retains its exact conjugation formula. -/
theorem matrixAdjointRep_apply (ρ : G →* GeneralLinearGroup ι R) (g : G)
    (X : Matrix ι ι R) :
    (matrixAdjointRep ρ).ρ g X = (ρ g).val * X * (ρ g⁻¹).val := rfl

/-- An actual first-order lift is a genuine dual-number group representation whose actual reduction is the original representation. -/
def MatrixFirstOrderLift (ρ : G →* GeneralLinearGroup ι R) :=
  {τ : G →* GeneralLinearGroup ι (DualNumber R) // dualMatrixReduction.comp τ = ρ}

/-- The actual first-order part of a genuine lift is a cocycle for the original adjoint representation. -/
def matrixFirstOrderCocycle (ρ : G →* GeneralLinearGroup ι R) (τ : MatrixFirstOrderLift ρ) :
    groupCohomology.cocycles₁ (matrixAdjointRep ρ) := by
  refine ⟨fun g => dualMatrixInfinitesimal (τ.val g), ?_⟩
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro g h
  have hg : dualMatrixReduction (τ.val g) = ρ g := DFunLike.congr_fun τ.property g
  change dualMatrixInfinitesimal (τ.val (g * h)) =
    (ρ g).val * dualMatrixInfinitesimal (τ.val h) * (ρ g⁻¹).val +
      dualMatrixInfinitesimal (τ.val g)
  rw [map_mul, dualMatrixInfinitesimal_mul, hg, map_inv, add_comm]

/-- The cocycle constructed from the original lift has its exact original first-order matrix value. -/
theorem matrixFirstOrderCocycle_apply (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) (g : G) :
    matrixFirstOrderCocycle ρ τ g = dualMatrixInfinitesimal (τ.val g) := rfl

end
end Dubon2026
