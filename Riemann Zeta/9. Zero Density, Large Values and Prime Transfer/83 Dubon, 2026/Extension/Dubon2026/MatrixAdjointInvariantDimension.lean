import Dubon2026.MatrixAdjointScalarDescent
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # The original adjoint invariant dimension under genuine scalar-extension irreducibility -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Original scalar matrices form a genuine coefficient-linear subspace of the original adjoint invariants. -/
def matrixAdjointScalarMap (ρ : G →* GeneralLinearGroup ι K) :
    K →ₗ[K] (matrixAdjointRepresentation ρ).invariants where
  toFun c := ⟨c • (1 : Matrix ι ι K), by
    intro g
    change (ρ g).val * (c • (1 : Matrix ι ι K)) * (ρ g⁻¹).val = c • (1 : Matrix ι ι K)
    rw [mul_smul_comm, mul_one, smul_mul_assoc, map_inv, Units.mul_inv]⟩
  map_add' c d := by
    apply Subtype.ext
    exact add_smul c d (1 : Matrix ι ι K)
  map_smul' c d := by
    apply Subtype.ext
    exact mul_smul c d (1 : Matrix ι ι K)

/-- A diagonal entry recovers the original scalar from a scalar matrix of nonempty size. -/
theorem matrixAdjointScalarMap_injective [Nonempty ι]
    (ρ : G →* GeneralLinearGroup ι K) : Function.Injective (matrixAdjointScalarMap ρ) := by
  intro c d h
  let i : ι := Classical.choice inferInstance
  have hi := congrArg (fun X : (matrixAdjointRepresentation ρ).invariants => X.val i i) h
  simpa [matrixAdjointScalarMap] using hi

variable (L : Type) [Field L] [Algebra K L] [IsAlgClosed L] [Nonempty ι]

/-- Genuine irreducibility over an algebraically closed extension makes every original invariant matrix an original scalar matrix. -/
theorem matrixAdjointScalarMap_surjective_of_extension
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))] :
    Function.Surjective (matrixAdjointScalarMap ρ) := by
  intro X
  obtain ⟨c, hc⟩ := matrixAdjointInvariant_eq_scalar_of_extension (L := L) ρ X
  exact ⟨c, Subtype.ext hc.symm⟩

/-- Under actual scalar-extension irreducibility, the original coefficient field is linearly equivalent to the original adjoint invariant submodule. -/
def matrixAdjointScalarLinearEquivOfExtension
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))] :
    K ≃ₗ[K] (matrixAdjointRepresentation ρ).invariants :=
  LinearEquiv.ofBijective (matrixAdjointScalarMap ρ)
    ⟨matrixAdjointScalarMap_injective ρ, matrixAdjointScalarMap_surjective_of_extension L ρ⟩

/-- Actual scalar-extension irreducibility gives original adjoint invariant dimension one over the original coefficient field. -/
theorem matrixAdjointInvariants_finrank_of_extension
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))] :
    Module.finrank K (matrixAdjointRepresentation ρ).invariants = 1 :=
  (matrixAdjointScalarLinearEquivOfExtension L ρ).symm.finrank_eq.trans (CommSemiring.finrank_self K)

end
end Dubon2026
