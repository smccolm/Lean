import Dubon2026.MatrixAdjointCocycles
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Actual invariant matrices and Schur's lemma for the original matrix action -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- The same original general-linear representation acts on its original column vectors. -/
def matrixStandardRepresentation (ρ : G →* GeneralLinearGroup ι K) :
    Representation K G (ι → K) where
  toFun g := Matrix.toLin' (ρ g).val
  map_one' := by
    change Matrix.toLin' (ρ 1).val = 1
    rw [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    change Matrix.toLin' (ρ (g * h)).val = Matrix.toLin' (ρ g).val * Matrix.toLin' (ρ h).val
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

/-- Invariance under the original adjoint action implies commutation with every original representation matrix. -/
theorem matrixAdjointInvariant_commute (ρ : G →* GeneralLinearGroup ι K)
    (X : (matrixAdjointRepresentation ρ).invariants) (g : G) :
    (ρ g).val * X.val = X.val * (ρ g).val := by
  have h := congrArg (fun Y : Matrix ι ι K => Y * (ρ g).val) (X.property g)
  change ((ρ g).val * X.val * (ρ g⁻¹).val) * (ρ g).val = X.val * (ρ g).val at h
  simpa only [map_inv, mul_assoc, Units.inv_mul, mul_one] using h

/-- Every genuine invariant matrix is an intertwining endomorphism of the same original column-vector representation. -/
def matrixAdjointInvariantIntertwining (ρ : G →* GeneralLinearGroup ι K)
    (X : (matrixAdjointRepresentation ρ).invariants) :
    Representation.IntertwiningMap (matrixStandardRepresentation ρ) (matrixStandardRepresentation ρ) where
  toLinearMap := Matrix.toLin' X.val
  isIntertwining' g := by
    change Matrix.toLin' X.val ∘ₗ Matrix.toLin' (ρ g).val =
      Matrix.toLin' (ρ g).val ∘ₗ Matrix.toLin' X.val
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, matrixAdjointInvariant_commute ρ X g]

/-- Over an algebraically closed coefficient field, actual irreducibility of the original column-vector representation forces every original invariant matrix to be scalar. -/
theorem matrixAdjointInvariant_eq_scalar [IsAlgClosed K]
    (ρ : G →* GeneralLinearGroup ι K) [Representation.IsIrreducible (matrixStandardRepresentation ρ)]
    (X : (matrixAdjointRepresentation ρ).invariants) :
    ∃ c : K, X.val = c • (1 : Matrix ι ι K) := by
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := matrixStandardRepresentation ρ)).surjective (matrixAdjointInvariantIntertwining ρ X)
  refine ⟨c, ?_⟩
  apply Matrix.toLin'.injective
  rw [map_smul, Matrix.toLin'_one]
  exact (congrArg Representation.IntertwiningMap.toLinearMap hc).symm

end
end Dubon2026
