import Dubon2026.DualNumberCoefficientOperations
import Dubon2026.CoefficientFiberProductRepresentation
import Dubon2026.ContinuousFirstOrderDeformation

/-! # Original first-order addition through the genuine coefficient fiber product -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing k]

/-- The two original first-order representations glue in the actual ring of
coefficient pairs with the same original residue. -/
def matrixFirstOrderPair (ρ : G →* GeneralLinearGroup ι k)
    (τ υ : MatrixFirstOrderLift ρ) :
    G →* GeneralLinearGroup ι
      (CoefficientFiberProduct (TrivSqZeroExt.fstHom k k k).toRingHom
        (TrivSqZeroExt.fstHom k k k).toRingHom) :=
  coefficientFiberProductRepresentation _ _ τ.val υ.val (τ.property.trans υ.property.symm)

/-- Add the genuine first-order parts by the actual compatible-pair coefficient
map, retaining the entire original residual representation. -/
def matrixFirstOrderSum (ρ : G →* GeneralLinearGroup ι k)
    (τ υ : MatrixFirstOrderLift ρ) : MatrixFirstOrderLift ρ := by
  refine ⟨(GeneralLinearGroup.map (dualNumberCompatibleAddition k)).comp
    (matrixFirstOrderPair ρ τ υ), ?_⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact congrArg (fun U : GeneralLinearGroup ι k => U.val i j)
    (DFunLike.congr_fun τ.property g)

/-- The original compatible-pair coefficient map induces exactly addition of the
original right-logarithmic adjoint cocycles, with the same matrix convention. -/
theorem matrixFirstOrderSum_cocycle (ρ : G →* GeneralLinearGroup ι k)
    (τ υ : MatrixFirstOrderLift ρ) :
    matrixFirstOrderCocycle ρ (matrixFirstOrderSum ρ τ υ) =
      matrixFirstOrderCocycle ρ τ + matrixFirstOrderCocycle ρ υ := by
  apply groupCohomology.cocycles₁_ext
  intro g
  have hτ : dualMatrixReduction (τ.val g) = ρ g := DFunLike.congr_fun τ.property g
  have hυ : dualMatrixReduction (υ.val g) = ρ g := DFunLike.congr_fun υ.property g
  have hsum : dualMatrixReduction ((matrixFirstOrderSum ρ τ υ).val g) = ρ g :=
    DFunLike.congr_fun (matrixFirstOrderSum ρ τ υ).property g
  have hs : dualMatrixSnd ((matrixFirstOrderSum ρ τ υ).val g).val =
      dualMatrixSnd (τ.val g).val + dualMatrixSnd (υ.val g).val := rfl
  change dualMatrixInfinitesimal ((matrixFirstOrderSum ρ τ υ).val g) =
    dualMatrixInfinitesimal (τ.val g) + dualMatrixInfinitesimal (υ.val g)
  simp only [dualMatrixInfinitesimal, hsum, hτ, hυ, hs, add_mul]

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [IsTopologicalRing k]

/-- The entire first-order sum is continuous because its actual cocycle is the sum
of the two original continuous cocycles. The existing continuity equivalence proves
continuity of both the original matrices and their inverses. -/
theorem matrixFirstOrderSum_continuous (ρ : G →* GeneralLinearGroup ι k)
    (hρ : Continuous ρ) (τ υ : MatrixFirstOrderLift ρ)
    (hτ : Continuous τ.val) (hυ : Continuous υ.val) :
    Continuous (matrixFirstOrderSum ρ τ υ).val := by
  apply (matrixFirstOrderLift_continuous_iff ρ hρ _).mpr
  rw [matrixFirstOrderSum_cocycle]
  exact (matrixFirstOrderCocycle_continuous ρ hρ τ hτ).add
    (matrixFirstOrderCocycle_continuous ρ hρ υ hυ)

end
end Dubon2026
