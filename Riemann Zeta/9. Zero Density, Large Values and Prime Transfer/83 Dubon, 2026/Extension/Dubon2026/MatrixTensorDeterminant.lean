import Dubon2026.DeterminantCoefficientLaw
import Dubon2026.GroupAlgebraScalarExtension

/-! # The determinant family on the literal scalar-extended group algebra -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped TensorProduct

variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] [Algebra R S]

/-- Evaluate the actual determinant on the literal tensor extension of the original group algebra. -/
def matrixTensorDeterminant (ρ : G →* GeneralLinearGroup ι R) :
    S ⊗[R] MonoidAlgebra R G →* S :=
  (determinantCoefficientLaw ρ (algebraMap R S)).comp
    groupAlgebraScalarExtensionEquiv.toMonoidHom

/-- On every simple tensor the actual determinant is the expected homogeneous extension of the original determinant. -/
theorem matrixTensorDeterminant_tmul (ρ : G →* GeneralLinearGroup ι R)
    (a : S) (x : MonoidAlgebra R G) :
    matrixTensorDeterminant ρ (a ⊗ₜ[R] x) =
      a ^ Fintype.card ι * algebraMap R S (matrixRepresentationDeterminant ρ x) := by
  change determinantCoefficientLaw ρ (algebraMap R S)
    (groupAlgebraScalarExtensionEquiv (a ⊗ₜ[R] x)) = _
  rw [groupAlgebraScalarExtensionEquiv_tmul, determinantCoefficientLaw_homogeneous]
  congr 1
  exact (matrixRepresentationDeterminant_map ρ (algebraMap R S) x).symm

/-- The literal tensor determinant has the correct degree on all tensors, including sums of simple tensors. -/
theorem matrixTensorDeterminant_homogeneous (ρ : G →* GeneralLinearGroup ι R)
    (a : S) (x : S ⊗[R] MonoidAlgebra R G) :
    matrixTensorDeterminant ρ (a • x) =
      a ^ Fintype.card ι * matrixTensorDeterminant ρ x := by
  change determinantCoefficientLaw ρ (algebraMap R S)
    (groupAlgebraScalarExtensionEquiv (a • x)) = _
  rw [map_smul, determinantCoefficientLaw_homogeneous]
  rfl

/-- The determinant family is natural on the literal tensor extensions under every coefficient-algebra homomorphism. -/
theorem matrixTensorDeterminant_natural {T : Type*} [CommRing T] [Algebra R T]
    (ρ : G →* GeneralLinearGroup ι R) (ψ : S →ₐ[R] T)
    (x : S ⊗[R] MonoidAlgebra R G) :
    ψ (matrixTensorDeterminant ρ x) =
      matrixTensorDeterminant ρ
        (Algebra.TensorProduct.map ψ (AlgHom.id R (MonoidAlgebra R G)) x) := by
  change ψ.toRingHom (determinantCoefficientLaw ρ (algebraMap R S)
    (groupAlgebraScalarExtensionEquiv x)) = _
  rw [determinantCoefficientLaw_natural, groupAlgebraScalarExtensionEquiv_natural]
  have hψ : ψ.toRingHom.comp (algebraMap R S) = algebraMap R T := by
    ext r
    exact ψ.commutes r
  rw [hψ]
  rfl

end
end Dubon2026
