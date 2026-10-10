import Dubon2026.OriginalUnframedDeformationClasses
import Dubon2026.MatrixStrictConjugacyConditions

/-! # Genuine determinant and subgroup conditions on the existing original unframed classes -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- The actual prescribed whole determinant condition on an existing original unframed class, well-defined by genuine strict-conjugacy invariance. -/
def originalUnframedHasDeterminant
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : H →* Oˣ) : OriginalUnframedDeformationClass eA H σ → Prop :=
  Quotient.lift (fun ρ : OriginalContinuousFramedFiber eA H σ =>
    ∀ g : H, GeneralLinearGroup.det (ρ.val g) = Units.map (algebraMap O A) (δ g)) (by
      intro ρ τ h
      apply propext
      apply forall_congr'
      intro g
      exact iff_of_eq (congrArg (fun d : Aˣ => d = Units.map (algebraMap O A) (δ g))
        (matrixStrictlyConjugate_det (localCoefficientReduction eA).toRingHom
          ρ.val.toMonoidHom τ.val.toMonoidHom h g).symm))

/-- The determinant condition on the actual class of an original framed lift is precisely its original whole matrix determinant condition. -/
theorem originalUnframedHasDeterminant_class_iff
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : H →* Oˣ) (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedHasDeterminant eA H σ δ (originalUnframedClass eA H σ ρ) ↔
      ∀ g : H, GeneralLinearGroup.det (ρ.val g) = Units.map (algebraMap O A) (δ g) := by
  rfl

/-- The actual condition of killing an original subgroup, including an actual arithmetic inertia subgroup, on an existing original unframed deformation class. -/
def originalUnframedKillsSubgroup
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup H) : OriginalUnframedDeformationClass eA H σ → Prop :=
  Quotient.lift (fun ρ : OriginalContinuousFramedFiber eA H σ => N ≤ ρ.val.toMonoidHom.ker) (by
    intro ρ τ h
    exact congrArg (fun K : Subgroup H => N ≤ K)
      (matrixStrictlyConjugate_ker (localCoefficientReduction eA).toRingHom
        ρ.val.toMonoidHom τ.val.toMonoidHom h))

/-- The subgroup condition on an actual original framed class is exactly containment in the original whole representation kernel. -/
theorem originalUnframedKillsSubgroup_class_iff
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup H) (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedKillsSubgroup eA H σ N (originalUnframedClass eA H σ ρ) ↔
      N ≤ ρ.val.toMonoidHom.ker := by
  rfl

end
end Dubon2026
