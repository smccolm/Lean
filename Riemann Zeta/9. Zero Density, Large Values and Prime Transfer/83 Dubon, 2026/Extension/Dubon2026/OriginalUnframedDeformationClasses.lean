import Dubon2026.OriginalResidualFramedFibers
import Dubon2026.MatrixRepresentationStrictConjugacy

/-! # Actual strict-conjugacy classes of the original continuous framed deformation fiber -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- The actual strict-conjugacy equivalence relation on the existing original continuous framed fiber. -/
def originalFramedStrictSetoid
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Setoid (OriginalContinuousFramedFiber eA H σ) where
  r ρ τ := MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
    ρ.val.toMonoidHom τ.val.toMonoidHom
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro ρ
      exact matrixStrictlyConjugate_refl (localCoefficientReduction eA).toRingHom
        ρ.val.toMonoidHom
    · intro ρ τ h
      exact matrixStrictlyConjugate_symm (localCoefficientReduction eA).toRingHom
        ρ.val.toMonoidHom τ.val.toMonoidHom h
    · intro ρ τ υ h₁ h₂
      exact matrixStrictlyConjugate_trans (localCoefficientReduction eA).toRingHom
        ρ.val.toMonoidHom τ.val.toMonoidHom υ.val.toMonoidHom h₁ h₂

/-- Actual unframed deformation classes of the existing whole original continuous fixed-residue lifts. -/
def OriginalUnframedDeformationClass
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  Quotient (originalFramedStrictSetoid eA H σ)

/-- The actual class of an original whole continuous framed lift. -/
def originalUnframedClass
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ : OriginalContinuousFramedFiber eA H σ) :
    OriginalUnframedDeformationClass eA H σ :=
  Quotient.mk _ ρ

/-- Equality of the genuine original deformation classes is exactly an original invertible conjugator reducing to the identity and conjugating every element of the original profinite group. -/
theorem originalUnframedClass_eq_iff
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ τ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedClass eA H σ ρ = originalUnframedClass eA H σ τ ↔
      ∃ U : GeneralLinearGroup ι A,
        GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom U = 1 ∧
        ∀ x : H, τ.val x = U * ρ.val x * U⁻¹ := by
  constructor
  · exact fun h => Quotient.exact h
  · exact fun h => Quotient.sound h

/-- Every actual unframed deformation class has a representative in the original whole continuous framed fiber with its original residual condition. -/
theorem originalUnframedClass_surjective
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Function.Surjective (originalUnframedClass eA H σ) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro ρ
  exact ⟨ρ, rfl⟩

end
end Dubon2026
