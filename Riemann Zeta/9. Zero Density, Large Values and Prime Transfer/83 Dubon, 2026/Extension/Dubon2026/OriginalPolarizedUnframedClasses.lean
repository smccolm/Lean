import Dubon2026.PolarizedFramedMatrixFiber
import Dubon2026.PolarizedRepresentationStrictConjugacy

/-! The actual unframed source polarized deformation classes. The quotient
uses residue-one GL matrices inside the original polarized group, retaining
the full fixed-similitude fiber required for DUB-17. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Genuine strict polarized equivalence on the existing continuous
fixed-residue and fixed-similitude framed fiber. -/
def originalPolarizedFramedStrictSetoid
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
    (ν : H →* Oˣ) : Setoid (OriginalContinuousPolarizedFiber eA H σ ν) where
  r ρ τ := PolarizedStrictlyConjugate (localCoefficientReduction eA).toRingHom
    ρ.val.toMonoidHom τ.val.toMonoidHom
  iseqv := ⟨fun ρ => polarizedStrictlyConjugate_refl _ ρ.val.toMonoidHom,
    fun h => polarizedStrictlyConjugate_symm _ _ _ h,
    fun h₁ h₂ => polarizedStrictlyConjugate_trans _ _ _ _ h₁ h₂⟩

/-- Original continuous unframed polarized deformation classes, with the
source fixed similitude and genuine strict general linear basis changes. -/
def OriginalPolarizedUnframedDeformationClass
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
    (ν : H →* Oˣ) := Quotient (originalPolarizedFramedStrictSetoid eA H σ ν)

/-- The actual unframed class of an original continuous polarized lift. -/
def originalPolarizedUnframedClass
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
    (ν : H →* Oˣ) (ρ : OriginalContinuousPolarizedFiber eA H σ ν) :
    OriginalPolarizedUnframedDeformationClass eA H σ ν := Quotient.mk _ ρ

/-- Equality of original polarized deformation classes is precisely
strict conjugacy of their entire original arithmetic representations. -/
theorem originalPolarizedUnframedClass_eq_iff
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
    (ν : H →* Oˣ) (ρ τ : OriginalContinuousPolarizedFiber eA H σ ν) :
    originalPolarizedUnframedClass eA H σ ν ρ = originalPolarizedUnframedClass eA H σ ν τ ↔
      PolarizedStrictlyConjugate (localCoefficientReduction eA).toRingHom
        ρ.val.toMonoidHom τ.val.toMonoidHom := by
  constructor
  · exact fun h => Quotient.exact h
  · exact fun h => Quotient.sound h

/-- Every original unframed polarized class is represented by an actual
continuous lift in the original fixed-similitude framed fiber. -/
theorem originalPolarizedUnframedClass_surjective
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
    (ν : H →* Oˣ) : Function.Surjective (originalPolarizedUnframedClass eA H σ ν) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro ρ
  exact ⟨ρ, rfl⟩

end
end Dubon2026
