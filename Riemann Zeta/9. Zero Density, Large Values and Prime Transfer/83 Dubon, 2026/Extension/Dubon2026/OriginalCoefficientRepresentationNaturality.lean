import Dubon2026.OriginalCoefficientRepresentationClass
import Dubon2026.OriginalUnframedDeformationNaturality

/-! # Genuine naturality of original coefficient evaluation in unframed deformation classes -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O R A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]

/-- Evaluating the whole original coefficient representation commutes with every genuine continuous residue-preserving coefficient change, in the actual existing unframed deformation classes. -/
theorem originalCoefficientRepresentationClass_natural
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (f : OriginalContinuousCoefficientFiber eR eA) :
    originalUnframedPostcomp eA eB H σ k hk hres
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) =
      originalCoefficientRepresentationClass eR eB H σ τ hτ
        (originalCoefficientFiberPostcomp eR eA eB k hk hres f) := by
  change originalUnframedPostcomp eA eB H σ k hk hres
      (originalUnframedClass eA H σ (originalCoefficientRepresentationFramed eR eA H σ τ hτ f)) = _
  rw [originalUnframedPostcomp_class]
  apply congrArg (originalUnframedClass eB H σ)
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl

end
end Dubon2026
