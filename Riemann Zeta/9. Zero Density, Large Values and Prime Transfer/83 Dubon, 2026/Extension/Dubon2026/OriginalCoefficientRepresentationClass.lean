import Dubon2026.OriginalCoefficientFramedEquivalence
import Dubon2026.OriginalUnframedDeformationClasses

/-! # Actual original deformation classes from continuous trace-coefficient evaluation -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Evaluate each original matrix of a continuous coefficient representation through a genuine continuous residue-preserving coefficient map, obtaining the actual existing original framed fiber. -/
def originalCoefficientRepresentationFramed
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (f : OriginalContinuousCoefficientFiber eR eA) : OriginalContinuousFramedFiber eA H σ := by
  have hmap : Continuous (GeneralLinearGroup.map (n := ι) f.val.toRingHom) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact f.property.1.comp (continuous_apply_apply i j)
  refine ⟨⟨(GeneralLinearGroup.map f.val.toRingHom).comp τ.toMonoidHom,
    hmap.comp τ.continuous⟩, ?_⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact (DFunLike.congr_fun f.property.2 ((τ g).val i j)).trans
    (congrArg (fun U : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => U.val i j)
      (DFunLike.congr_fun hτ g))

/-- The actual original unframed deformation class obtained by genuine continuous coefficient evaluation. -/
def originalCoefficientRepresentationClass
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (f : OriginalContinuousCoefficientFiber eR eA) : OriginalUnframedDeformationClass eA H σ :=
  originalUnframedClass eA H σ (originalCoefficientRepresentationFramed eR eA H σ τ hτ f)

/-- Equality of the actual evaluated original classes is exactly strict conjugacy of the whole coefficient-evaluated representations. -/
theorem originalCoefficientRepresentationClass_eq_iff
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (f g : OriginalContinuousCoefficientFiber eR eA) :
    originalCoefficientRepresentationClass eR eA H σ τ hτ f =
        originalCoefficientRepresentationClass eR eA H σ τ hτ g ↔
      MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
        ((GeneralLinearGroup.map f.val.toRingHom).comp τ.toMonoidHom)
        ((GeneralLinearGroup.map g.val.toRingHom).comp τ.toMonoidHom) := by
  exact originalUnframedClass_eq_iff eA H σ _ _

end
end Dubon2026
