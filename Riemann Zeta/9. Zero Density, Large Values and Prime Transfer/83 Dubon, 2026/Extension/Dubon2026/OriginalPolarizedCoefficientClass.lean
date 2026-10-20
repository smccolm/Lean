import Dubon2026.OriginalPolarizedUnframedClasses
import Dubon2026.PolarizedCoefficientContinuity
import Dubon2026.OriginalCoefficientFramedEquivalence

/-! Evaluate the actual trace-ring polarized representation at original
continuous residue-preserving coefficient maps and take its genuine
unframed class. This is the classification map required for DUB-17. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {ι O R A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
  (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
  (H : ProfiniteGrp.{0}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : H →* Oˣ) (τ : H →ₜ* PolarizedGaloisGroup ι R)
  (hτ : (polarizedCoefficientMap (localCoefficientReduction eR).toRingHom).comp τ.toMonoidHom = σ)
  (hν : ∀ g, polarizedSimilitude (τ g) = Units.map (algebraMap O R).toMonoidHom (ν g))

/-- Original continuous coefficient evaluation preserves the entire
polarized residual representation and the original base similitude. -/
def originalPolarizedCoefficientFramed (f : OriginalContinuousCoefficientFiber eR eA) :
    OriginalContinuousPolarizedFiber eA H σ ν := by
  refine ⟨⟨(polarizedCoefficientMap f.val.toRingHom).comp τ.toMonoidHom,
    (polarizedCoefficientMap_continuous f.val.toRingHom f.property.1).comp τ.continuous⟩, ?_, ?_⟩
  · apply MonoidHom.ext
    intro g
    have hr : (localCoefficientReduction eA).toRingHom.comp f.val.toRingHom =
        (localCoefficientReduction eR).toRingHom := congrArg AlgHom.toRingHom f.property.2
    have hm := DFunLike.congr_fun
      (polarizedCoefficientMap_comp (ι := ι) f.val.toRingHom (localCoefficientReduction eA).toRingHom) (τ g)
    rw [hr] at hm
    exact hm.symm.trans (DFunLike.congr_fun hτ g)
  · apply MonoidHom.ext
    intro g
    change polarizedSimilitude (polarizedCoefficientMap f.val.toRingHom (τ g)) = _
    rw [polarizedCoefficientMap_similitude, hν]
    apply Units.ext
    exact f.val.commutes (ν g : O)

/-- The actual polarized unframed class obtained by original coefficient evaluation. -/
def originalPolarizedCoefficientClass (f : OriginalContinuousCoefficientFiber eR eA) :
    OriginalPolarizedUnframedDeformationClass eA H σ ν :=
  originalPolarizedUnframedClass eA H σ ν (originalPolarizedCoefficientFramed eR eA H σ ν τ hτ hν f)

/-- Equality of evaluated original polarized classes is exactly full
strict polarized conjugacy of the coefficient-specialized representations. -/
theorem originalPolarizedCoefficientClass_eq_iff (f g : OriginalContinuousCoefficientFiber eR eA) :
    originalPolarizedCoefficientClass eR eA H σ ν τ hτ hν f =
        originalPolarizedCoefficientClass eR eA H σ ν τ hτ hν g ↔
      PolarizedStrictlyConjugate (localCoefficientReduction eA).toRingHom
        ((polarizedCoefficientMap f.val.toRingHom).comp τ.toMonoidHom)
        ((polarizedCoefficientMap g.val.toRingHom).comp τ.toMonoidHom) :=
  originalPolarizedUnframedClass_eq_iff eA H σ ν _ _

end
end Dubon2026
