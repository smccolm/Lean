import Dubon2026.OriginalUnframedFixedQuotientEquivalence
import Dubon2026.OriginalCoefficientRepresentationClass

/-! # Actual coefficient evaluation through the original fixed-residual quotient -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- The actual existing unframed fixed-quotient equivalence commutes with original coefficient evaluation of the same whole original representation and its genuine quotient factor. -/
theorem originalCoefficientRepresentationClass_fixedQuotient
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (τq : fixedResidualProfiniteQuotient p H σ.ker
      (originalResidualMatrixKernel_isClosed H σ hσ) →ₜ* GeneralLinearGroup ι R)
    (hτq : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τq.toMonoidHom = (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom)
    (hwhole : ∀ g : H, τ g = τq (QuotientGroup.mk'
      (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) g))
    (f : OriginalContinuousCoefficientFiber eR eA) :
    originalUnframedFixedQuotientEquiv hA eA p hp H σ hσ
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) =
      originalCoefficientRepresentationClass eR eA _
        (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom τq hτq f := by
  change originalUnframedFixedQuotientEquiv hA eA p hp H σ hσ
    (originalUnframedClass eA H σ (originalCoefficientRepresentationFramed eR eA H σ τ hτ f)) = _
  rw [originalUnframedFixedQuotientEquiv_class]
  apply congrArg (originalUnframedClass eA _
    (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom)
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) x
  change GeneralLinearGroup.map f.val.toRingHom (τ g) =
    GeneralLinearGroup.map f.val.toRingHom (τq (QuotientGroup.mk'
      (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) g))
  rw [hwhole g]

/-- A proved actual class bijection for the genuine original fixed-residual quotient transfers to the entire original group, through the existing quotient equivalence and exact original matrix evaluation. -/
theorem originalCoefficientRepresentationClass_fixedQuotient_bijective
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (τq : fixedResidualProfiniteQuotient p H σ.ker
      (originalResidualMatrixKernel_isClosed H σ hσ) →ₜ* GeneralLinearGroup ι R)
    (hτq : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τq.toMonoidHom = (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom)
    (hwhole : ∀ g : H, τ g = τq (QuotientGroup.mk'
      (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) g))
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eR eA _
      (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom τq hτq)) :
    Function.Bijective (originalCoefficientRepresentationClass eR eA H σ τ hτ) := by
  let e := originalUnframedFixedQuotientEquiv hA eA p hp H σ hσ
  have he (f : OriginalContinuousCoefficientFiber eR eA) :=
    originalCoefficientRepresentationClass_fixedQuotient hA eR eA p hp H σ hσ
      τ hτ τq hτq hwhole f
  constructor
  · intro f g hfg
    apply hbij.1
    exact (he f).symm.trans ((congrArg e hfg).trans (he g))
  · intro c
    obtain ⟨f, hf⟩ := hbij.2 (e c)
    refine ⟨f, e.injective ?_⟩
    exact (he f).trans hf

end
end Dubon2026
