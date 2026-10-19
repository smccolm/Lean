import Dubon2026.ArithmeticUniversalAuxiliaryRepresentation
import Dubon2026.AuxiliaryFamilyAugmentationRepresentation

/-! Compose the augmentation specialization with a universal-matrix
comparison while the target ring is abstract. The actual base-support
target and comparison are supplied by the arithmetic consumer. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- An actual auxiliary universal quotient comparison transports the
constructed character augmentation and every universal matrix. -/
def arithmeticAuxiliaryAugmentationRepresentationComparison
    {ι n O A : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    [CommRing A] [Algebra O A]
    (b : 𝓞 ℚ) (hb : b ≠ 0) (q : ℕ) (hq : q.Prime) (hqb : (q : 𝓞 ℚ) ∣ b)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup n (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes) (D : Q → Type) [∀ p, Group (D p)]
    (τ₀ : rationalArithmeticGaloisGroup b → GeneralLinearGroup n A)
    (e : (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q) ≃ₐ[O] A)
    (he : ∀ g, GeneralLinearGroup.map e.toAlgHom.toRingHom
      (arithmeticAuxiliaryUniversalRepresentation b hb q hq hqb σ hσ δ Q g) = τ₀ g) :
    (letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
     AuxiliaryFamilyAugmentationSpecialization O (ι := ι) D
       (arithmeticAuxiliaryInertiaRelationIdeal b Q
         (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom) →
     AuxiliaryFamilyAugmentationRepresentationComparison O (ι := ι) D
       (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ) τ₀) := by
  letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
  intro d
  exact auxiliaryFamilyAugmentationRepresentationComparison O D
    (arithmeticAuxiliaryInertiaRelationIdeal b Q
      (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom)
    (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ) τ₀ d e he

end
end Dubon2026
