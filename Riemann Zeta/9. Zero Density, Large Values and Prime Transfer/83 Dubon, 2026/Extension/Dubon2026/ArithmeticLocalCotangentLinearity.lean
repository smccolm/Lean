import Dubon2026.ArithmeticLocalCotangentPoints
import Dubon2026.ArithmeticLocalDerivationLinearity
import Dubon2026.OriginalResidueCotangentLinearity

/-! # Original residue-field linearity for the actual arithmetic local cotangent maps -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Genuine cotangent maps of the original arithmetic local ring inherit their actual additive group. -/
instance arithmeticLocalCotangentMapsAddCommGroup
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : AddCommGroup (ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact inferInstanceAs (AddCommGroup (OriginalResidueCotangentMaps (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)))

/-- The original residue field acts on the actual relative cotangent maps through their epsilon coefficients. -/
instance arithmeticLocalCotangentMapsModule
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Module (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact originalResidueCotangentMapsModule (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The universal differential of the literal original arithmetic local ring gives a genuine residue-field-linear equivalence of its cotangent maps and relative residue derivations. -/
def arithmeticLocalCotangentDerivationLinearEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP ≃ₗ[IsLocalRing.ResidueField O]
      ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact originalResidueCotangentDerivationLinearEquiv (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The actual cotangent-to-derivation linear equivalence preserves the entire original local first-order representation. -/
theorem arithmeticLocalCotangentDerivationLinearEquiv_lift
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d : ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP
      (arithmeticLocalCotangentDerivationLinearEquiv a ha p hp hpa σ hσ δ hδ P hP d) =
        arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d := rfl

/-- The actual cotangent maps of the original local ring map linearly to its original local continuous cohomology classes. -/
def arithmeticLocalCotangentClassLinearMap
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP →ₗ[IsLocalRing.ResidueField O]
      arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal :=
  (arithmeticLocalResidueDerivationClassLinearMap a ha p hp hpa σ hσ δ hδ P hP).comp
    (arithmeticLocalCotangentDerivationLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).toLinearMap

/-- The genuine cotangent class linear map is the same original local cohomology class obtained from coefficient-point universality. -/
theorem arithmeticLocalCotangentClassLinearMap_apply
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d : ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP d =
      arithmeticLocalCotangentClass a ha p hp hpa σ hσ δ hδ P hP d := rfl

/-- Every actual local continuous cohomology class is the image of an original relative cotangent map under the same residue-field-linear class map. -/
theorem arithmeticLocalCotangentClassLinearMap_surjective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalResidueDerivationClassLinearMap_surjective a ha p hp hpa σ hσ δ hδ P hP).comp
    (arithmeticLocalCotangentDerivationLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).surjective

end
end Dubon2026
