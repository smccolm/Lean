import Dubon2026.ArithmeticLocalCotangentLinearity
import Dubon2026.OriginalResidueMaximalCotangent

/-! # Actual relative maximal-ideal cotangent maps of the original arithmetic local ring -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Genuine linear maps from the literal relative maximal-ideal quotient of the original completed arithmetic local ring to its actual residue epsilon ideal. -/
def ArithmeticLocalMaximalCotangentMaps
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Type :=
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  OriginalResidueMaximalCotangentMaps (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The genuine maximal-ideal cotangent maps inherit their actual additive group. -/
instance arithmeticLocalMaximalCotangentMapsAddCommGroup
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : AddCommGroup (ArithmeticLocalMaximalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact inferInstanceAs (AddCommGroup (OriginalResidueMaximalCotangentMaps (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)))

/-- The actual original residue field acts on these original maximal-ideal cotangent maps through epsilon coefficients. -/
instance arithmeticLocalMaximalCotangentMapsModule
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Module (IsLocalRing.ResidueField O) (ArithmeticLocalMaximalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact originalResidueMaximalCotangentMapsModule (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The original relative maximal-ideal quotient and the original universal differential give exactly the same tangent maps of the actual completed arithmetic local ring, linearly over the original residue field. -/
def arithmeticLocalMaximalCotangentLinearEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalMaximalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP ≃ₗ[IsLocalRing.ResidueField O]
      ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact originalResidueMaximalCotangentLinearEquiv (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The literal original relative maximal-ideal quotient is finite-dimensional by the proved Noetherian property of the actual arithmetic local deformation ring. -/
theorem arithmeticLocalRelativeMaximalCotangent_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     Module.Finite (IsLocalRing.ResidueField (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))
       (RelativeMaximalCotangent O (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  letI := (arithmeticUnramifiedDeformationRing_localData a ha p hp hpa σ hσ δ hδ P hP).1
  exact relativeMaximalCotangent_finite O (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)

/-- Actual relative maximal-ideal cotangent maps classify the same whole original continuous first-order representations satisfying the original determinant and inertia conditions. -/
def arithmeticLocalMaximalCotangentLiftEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalMaximalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP ≃ ArithmeticLocalFirstOrderLift a σ P.asIdeal :=
  (arithmeticLocalMaximalCotangentLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).toEquiv.trans
    (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The genuine maps from the original relative maximal-ideal quotient map linearly to the original local continuous cohomology classes. -/
def arithmeticLocalMaximalCotangentClassLinearMap
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalMaximalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP →ₗ[IsLocalRing.ResidueField O]
      arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal :=
  (arithmeticLocalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP).comp
    (arithmeticLocalMaximalCotangentLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).toLinearMap

/-- Every original local continuous cohomology class comes from a genuine map on the literal original relative maximal-ideal cotangent quotient. -/
theorem arithmeticLocalMaximalCotangentClassLinearMap_surjective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalMaximalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalCotangentClassLinearMap_surjective a ha p hp hpa σ hσ δ hδ P hP).comp
    (arithmeticLocalMaximalCotangentLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).surjective

/-- Equality of original local classes of actual maximal-ideal cotangent maps is exactly strict conjugacy of their same whole genuine first-order local arithmetic representations. -/
theorem arithmeticLocalMaximalCotangentClassLinearMap_eq_iff
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (f g : ArithmeticLocalMaximalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalMaximalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP f =
      arithmeticLocalMaximalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP g ↔
        MatrixFirstOrderStrictlyConjugate σ
          (arithmeticLocalMaximalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP f).val.val
          (arithmeticLocalMaximalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP g).val.val :=
  arithmeticLocalCotangentClass_eq_iff a ha p hp hpa σ hσ δ hδ P hP _ _

end
end Dubon2026
