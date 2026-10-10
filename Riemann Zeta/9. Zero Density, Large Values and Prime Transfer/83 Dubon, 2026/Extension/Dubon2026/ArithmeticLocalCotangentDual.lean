import Dubon2026.ArithmeticLocalMaximalCotangent
import Dubon2026.OriginalRelativeCotangentDualFiniteness

/-! # The ordinary residue dual and local cohomology dimension of the actual arithmetic local ring -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The ordinary original residue-field dual of the literal relative maximal-ideal quotient of the actual completed arithmetic local deformation ring. -/
def ArithmeticLocalCotangentDual
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Type :=
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  OriginalRelativeMaximalCotangentDual (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The genuine ordinary arithmetic cotangent dual inherits its actual additive group. -/
instance arithmeticLocalCotangentDualAddCommGroup
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : AddCommGroup (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact inferInstanceAs (AddCommGroup (OriginalRelativeMaximalCotangentDual (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)))

/-- The ordinary dual has its genuine original residue-field scalar action. -/
instance arithmeticLocalCotangentDualModule
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Module (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact inferInstanceAs (Module (IsLocalRing.ResidueField O) (OriginalRelativeMaximalCotangentDual (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)))

/-- Original epsilon coefficients identify the genuine ordinary residue dual with actual maximal-ideal cotangent maps of the same completed arithmetic local ring. -/
def arithmeticLocalCotangentDualLinearEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP ≃ₗ[IsLocalRing.ResidueField O]
      ArithmeticLocalMaximalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact (originalMaximalCotangentDualLinearEquiv (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)).symm

/-- The actual original arithmetic cotangent dual is finite-dimensional by genuine Noetherianity of the same completed local ring. -/
theorem arithmeticLocalCotangentDual_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Module.Finite (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  letI := (arithmeticUnramifiedDeformationRing_localData a ha p hp hpa σ hσ δ hδ P hP).1
  exact originalRelativeMaximalCotangentDual_finite (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The ordinary residue dual of the actual relative cotangent quotient maps linearly to the same original local continuous cohomology classes. -/
def arithmeticLocalCotangentDualClassLinearMap
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP →ₗ[IsLocalRing.ResidueField O]
      arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal :=
  (arithmeticLocalMaximalCotangentClassLinearMap a ha p hp hpa σ hσ δ hδ P hP).comp
    (arithmeticLocalCotangentDualLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).toLinearMap

/-- Every original local continuous cohomology class is attained by the ordinary original residue-field dual of the actual relative maximal-ideal quotient. -/
theorem arithmeticLocalCotangentDualClassLinearMap_surjective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalCotangentDualClassLinearMap a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalMaximalCotangentClassLinearMap_surjective a ha p hp hpa σ hσ δ hδ P hP).comp
    (arithmeticLocalCotangentDualLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).surjective

/-- The dimension of the actual local continuous cohomology condition is bounded by the dimension of the literal original relative maximal-ideal cotangent quotient. -/
theorem arithmeticLocalClass_finrank_le_cotangent
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     letI : AddCommMonoid (RelativeMaximalCotangent O
       (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)) :=
         (instAddCommGroupRelativeMaximalCotangent O
           (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)).toAddCommMonoid
     letI := originalMaximalCotangentResidueModule (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)
     Module.finrank (IsLocalRing.ResidueField O)
       (arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal) ≤
         Module.finrank (IsLocalRing.ResidueField O)
           (RelativeMaximalCotangent O (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  letI : AddCommMonoid (RelativeMaximalCotangent O
    (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)) :=
      (instAddCommGroupRelativeMaximalCotangent O
        (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)).toAddCommMonoid
  letI : Module.Finite (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) :=
    arithmeticLocalCotangentDual_finite a ha p hp hpa σ hσ δ hδ P hP
  letI := originalMaximalCotangentResidueModule (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)
  have h := LinearMap.finrank_le_finrank_of_surjective
    (arithmeticLocalCotangentDualClassLinearMap_surjective a ha p hp hpa σ hσ δ hδ P hP)
  change Module.finrank (IsLocalRing.ResidueField O)
    (arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal) ≤
      Module.finrank (IsLocalRing.ResidueField O) (OriginalRelativeMaximalCotangentDual (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)) at h
  rw [originalRelativeMaximalCotangentDual_finrank (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)] at h
  exact h

end
end Dubon2026
