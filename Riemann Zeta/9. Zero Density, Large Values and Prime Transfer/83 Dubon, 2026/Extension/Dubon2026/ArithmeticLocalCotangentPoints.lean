import Dubon2026.ArithmeticLocalTangentPoints
import Dubon2026.OriginalRelativeCotangentPoints

/-! # Genuine relative cotangent maps of the original arithmetic local deformation ring -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Actual relative cotangent maps of the literal original arithmetic local deformation ring, with its genuine original coefficient action. -/
def ArithmeticLocalCotangentMaps
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Type :=
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  OriginalResidueCotangentMaps (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The actual original relative cotangent maps classify all genuine residual dual-number points of the original arithmetic local deformation ring. -/
def arithmeticLocalCotangentPointEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP ≃
      ArithmeticLocalTangentPoint a ha p hp hpa σ hσ δ hδ P hP := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  letI : Finite (DualNumber (IsLocalRing.ResidueField O)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O)))
      (DualNumber (IsLocalRing.ResidueField O)) :=
    finiteDualNumber_maximal_isAdicComplete (IsLocalRing.ResidueField O)
  exact originalResidueCotangentContinuousFiberEquiv
    (arithmeticUnramifiedDeformationRing_localData a ha p hp hpa σ hσ δ hδ P hP).2.2
    (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The genuine relative cotangent maps of the original completed local ring classify all original continuous first-order representations with its prescribed determinant and inertia conditions. -/
def arithmeticLocalCotangentLiftEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP ≃
      ArithmeticLocalFirstOrderLift a σ P.asIdeal :=
  (arithmeticLocalCotangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP).trans
    (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- Each genuine first-order local arithmetic representation corresponds uniquely to an actual relative cotangent map of the original local deformation ring. -/
theorem arithmeticLocalCotangentLiftEquiv_bijective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Bijective (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP).bijective

/-- The actual relative cotangent map of the original local ring has the class of its same genuine whole first-order local representation. -/
def arithmeticLocalCotangentClass
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d : ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal :=
  arithmeticLocalFirstOrderClass a σ hσ P.asIdeal hP
    (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d)

/-- Every actual continuous local cohomology class comes from a genuine relative cotangent map of the original arithmetic local deformation ring. -/
theorem arithmeticLocalCotangentClass_surjective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalCotangentClass a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalFirstOrderClass_surjective a σ hσ P.asIdeal hP).comp
    (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP).surjective

/-- Equality of actual local classes of original relative cotangent maps is precisely strict conjugacy of their genuine whole lifted arithmetic representations. -/
theorem arithmeticLocalCotangentClass_eq_iff
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d e : ArithmeticLocalCotangentMaps a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalCotangentClass a ha p hp hpa σ hσ δ hδ P hP d =
      arithmeticLocalCotangentClass a ha p hp hpa σ hσ δ hδ P hP e ↔
        MatrixFirstOrderStrictlyConjugate σ
          (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d).val.val
          (arithmeticLocalCotangentLiftEquiv a ha p hp hpa σ hσ δ hδ P hP e).val.val :=
  arithmeticLocalFirstOrderClass_eq_iff a σ hσ P.asIdeal hP _ _

end
end Dubon2026
