import Dubon2026.ArithmeticLocalTangentPoints
import Dubon2026.OriginalRelativeCoefficientFiberEquiv

/-! # Genuine relative derivations of the original arithmetic local deformation ring -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Actual relative residue derivations of the literal original arithmetic local deformation ring, with its genuine original coefficient action. -/
def ArithmeticLocalResidueDerivations
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Type :=
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  OriginalResidueDerivations (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The actual original relative residue derivations classify all genuine residual dual-number points of the original arithmetic local deformation ring. -/
def arithmeticLocalResidueDerivationPointEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP ≃
      ArithmeticLocalTangentPoint a ha p hp hpa σ hσ δ hδ P hP := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  letI : Finite (DualNumber (IsLocalRing.ResidueField O)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O)))
      (DualNumber (IsLocalRing.ResidueField O)) :=
    finiteDualNumber_maximal_isAdicComplete (IsLocalRing.ResidueField O)
  exact originalResidueDerivationContinuousFiberEquiv
    (arithmeticUnramifiedDeformationRing_localData a ha p hp hpa σ hσ δ hδ P hP).2.2
    (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- The genuine relative derivations of the original completed local ring classify all original continuous first-order representations with its prescribed determinant and inertia conditions. -/
def arithmeticLocalResidueDerivationLiftEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP ≃
      ArithmeticLocalFirstOrderLift a σ P.asIdeal :=
  (arithmeticLocalResidueDerivationPointEquiv a ha p hp hpa σ hσ δ hδ P hP).trans
    (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- Each genuine first-order local arithmetic representation corresponds uniquely to an actual relative residue derivation of the original local deformation ring. -/
theorem arithmeticLocalResidueDerivationLiftEquiv_bijective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Bijective (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP).bijective

/-- The actual relative derivation of the original local ring has the class of its same genuine whole first-order local representation. -/
def arithmeticLocalResidueDerivationClass
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d : ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal :=
  arithmeticLocalFirstOrderClass a σ hσ P.asIdeal hP
    (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d)

/-- Every actual continuous local cohomology class comes from a genuine relative residue derivation of the original arithmetic local deformation ring. -/
theorem arithmeticLocalResidueDerivationClass_surjective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalResidueDerivationClass a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalFirstOrderClass_surjective a σ hσ P.asIdeal hP).comp
    (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP).surjective

/-- Equality of actual local classes of original relative derivations is precisely strict conjugacy of their genuine whole lifted arithmetic representations. -/
theorem arithmeticLocalResidueDerivationClass_eq_iff
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d e : ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalResidueDerivationClass a ha p hp hpa σ hσ δ hδ P hP d =
      arithmeticLocalResidueDerivationClass a ha p hp hpa σ hσ δ hδ P hP e ↔
        MatrixFirstOrderStrictlyConjugate σ
          (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d).val.val
          (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP e).val.val :=
  arithmeticLocalFirstOrderClass_eq_iff a σ hσ P.asIdeal hP _ _

end
end Dubon2026
