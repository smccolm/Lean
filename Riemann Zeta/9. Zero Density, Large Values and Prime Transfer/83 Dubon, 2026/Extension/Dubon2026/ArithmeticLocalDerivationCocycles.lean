import Dubon2026.ArithmeticLocalFirstOrderCocycles
import Dubon2026.ArithmeticLocalDerivationLinearity

/-! # Genuine linear classification of local-ring derivations by local first-order cocycles -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Differentiate the same whole original universal representation into its actual trace-zero inertia-vanishing continuous cocycles. -/
def arithmeticLocalResidueDerivationLocalCocycleLinearMap
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP →ₗ[IsLocalRing.ResidueField O]
      arithmeticLocalFirstOrderCocycles a σ P.asIdeal :=
  (arithmeticLocalResidueDerivationCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP).codRestrict _ (by
    intro d
    have hd : arithmeticLocalResidueDerivationCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP d =
        (arithmeticLocalFirstOrderCocycle a σ hσ P.asIdeal hP
          (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d)).val := by
      apply Subtype.ext
      exact arithmeticLocalResidueDerivationCocycleLinearMap_original a ha p hp hpa σ hσ δ hδ P hP d
    rw [hd]
    exact (arithmeticLocalFirstOrderCocycle a σ hσ P.asIdeal hP
      (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d)).property)

/-- The actual local cocycle of the original derivation agrees with the entire original lift-to-cocycle classification. -/
theorem arithmeticLocalResidueDerivationLocalCocycleLinearMap_apply
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d : ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalResidueDerivationLocalCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP d =
      arithmeticLocalFirstOrderCocycleEquiv a σ hσ P.asIdeal hP
        (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d) := by
  apply Subtype.ext
  apply Subtype.ext
  exact arithmeticLocalResidueDerivationCocycleLinearMap_original a ha p hp hpa σ hσ δ hδ P hP d

/-- Genuine relative derivations of the original arithmetic local ring and actual local first-order cocycles are bijective before quotienting by strict conjugacy. -/
theorem arithmeticLocalResidueDerivationLocalCocycleLinearMap_bijective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Bijective (arithmeticLocalResidueDerivationLocalCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP) := by
  let e := (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP).trans
    (arithmeticLocalFirstOrderCocycleEquiv a σ hσ P.asIdeal hP)
  have he : (arithmeticLocalResidueDerivationLocalCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP :
      ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP → arithmeticLocalFirstOrderCocycles a σ P.asIdeal) = e.toFun := by
    funext d
    exact arithmeticLocalResidueDerivationLocalCocycleLinearMap_apply a ha p hp hpa σ hσ δ hδ P hP d
  rw [he]
  exact e.bijective

/-- The actual relative derivations of the literal completed arithmetic local ring are linearly equivalent to the genuine local first-order continuous cocycles. -/
def arithmeticLocalResidueDerivationLocalCocycleLinearEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP ≃ₗ[IsLocalRing.ResidueField O]
      arithmeticLocalFirstOrderCocycles a σ P.asIdeal :=
  LinearEquiv.ofBijective (arithmeticLocalResidueDerivationLocalCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP)
    (arithmeticLocalResidueDerivationLocalCocycleLinearMap_bijective a ha p hp hpa σ hσ δ hδ P hP)

end
end Dubon2026
