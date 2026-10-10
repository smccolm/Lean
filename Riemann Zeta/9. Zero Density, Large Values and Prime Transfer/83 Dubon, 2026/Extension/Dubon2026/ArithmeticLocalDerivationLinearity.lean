import Dubon2026.ArithmeticLocalResidueDerivations
import Dubon2026.OriginalResidueDerivationContinuousCocycles
import Dubon2026.ArithmeticUnramifiedRepresentation

/-! # Original residue-field linearity for the actual arithmetic local-ring derivations -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The genuine original arithmetic local-ring derivations inherit their actual additive group from relative derivations. -/
instance arithmeticLocalResidueDerivationsAddCommGroup
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : AddCommGroup (ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact inferInstanceAs (AddCommGroup (OriginalResidueDerivations (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)))

/-- The original residue field acts on genuine relative derivations of the actual arithmetic local ring through the actual epsilon coefficient ideal. -/
instance arithmeticLocalResidueDerivationsModule
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Module (IsLocalRing.ResidueField O)
      (ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact originalResidueDerivationsModule (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)

/-- Differentiate the actual whole universal unramified arithmetic representation by each genuine relative derivation of its original coefficient ring. The resulting genuine continuous cocycle map is linear over the original residue field. -/
def arithmeticLocalResidueDerivationCocycleLinearMap
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP →ₗ[IsLocalRing.ResidueField O]
      continuousMatrixAdjointCocycles σ := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact originalResidueDerivationContinuousCocycleLinearMap
    (arithmeticUnramifiedDeformationRing_localData a ha p hp hpa σ hσ δ hδ P hP).2.2
    (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)
    (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P).toMonoidHom
    (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P).continuous σ hσ
    (arithmeticUnramifiedRepresentation_residue a ha p hp hpa σ hσ δ hδ P hP)

/-- The original universal-ring point classification and differentiation of the same actual universal representation give exactly the same whole first-order lift. -/
theorem arithmeticLocalResidueDerivationLiftEquiv_original
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d : ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d).val.val =
       originalResidueDerivationFirstOrderLift
         (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)
         (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P).toMonoidHom σ
         (arithmeticUnramifiedRepresentation_residue a ha p hp hpa σ hσ δ hδ P hP) d) := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  apply Subtype.ext
  apply MonoidHom.ext
  intro g
  rfl

/-- The actual linear cocycle of the original arithmetic local-ring derivation is the original cocycle of its same local first-order lift. -/
theorem arithmeticLocalResidueDerivationCocycleLinearMap_original
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (d : ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP) :
    (arithmeticLocalResidueDerivationCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP d).val =
      matrixFirstOrderCocycle σ (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d).val.val := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  rw [arithmeticLocalResidueDerivationLiftEquiv_original]
  rfl

/-- The actual class map of original local-ring relative derivations is linear over the original residue field. -/
def arithmeticLocalResidueDerivationClassLinearMap
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalResidueDerivations a ha p hp hpa σ hσ δ hδ P hP →ₗ[IsLocalRing.ResidueField O]
      arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal where
  toFun := arithmeticLocalResidueDerivationClass a ha p hp hpa σ hσ δ hδ P hP
  map_add' d e := by
    apply Subtype.ext
    change (Submodule.Quotient.mk ⟨_, _⟩ : ContinuousMatrixAdjointH1 σ hσ) =
      Submodule.Quotient.mk ⟨_, _⟩ + Submodule.Quotient.mk ⟨_, _⟩
    rw [← Submodule.Quotient.mk_add]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change matrixFirstOrderCocycle σ (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP (d + e)).val.val =
      matrixFirstOrderCocycle σ (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d).val.val +
        matrixFirstOrderCocycle σ (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP e).val.val
    rw [← arithmeticLocalResidueDerivationCocycleLinearMap_original,
      ← arithmeticLocalResidueDerivationCocycleLinearMap_original,
      ← arithmeticLocalResidueDerivationCocycleLinearMap_original]
    exact congrArg Subtype.val (map_add (arithmeticLocalResidueDerivationCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP) d e)
  map_smul' r d := by
    apply Subtype.ext
    change (Submodule.Quotient.mk ⟨_, _⟩ : ContinuousMatrixAdjointH1 σ hσ) =
      r • Submodule.Quotient.mk ⟨_, _⟩
    rw [← Submodule.Quotient.mk_smul]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change matrixFirstOrderCocycle σ (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP (r • d)).val.val =
      r • matrixFirstOrderCocycle σ (arithmeticLocalResidueDerivationLiftEquiv a ha p hp hpa σ hσ δ hδ P hP d).val.val
    rw [← arithmeticLocalResidueDerivationCocycleLinearMap_original,
      ← arithmeticLocalResidueDerivationCocycleLinearMap_original]
    exact congrArg Subtype.val (map_smul (arithmeticLocalResidueDerivationCocycleLinearMap a ha p hp hpa σ hσ δ hδ P hP) r d)

/-- The actual residue-field-linear local class map of original relative derivations is surjective. -/
theorem arithmeticLocalResidueDerivationClassLinearMap_surjective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalResidueDerivationClassLinearMap a ha p hp hpa σ hσ δ hδ P hP) :=
  arithmeticLocalResidueDerivationClass_surjective a ha p hp hpa σ hσ δ hδ P hP

end
end Dubon2026
