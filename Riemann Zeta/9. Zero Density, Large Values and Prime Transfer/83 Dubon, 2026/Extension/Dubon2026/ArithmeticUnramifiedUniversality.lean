import Dubon2026.ArithmeticUnramifiedDeformationRing

/-! # Classification of original unramified fixed-determinant arithmetic framed lifts -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- The original continuous coefficient fiber of the genuine unramified arithmetic quotient, with its proved true residue field. -/
def ArithmeticUnramifiedCoefficientFiber
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Type :=
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  OriginalContinuousCoefficientFiber
    (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP) eA

/-- Maps from the actual local deformation quotient classify all original continuous framed arithmetic lifts with prescribed determinant and trivial original inertia at the chosen prime. -/
def arithmeticUnramifiedFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     ArithmeticUnramifiedCoefficientFiber eA a ha p hp hpa σ hσ δ hδ P hP ≃
         {f : {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ //
             ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)} //
           rationalArithmeticInertia a P.asIdeal ≤ f.val.val.toMonoidHom.ker}) := by
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  let eR := arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ
  let ρ := (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom
  let I := rationalArithmeticInertia a P.asIdeal
  let J := matrixRepresentationRelationIdeal ρ I
  exact (originalLocalQuotientCoefficientFiberEquiv eR eA J).trans
    ((arithmeticFixedDeterminantFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ).subtypeEquiv
      (fun f => matrixRepresentationRelationIdeal_le_kernel_iff ρ I f.val.toRingHom))

/-- The actual unramified fixed-determinant coefficient classification is bijective on the whole original continuous framed fibers. -/
theorem arithmeticUnramifiedFramedFiberEquiv_bijective
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Bijective (arithmeticUnramifiedFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticUnramifiedFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ P hP).bijective

/-- The original local deformation classification evaluates each genuine universal arithmetic matrix through the literal inertia quotient. -/
theorem arithmeticUnramifiedFramedFiberEquiv_evaluation
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     ∀ (f : ArithmeticUnramifiedCoefficientFiber eA a ha p hp hpa σ hσ δ hδ P hP)
       (g : rationalArithmeticGaloisGroup a),
       (arithmeticUnramifiedFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ P hP f).val.val.val g =
         GeneralLinearGroup.map (n := ι) f.val.toRingHom
           (GeneralLinearGroup.map (n := ι)
             (Ideal.Quotient.mk (matrixRepresentationRelationIdeal
               (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom
               (rationalArithmeticInertia a P.asIdeal)))
             (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ g))) := by
  intro f g
  rfl

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The original unramified fixed-determinant framed classification is natural on every original arithmetic matrix under actual continuous residue-preserving coefficient maps. -/
theorem arithmeticUnramifiedFramedFiberEquiv_natural
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     ∀ (f : ArithmeticUnramifiedCoefficientFiber eA a ha p hp hpa σ hσ δ hδ P hP)
       (g : rationalArithmeticGaloisGroup a),
       (arithmeticUnramifiedFramedFiberEquiv hB eB a ha p hp hpa σ hσ δ hδ P hP
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f)).val.val.val g =
           GeneralLinearGroup.map (n := ι) k.toRingHom
             ((arithmeticUnramifiedFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ P hP f).val.val.val g)) := by
  intro f g
  rfl

end
end Dubon2026
