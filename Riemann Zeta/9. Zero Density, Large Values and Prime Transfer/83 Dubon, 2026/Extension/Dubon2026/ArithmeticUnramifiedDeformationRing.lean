import Dubon2026.ArithmeticFixedDeterminantCompactness
import Dubon2026.ResidualRelationQuotient
import Dubon2026.RationalArithmeticInertia

/-! # Actual fixed-determinant arithmetic coefficients imposing unramifiedness at a prime -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The literal quotient of the original fixed-determinant arithmetic ring by every original inertia matrix relation at the chosen genuine arithmetic prime. -/
abbrev ArithmeticUnramifiedDeformationRing
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a))) :=
  ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ ⧸
    matrixRepresentationRelationIdeal
      (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom
      (rationalArithmeticInertia a P.asIdeal)

/-- Actual residual unramifiedness at the original prime and original determinant compatibility make the literal arithmetic local deformation quotient a genuine local ring. -/
theorem arithmeticUnramifiedDeformationRing_isLocal
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    IsLocalRing (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P) := by
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  exact matrixRepresentationRelationQuotient_isLocal
    (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ)
    (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom σ
    (arithmeticFixedDeterminantRepresentation_residue a ha p hp hpa σ hσ δ hδ)
    (rationalArithmeticInertia a P.asIdeal) hP

/-- The original unramified local deformation quotient has the true original coefficient residue field. -/
def arithmeticUnramifiedDeformationResidueEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     IsLocalRing.ResidueField (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P) ≃ₐ[O]
       IsLocalRing.ResidueField O) := by
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  exact originalLocalQuotientResidueEquiv
    (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ)
    (matrixRepresentationRelationIdeal
      (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom
      (rationalArithmeticInertia a P.asIdeal))

/-- The genuine unramified fixed-determinant arithmetic deformation quotient is Noetherian, maximal-adically complete and retains its original maximal-adic quotient topology. -/
theorem arithmeticUnramifiedDeformationRing_localData
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     IsNoetherianRing (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P) ∧
       IsAdicComplete
         (IsLocalRing.maximalIdeal (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))
         (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P) ∧
       (inferInstance : TopologicalSpace (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)) =
         (IsLocalRing.maximalIdeal (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)).adicTopology) := by
  let R := ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  have hR := arithmeticFixedDeterminantRing_localData a ha p hp hpa σ hσ δ hδ
  letI : IsNoetherianRing R := hR.1
  letI : CompactSpace R := arithmeticFixedDeterminantRing_compactSpace a ha p hp hpa σ hσ δ
  letI : T2Space R := arithmeticFixedDeterminantRing_t2Space a ha p hp hpa σ hσ δ
  let J := matrixRepresentationRelationIdeal
    (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom
    (rationalArithmeticInertia a P.asIdeal)
  refine ⟨isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, ?_, ?_⟩
  · exact compactLocalAdicQuotient_maximal_complete J hR.2.2
  · exact localQuotient_maximal_adicTopology J hR.2.2

end
end Dubon2026
