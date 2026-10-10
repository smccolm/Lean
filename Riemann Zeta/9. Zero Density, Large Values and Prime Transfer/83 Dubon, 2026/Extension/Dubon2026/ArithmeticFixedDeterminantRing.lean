import Dubon2026.ArithmeticFramedUniversality
import Dubon2026.OriginalPresentedCoefficientCompactness
import Dubon2026.ResidualDeterminantQuotient
import Dubon2026.LocalQuotientCoefficientFibers

/-! # The actual arithmetic framed ring with prescribed determinant -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Impose every original prescribed-determinant equation in the actual arithmetic universal ring. -/
abbrev ArithmeticFixedDeterminantRing
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ) :=
  ArithmeticFramedUniversalRing a ha p hp hpa σ hσ ⧸
    representationDeterminantIdeal
      (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom δ

/-- Original residual determinant compatibility makes the genuine arithmetic fixed-determinant ring local. -/
theorem arithmeticFixedDeterminantRing_isLocal
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    IsLocalRing (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) := by
  letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
  exact representationDeterminantQuotient_isLocal
    (arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ)
    (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom σ
    (arithmeticFramedUniversalRepresentation_residue a ha p hp hpa σ hσ) δ hδ

/-- The actual fixed-determinant ring has the original specified arithmetic coefficient residue field. -/
def arithmeticFixedDeterminantResidueEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     IsLocalRing.ResidueField (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) ≃ₐ[O]
       IsLocalRing.ResidueField O) := by
  letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  exact originalLocalQuotientResidueEquiv
    (arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ)
    (representationDeterminantIdeal
      (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom δ)

/-- The actual arithmetic fixed-determinant ring is Noetherian, complete and endowed with its original maximal-adic topology. -/
theorem arithmeticFixedDeterminantRing_localData
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     IsNoetherianRing (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ))
         (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) ∧
       (inferInstance : TopologicalSpace (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ)) =
         (IsLocalRing.maximalIdeal (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ)).adicTopology) := by
  let R := ArithmeticFramedUniversalRing a ha p hp hpa σ hσ
  letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  have hR := arithmeticFramedUniversalRing_localData a ha p hp hpa σ hσ
  letI : IsNoetherianRing R := hR.1
  let H := originalResidualProfiniteGroup p (rationalArithmeticGaloisGroup a) σ hσ
  let q := profiniteGeneratorPresentation H (arithmeticResidualGenerators a ha p hp hpa σ hσ)
  let τ := fixedResidualOriginalRepresentation p (rationalArithmeticGaloisGroup a) σ hσ
  letI : CompactSpace R := originalPresentedCoefficientRing_compactSpace H q τ
  letI : T2Space R := originalPresentedCoefficientRing_t2Space H q τ
  let J := representationDeterminantIdeal
    (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom δ
  refine ⟨isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, ?_, ?_⟩
  · exact compactLocalAdicQuotient_maximal_complete J hR.2.2
  · exact localQuotient_maximal_adicTopology J hR.2.2

end
end Dubon2026
