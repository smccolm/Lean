import Dubon2026.OriginalUnframedDeterminantFiniteFlatQuotientEquivalence
import Dubon2026.OriginalCotangentCohomologyClass
import Dubon2026.OriginalCoefficientQuotientRepresentation
import Dubon2026.FiniteNilpotentAdicCoefficients
import Dubon2026.ResidualDeterminantHopfFlatQuotient

/-! # The genuine determinant and geometric finite-flat cotangent image in continuous cohomology -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R F K ι O A : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-- The actual sum quotient's cotangent class map is injective, and its linear image
is exactly the continuous cohomology classes of original dual-number deformations
with prescribed determinant and actual geometric finite-flat models at every positive
adic level. This proves a geometric description of the genuine linear range; closure
of a separately specified local cohomology condition is not assumed. -/
private theorem originalDeterminantFiniteFlatCotangent_classification
    [CompactSpace A]
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ (τ.toMonoidHom.comp j))))
    (δ : H →* Oˣ)
    [IsLocalRing (A ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔
      matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)))]
    (hQ : IsAdic (IsLocalRing.maximalIdeal
      (A ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)))))
    (hbij : letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
        ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
      Function.Bijective (originalCoefficientRepresentationClass eA
        (relativeDualNumberResidueEquiv O) H σ τ hτ)) :
    let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
      matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
    let eQ := originalLocalQuotientResidueEquiv eA J
    let τQ := originalCoefficientQuotientRepresentation H τ J
    let hτQ := originalCoefficientQuotientRepresentation_residue eA H σ τ hτ J
    let LQ := originalCotangentCohomologyClassLinearMap hQ eQ H σ hσ τQ hτQ
    Function.Injective LQ ∧ ∀ x : ContinuousMatrixAdjointH1 σ hσ,
      x ∈ LinearMap.range LQ ↔
        (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
           ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
         ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H σ,
           (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) H σ δ c ∧
             originalUnframedFiniteFlatScheme R F K (relativeDualNumberResidueEquiv O) H σ j c) ∧
           relativeDualNumberUnframedCohomologyMap H σ hσ c = x) := by
  let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
    matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
  let eQ := originalLocalQuotientResidueEquiv eA J
  let τQ := originalCoefficientQuotientRepresentation H τ J
  let hτQ := originalCoefficientQuotientRepresentation_residue eA H σ τ hτ J
  let LQ := originalCotangentCohomologyClassLinearMap hQ eQ H σ hσ τQ hτQ
  letI : Finite (DualNumber (IsLocalRing.ResidueField O)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O)))
      (DualNumber (IsLocalRing.ResidueField O)) :=
    finiteDualNumber_maximal_isAdicComplete (IsLocalRing.ResidueField O)
  letI : TopologicalSpace (DualNumber (IsLocalRing.ResidueField O)) :=
    (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))).adicTopology
  letI : T2Space (DualNumber (IsLocalRing.ResidueField O)) :=
    originalAdicCompleteLocal_t2Space (show IsAdic
      (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))) from rfl)
  let e := originalUnframedDeterminantFiniteFlatQuotientEquiv rfl eA
    (relativeDualNumberResidueEquiv O) H σ τ hτ j I₀ hI₀ m₀ δ hbij
  let ecot := originalResidueCotangentContinuousFiberEquiv hQ eQ
  have heval (d : OriginalResidueCotangentMaps eQ) :
      LQ d = relativeDualNumberUnframedCohomologyMap H σ hσ (e (ecot d)).val := by
    calc
      _ = relativeDualNumberUnframedCohomologyMap H σ hσ
          (originalCoefficientRepresentationClass eQ (relativeDualNumberResidueEquiv O)
            H σ τQ hτQ (ecot d)) :=
        originalCotangentCohomologyClassLinearMap_coefficient hQ eQ H σ hσ τQ hτQ d
      _ = relativeDualNumberUnframedCohomologyMap H σ hσ
          (originalCoefficientRepresentationClass eA (relativeDualNumberResidueEquiv O)
            H σ τ hτ (originalQuotientCoefficientRestriction eA
              (relativeDualNumberResidueEquiv O) J (ecot d)).val) :=
        congrArg (relativeDualNumberUnframedCohomologyMap H σ hσ)
          (originalCoefficientQuotientRepresentation_class eA
            (relativeDualNumberResidueEquiv O) H σ τ hτ J (ecot d))
      _ = _ := (congrArg (relativeDualNumberUnframedCohomologyMap H σ hσ)
        (originalUnframedDeterminantFiniteFlatQuotientEquiv_evaluation rfl eA
          (relativeDualNumberResidueEquiv O) H σ τ hτ j I₀ hI₀ m₀ δ hbij (ecot d))).symm
  constructor
  · intro d f h
    apply ecot.injective
    apply e.injective
    apply Subtype.ext
    apply (relativeDualNumberUnframedCohomologyMap_bijective H σ hσ).1
    exact (heval d).symm.trans (h.trans (heval f))
  · intro x
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨(e (ecot d)).val, (e (ecot d)).property, (heval d).symm.trans hd⟩
    · rintro ⟨c, hc, hx⟩
      obtain ⟨f, hf⟩ := e.surjective ⟨c, hc⟩
      obtain ⟨d, hd⟩ := ecot.surjective f
      refine ⟨d, ?_⟩
      rw [heval, hd, hf]
      exact hx

/-- Full original coefficient-class universality, residual determinant compatibility,
and an actual residual local model construct the genuine local sum quotient and
identify its cotangent image with the geometric deformation condition. In particular,
neither a restricted tangent-space bijection nor closure of that condition is assumed. -/
theorem originalResidualDeterminantFiniteFlatCotangent_classification
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j)))
    (hwhole : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
      (_hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
      (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O),
      Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ)) :
    let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
      matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
    ∃ hquot : IsLocalRing (A ⧸ J),
      letI := hquot
      IsNoetherianRing (A ⧸ J) ∧ ∃ hQ : IsAdic (IsLocalRing.maximalIdeal (A ⧸ J)),
        IsAdicComplete (IsLocalRing.maximalIdeal (A ⧸ J)) (A ⧸ J) ∧
        (let eQ := originalLocalQuotientResidueEquiv eA J
         let τQ := originalCoefficientQuotientRepresentation H τ J
         let hτQ := originalCoefficientQuotientRepresentation_residue eA H σ τ hτ J
         let LQ := originalCotangentCohomologyClassLinearMap hQ eQ H σ hσ τQ hτQ
         Function.Injective LQ ∧ ∀ x : ContinuousMatrixAdjointH1 σ hσ,
           x ∈ LinearMap.range LQ ↔
             (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
                ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
              ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H σ,
                (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) H σ δ c ∧
                  originalUnframedFiniteFlatScheme R F K
                    (relativeDualNumberResidueEquiv O) H σ j c) ∧
                relativeDualNumberUnframedCohomologyMap H σ hσ c = x)) := by
  letI : Finite (IsLocalRing.ResidueField A) := Finite.of_injective eA eA.injective
  letI : CompactSpace A := originalAdicCompleteLocal_compactSpace hA
  letI := representationDeterminantHopfFlatQuotient_isLocal
    hA eA τ.toMonoidHom σ hτ δ hδ j m
  obtain ⟨hnoeth, hQ, hcomplete⟩ := representationDeterminantHopfFlatQuotient_localData
    hA eA τ.toMonoidHom σ hτ δ hδ j m
  refine ⟨inferInstance, hnoeth, hQ, hcomplete, ?_⟩
  letI : Finite (DualNumber (IsLocalRing.ResidueField O)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O)))
      (DualNumber (IsLocalRing.ResidueField O)) :=
    finiteDualNumber_maximal_isAdicComplete (IsLocalRing.ResidueField O)
  have hopen : IsOpen (IsLocalRing.maximalIdeal A : Set A) := by
    simpa using (isAdic_iff.mp hA).1 1
  exact originalDeterminantFiniteFlatCotangent_classification eA H σ hσ τ hτ j
    (IsLocalRing.maximalIdeal A) hopen (originalResidualHopfModel eA τ.toMonoidHom σ hτ j m)
    δ hQ (hwhole (DualNumber (IsLocalRing.ResidueField O)) rfl (relativeDualNumberResidueEquiv O))

end
end Dubon2026
