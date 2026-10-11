import Dubon2026.ArithmeticTraceUnframedUniversality
import Dubon2026.OriginalDeterminantFiniteFlatCotangentImage

/-! # The genuine geometric local condition in the actual arithmetic trace cotangent image -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {R F K : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

section CotangentAux
variable {O B : Type} [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing B] [Algebra O B] [TopologicalSpace B] [IsTopologicalRing B]

private theorem traceFiniteFlatCotangent_from_original_universality
    (T : Subalgebra O B) (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j)))
    (hwhole : ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
          [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
          (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
          Function.Bijective (originalCoefficientRepresentationClass eT eA H σ τ hτ)) :
    letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ ∃ _htop : IsAdic (IsLocalRing.maximalIdeal T),
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        (let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
           matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
         ∃ hquot : IsLocalRing (T ⧸ J),
           letI := hquot
           IsNoetherianRing (T ⧸ J) ∧ ∃ hQ : IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)),
             IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
             (let eQ := originalLocalQuotientResidueEquiv eT J
              let τQ := originalCoefficientQuotientRepresentation H τ J
              let hτQ := originalCoefficientQuotientRepresentation_residue eT H σ τ hτ J
              let LQ := originalCotangentCohomologyClassLinearMap hQ eQ H σ hσ τQ hτQ
              Function.Injective LQ ∧ ∀ x : ContinuousMatrixAdjointH1 σ hσ,
                x ∈ LinearMap.range LQ ↔
                  (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
                     ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
                   ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H σ,
                     (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) H σ δ c ∧
                       originalUnframedFiniteFlatScheme R F K
                         (relativeDualNumberResidueEquiv O) H σ j c) ∧
                     relativeDualNumberUnframedCohomologyMap H σ hσ c = x))) := by
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, hbij⟩ := hwhole
  letI : IsLocalRing T := hlocal
  letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
  letI : IsNoetherianRing T := hnoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
  refine ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, ?_⟩
  exact originalResidualDeterminantFiniteFlatCotangent_classification
    htop eT H σ hσ τ hτ δ hδ j m hbij

end CotangentAux

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Consume the constructed arithmetic trace universality and an actual residual local
model to construct the determinant/finite-flat quotient and identify its cotangent
image in genuine continuous adjoint cohomology. No class bijection, tangent image,
or local cohomology-subspace closure is an input. -/
theorem arithmeticDeterminantFiniteFlatCotangent_exists
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* rationalArithmeticGaloisGroup a)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j)))
    :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
       ∃ hlocal : IsLocalRing T,
         letI := hlocal
         IsNoetherianRing T ∧ ∃ _htop : IsAdic (IsLocalRing.maximalIdeal T),
         IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
         ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
           (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
           (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
             τ.toMonoidHom = σ),
           (let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
              matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
            ∃ hquot : IsLocalRing (T ⧸ J),
              letI := hquot
              IsNoetherianRing (T ⧸ J) ∧ ∃ hQ : IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)),
                IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
                (let eQ := originalLocalQuotientResidueEquiv eT J
                 let τQ := originalCoefficientQuotientRepresentation (rationalArithmeticGaloisGroup a) τ J
                 let hτQ := originalCoefficientQuotientRepresentation_residue eT (rationalArithmeticGaloisGroup a) σ τ hτ J
                 let LQ := originalCotangentCohomologyClassLinearMap hQ eQ (rationalArithmeticGaloisGroup a) σ hσ τQ hτQ
                 Function.Injective LQ ∧ ∀ x : ContinuousMatrixAdjointH1 σ hσ,
                   x ∈ LinearMap.range LQ ↔
                     (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
                        ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
                      ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ,
                        (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ δ c ∧
                          originalUnframedFiniteFlatScheme R F K
                            (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ j c) ∧
                        relativeDualNumberUnframedCohomologyMap (rationalArithmeticGaloisGroup a) σ hσ c = x)))) := by
  refine ⟨ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ, rfl, ?_⟩
  exact traceFiniteFlatCotangent_from_original_universality _ (rationalArithmeticGaloisGroup a) σ hσ δ hδ j m
    (arithmeticTraceUnframedUniversality_exists (L := L) a ha p hp hpa σ hσ i₀)

end
end Dubon2026
