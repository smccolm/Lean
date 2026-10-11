import Dubon2026.ArithmeticUnframedHopfFlatUniversality
import Dubon2026.OriginalUnframedFiniteFlatSchemeCondition

/-! # The arithmetic trace quotient classifies the original geometric finite-flat condition

Consume the actual previously constructed arithmetic trace quotient and the proved
scheme/Hopf model equivalence. The original restriction map and residual model are
explicit inputs; no existence of a modular arithmetic representation is asserted.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {R F K ι : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι]



section GeometricAux
variable {O B : Type} [CommRing O] [IsLocalRing O]
  [CommRing B] [Algebra O B] [TopologicalSpace B] [IsTopologicalRing B]

omit [PerfectField F] [IsFractionRing R F] [Normal F K] [IsAlgClosed K] in
private theorem finiteFlatSchemeQuotient_from_hopfClassification
    (T : Subalgebra O B) (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H)
    (hwhole : letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA H σ //
                originalUnframedHopfFlat R F K eA H σ j c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                H σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) :
    letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA H σ //
                originalUnframedFiniteFlatScheme R F K eA H σ j c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                H σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val := by
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ,
    hquot, hqnoeth, hqtop, hqcomplete, hclass⟩ := hwhole
  letI : IsLocalRing T := hlocal
  letI : IsNoetherianRing T := hnoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
  let J := matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
  letI : IsLocalRing (T ⧸ J) := hquot
  refine ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ,
    hquot, hqnoeth, hqtop, hqcomplete, ?_⟩
  intro A _ _ _ _ _ _ hA eA
  obtain ⟨e, he⟩ := hclass A hA eA
  let eclass := (Equiv.refl
    (OriginalUnframedDeformationClass eA H σ)).subtypeEquiv
      (fun c => originalUnframedHopfFlat_iff_finiteFlatScheme (R := R) eA
        H σ j c)
  refine ⟨e.trans eclass, ?_⟩
  intro f
  exact he f
end GeometricAux

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Consume the actual arithmetic trace-ring universal representation to construct its
complete local quotient classifying the original all-adic model condition along the specified
restriction. A model of the original residual restriction is the explicit local input. -/
theorem arithmeticUnframedFiniteFlatSchemeUniversality_exists
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (j : (K ≃ₐ[F] K) →* rationalArithmeticGaloisGroup a)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ //
                originalUnframedFiniteFlatScheme R F K eA (rationalArithmeticGaloisGroup a) σ j c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) := by
  exact Exists.imp (fun T => And.imp_right
    (finiteFlatSchemeQuotient_from_hopfClassification (R := R) T
      (rationalArithmeticGaloisGroup a) σ j))
    (arithmeticUnframedHopfFlatUniversality_exists (L := L) a ha p hp hpa σ hσ i₀ j m)

end
end Dubon2026
