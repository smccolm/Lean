import Dubon2026.ArithmeticTraceUnframedUniversality
import Dubon2026.ResidualDeterminantSubgroupQuotient
import Dubon2026.OriginalUnframedConditionQuotientEquivalence
import Dubon2026.RationalArithmeticInertia

/-! # Actual arithmetic unframed determinant and inertia quotient classification -/

namespace Dubon2026
noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

section QuotientAux
variable {ι O B : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [CommRing B] [Algebra O B] [TopologicalSpace B] [IsTopologicalRing B]

private theorem conditionQuotient_of_whole_classification
    (T : Subalgebra O B) [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (htop : IsAdic (IsLocalRing.maximalIdeal T))
    (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι T)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (N : Subgroup H) (hN : N ≤ σ.ker)
    (hbij : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
      (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
      Function.Bijective (originalCoefficientRepresentationClass eT eA H σ τ hτ)) :
    letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
      matrixRepresentationRelationIdeal τ.toMonoidHom N
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
            originalUnframedHasDeterminant eA H σ δ c ∧ originalUnframedKillsSubgroup eA H σ N c},
          ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA H σ τ hτ
            (originalQuotientCoefficientRestriction eT eA J f).val := by
  letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
  let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
    matrixRepresentationRelationIdeal τ.toMonoidHom N
  let hquot := representationDeterminantSubgroupQuotient_isLocal eT τ.toMonoidHom σ hτ δ hδ N hN
  letI : IsLocalRing (T ⧸ J) := hquot
  obtain ⟨hqnoeth, hqtop, hqcomplete⟩ :=
    representationDeterminantSubgroupQuotient_localData htop eT τ.toMonoidHom σ hτ δ hδ N hN
  refine ⟨hquot, hqnoeth, hqtop, hqcomplete, ?_⟩
  intro A _ _ _ _ _ _ hA eA
  refine ⟨originalUnframedConditionQuotientEquiv eT eA H σ τ hτ δ N (hbij A hA eA), ?_⟩
  intro f
  exact originalUnframedConditionQuotientEquiv_evaluation eT eA H σ τ hτ δ N (hbij A hA eA) f

private theorem conditionQuotient_from_constructed_universality
    (T : Subalgebra O B)
    (H : ProfiniteGrp.{0}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : H →* Oˣ) (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (N : Subgroup H) (hN : N ≤ σ.ker)
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
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
          matrixRepresentationRelationIdeal τ.toMonoidHom N
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
                originalUnframedHasDeterminant eA _ σ δ c ∧
                originalUnframedKillsSubgroup eA _ σ N c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA _ σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val := by
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, hbij⟩ := hwhole
  letI : IsLocalRing T := hlocal
  letI : IsNoetherianRing T := hnoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
  refine ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, ?_⟩
  exact conditionQuotient_of_whole_classification T htop eT H σ τ hτ δ hδ N hN hbij

end QuotientAux

variable {ι O L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- The actual arithmetic trace ring has a complete local quotient classifying original unframed lifts with the specified determinant and trivial original inertia at the given arithmetic prime. The whole universal classification and all quotient ring properties are derived from the original arithmetic residual representation. -/
theorem arithmeticUnframedInertiaUniversality_exists
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
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
        let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
          matrixRepresentationRelationIdeal τ.toMonoidHom (rationalArithmeticInertia a P.asIdeal)
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
                originalUnframedHasDeterminant eA _ σ δ c ∧
                originalUnframedKillsSubgroup eA _ σ (rationalArithmeticInertia a P.asIdeal) c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA _ σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) := by
  refine ⟨ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ, rfl, ?_⟩
  exact conditionQuotient_from_constructed_universality _ (rationalArithmeticGaloisGroup a)
    σ δ hδ (rationalArithmeticInertia a P.asIdeal) hP
    (arithmeticTraceUnframedUniversality_exists (L := L) a ha p hp hpa σ hσ i₀)

end
end Dubon2026
