import Dubon2026.ArithmeticTraceUnframedUniversality
import Dubon2026.OriginalResidualHopfModel
import Dubon2026.MatrixHopfModelCoefficientQuotientLocalData
import Dubon2026.OriginalUnframedHopfFlatQuotientEquivalence

/-! # The constructed arithmetic trace ring and the original local model quotient

The original restriction homomorphism and a genuine model of the original residual
representation are explicit inputs. The unrestricted universal representation and its
class bijection are consumed from the existing arithmetic trace-ring theorem.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {R F K ι : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι]

section QuotientAux
variable {O B : Type} [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [CommRing B] [Algebra O B] [TopologicalSpace B] [IsTopologicalRing B]

private theorem hopfFlatQuotient_from_constructed_universality
    (T : Subalgebra O B) (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
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
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA H σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val := by
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, hbij⟩ := hwhole
  letI : IsLocalRing T := hlocal
  letI : IsNoetherianRing T := hnoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
  letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
  letI : Finite (IsLocalRing.ResidueField T) := Finite.of_injective eT eT.injective
  letI : T2Space T := originalAdicCompleteLocal_t2Space htop
  letI : CompactSpace T := originalAdicCompleteLocal_compactSpace htop
  let mT := originalResidualHopfModel eT τ.toMonoidHom σ hτ j m
  have hopen : IsOpen (IsLocalRing.maximalIdeal T : Set T) := by
    simpa using (isAdic_iff.mp htop).1 1
  let J := matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
  let hquot := matrixHopfModelCoefficientQuotient_isLocal_of_isAdic htop
    (τ.toMonoidHom.comp j) mT
  letI : IsLocalRing (T ⧸ J) := hquot
  obtain ⟨hqnoeth, hqtop, hqcomplete⟩ := matrixHopfModelCoefficientQuotient_localData htop
    (τ.toMonoidHom.comp j) mT
  refine ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ,
    hquot, hqnoeth, hqtop, hqcomplete, ?_⟩
  intro A _ _ _ _ _ _ hA eA
  letI : Finite (IsLocalRing.ResidueField A) := Finite.of_injective eA eA.injective
  have htarget : IsAdic (IsLocalRing.maximalIdeal A) := by
    rw [← hA]
    rfl
  letI : T2Space A := originalAdicCompleteLocal_t2Space htarget
  refine ⟨originalUnframedHopfFlatQuotientEquiv hA eT eA H σ τ hτ j
    (IsLocalRing.maximalIdeal T) hopen mT (hbij A hA eA), ?_⟩
  intro f
  exact originalUnframedHopfFlatQuotientEquiv_evaluation hA eT eA H σ τ hτ j
    (IsLocalRing.maximalIdeal T) hopen mT (hbij A hA eA) f

end QuotientAux

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Consume the actual arithmetic trace-ring universal representation to construct its
complete local quotient classifying the original all-adic model condition along the specified
restriction. A model of the original residual restriction is the explicit local input. -/
theorem arithmeticUnframedHopfFlatUniversality_exists
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
                originalUnframedHopfFlat R F K eA (rationalArithmeticGaloisGroup a) σ j c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) := by
  refine ⟨ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ, rfl, ?_⟩
  exact hopfFlatQuotient_from_constructed_universality _ (rationalArithmeticGaloisGroup a) σ j m
    (arithmeticTraceUnframedUniversality_exists (L := L) a ha p hp hpa σ hσ i₀)

end
end Dubon2026
