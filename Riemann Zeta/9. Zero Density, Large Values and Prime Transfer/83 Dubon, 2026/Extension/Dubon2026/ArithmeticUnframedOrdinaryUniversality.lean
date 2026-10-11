import Dubon2026.ArithmeticTraceUnframedUniversality
import Dubon2026.ResidualOrdinaryNontrivialElement
import Dubon2026.ResidualOrdinaryRelationQuotient
import Dubon2026.OriginalUnframedOrdinaryQuotientEquivalence
import Dubon2026.RationalArithmeticInertia

/-! # Genuine arithmetic ordinary unframed classification from the constructed original trace ring -/

namespace Dubon2026
noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

section QuotientAux
variable {O B : Type} [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [CommRing B] [Algebra O B] [TopologicalSpace B] [IsTopologicalRing B]

private theorem ordinaryQuotient_from_constructed_universality
    (T : Subalgebra O B) (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (N : Subgroup H)
    (hOrd : Nonempty ((matrixStandardRepresentation (σ.comp N.subtype)).invariants
      ≃ₗ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O) ∧
    ∃ W : Submodule (IsLocalRing.ResidueField O) (Fin 2 → IsLocalRing.ResidueField O),
      IsCompl (matrixStandardRepresentation (σ.comp N.subtype)).invariants W)
    (hwhole : ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup (Fin 2) T)
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
        (τ : H →ₜ* GeneralLinearGroup (Fin 2) T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        ∃ g₀ : N, σ g₀.val ≠ 1 ∧
        let J := matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA H σ // originalUnframedOrdinary eA H σ N c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA H σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val := by
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, hbij⟩ := hwhole
  letI : IsLocalRing T := hlocal
  letI : IsNoetherianRing T := hnoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
  letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
  obtain ⟨g₀, hg₀⟩ := residualOrdinary_exists_nonidentity (σ.comp N.subtype) (Classical.choice hOrd.1)
  have hτN : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
      (τ.toMonoidHom.comp N.subtype) = σ.comp N.subtype := by
    apply MonoidHom.ext
    intro g
    exact DFunLike.congr_fun hτ g.val
  let J := matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀
  let hquot := matrixOrdinaryRelationQuotient_isLocal eT (τ.toMonoidHom.comp N.subtype)
    (σ.comp N.subtype) hτN g₀ hg₀ hOrd
  letI : IsLocalRing (T ⧸ J) := hquot
  obtain ⟨hqnoeth, hqtop, hqcomplete⟩ := matrixOrdinaryRelationQuotient_localData htop eT
    (τ.toMonoidHom.comp N.subtype) (σ.comp N.subtype) hτN g₀ hg₀ hOrd
  refine ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, g₀, hg₀,
    hquot, hqnoeth, hqtop, hqcomplete, ?_⟩
  intro A _ _ _ _ _ _ hA eA
  refine ⟨originalUnframedOrdinaryQuotientEquiv eT eA H σ τ hτ N g₀ hg₀ (hbij A hA eA), ?_⟩
  intro f
  exact originalUnframedOrdinaryQuotientEquiv_evaluation eT eA H σ τ hτ N g₀ hg₀ (hbij A hA eA) f

end QuotientAux

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Genuine residual ordinarity at the original arithmetic inertia group constructs a complete local ordinary quotient of the actual arithmetic trace ring. Its coefficient maps classify exactly the original ordinary unframed classes, with the same universal-matrix evaluation formula. -/
theorem arithmeticUnframedOrdinaryUniversality_exists
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))]
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hOrd : Nonempty ((matrixStandardRepresentation (σ.comp (rationalArithmeticInertia a P.asIdeal).subtype)).invariants
      ≃ₗ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O) ∧
    ∃ W : Submodule (IsLocalRing.ResidueField O) (Fin 2 → IsLocalRing.ResidueField O),
      IsCompl (matrixStandardRepresentation (σ.comp (rationalArithmeticInertia a P.asIdeal).subtype)).invariants W) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : (rationalArithmeticGaloisGroup a) →ₜ* GeneralLinearGroup (Fin 2) T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        ∃ g₀ : rationalArithmeticInertia a P.asIdeal, σ g₀.val ≠ 1 ∧
        let J := matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp (rationalArithmeticInertia a P.asIdeal).subtype) g₀
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ // originalUnframedOrdinary eA (rationalArithmeticGaloisGroup a) σ (rationalArithmeticInertia a P.asIdeal) c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) := by
  refine ⟨ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ, rfl, ?_⟩
  exact ordinaryQuotient_from_constructed_universality _ (rationalArithmeticGaloisGroup a) σ
    (rationalArithmeticInertia a P.asIdeal) hOrd
    (arithmeticTraceUnframedUniversality_exists (L := L) a ha p hp hpa σ hσ (0 : Fin 2))

end
end Dubon2026
