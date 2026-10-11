import Dubon2026.ArithmeticTraceUnframedUniversality
import Dubon2026.OriginalCotangentCohomologyClassification

/-! # Actual arithmetic trace-ring cotangent classification in continuous adjoint cohomology -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]

section CotangentAux
variable {O B : Type} [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing B] [Algebra O B] [TopologicalSpace B] [IsTopologicalRing B]

omit [IsTopologicalRing B] in
private theorem traceCotangent_from_original_universality
    (T : Subalgebra O B) (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
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
      IsNoetherianRing T ∧ ∃ htop : IsAdic (IsLocalRing.maximalIdeal T),
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        Function.Bijective (originalCotangentCohomologyClassLinearMap htop eT H σ hσ τ hτ) := by
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, hbij⟩ := hwhole
  letI : IsLocalRing T := hlocal
  exact ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ,
    originalCotangentCohomologyClassLinearMap_bijective htop eT H σ hσ τ hτ hbij⟩

end CotangentAux

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Consume the constructed original arithmetic trace universality to identify its
actual residue-field-linear cotangent class map bijectively with genuine continuous
adjoint first cohomology. Original residual continuity and absolute irreducibility are
the arithmetic inputs; no coefficient-class or cotangent bijection is assumed. -/
theorem arithmeticTraceCotangentCohomology_exists
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
       ∃ hlocal : IsLocalRing T,
         letI := hlocal
         IsNoetherianRing T ∧ ∃ htop : IsAdic (IsLocalRing.maximalIdeal T),
         IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
         ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
           (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
           (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
             τ.toMonoidHom = σ),
           Function.Bijective (originalCotangentCohomologyClassLinearMap htop eT
             (rationalArithmeticGaloisGroup a) σ hσ τ hτ)) := by
  refine ⟨ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ, rfl, ?_⟩
  exact traceCotangent_from_original_universality _ (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticTraceUnframedUniversality_exists (L := L) a ha p hp hpa σ hσ i₀)

end
end Dubon2026
