import Dubon2026.OriginalGeometricFiniteFlatCohomologySubmodule
import Dubon2026.ArithmeticTraceUnframedUniversality
import Dubon2026.ArithmeticContinuousAdjointFinite
import Dubon2026.RationalPrimeArithmeticRestriction

/-! # The actual prime-local geometric finite-flat cohomology submodule is finite dimensional -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

section CotangentAux
variable {R F K : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O B : Type} [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing B] [Algebra O B] [TopologicalSpace B] [IsTopologicalRing B]

private theorem traceGeometricCohomology_from_original_universality
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
    ∃! S : Submodule (IsLocalRing.ResidueField O) (ContinuousMatrixAdjointH1 σ hσ),
      ∀ x, x ∈ S ↔ x ∈ originalGeometricFiniteFlatCohomologyCondition
        (R := R) H σ hσ δ j := by
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτ, hbij⟩ := hwhole
  letI : IsLocalRing T := hlocal
  letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
  letI : IsNoetherianRing T := hnoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
  exact originalGeometricFiniteFlatCohomologySubmodule_existsUnique
    htop eT H σ hσ τ hτ δ hδ j m hbij

end CotangentAux

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- The existing arithmetic trace universality and an actual residual prime-local model
prove that the intrinsic geometric condition is the membership predicate of a unique
finite-dimensional continuous adjoint cohomology submodule. Its linear closure and
finiteness are derived, while no numerical dimension formula is asserted. -/
theorem arithmeticPrimeGeometricFiniteFlatCohomology_existsUnique
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))
    :
    ∃! S : Submodule (IsLocalRing.ResidueField O) (ContinuousMatrixAdjointH1 σ hσ),
      (∀ x, x ∈ S ↔ x ∈ originalGeometricFiniteFlatCohomologyCondition
        (R := rationalPrimeLocalIntegerRing p hp) (rationalArithmeticGaloisGroup a) σ hσ δ
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom) ∧
      Module.Finite (IsLocalRing.ResidueField O) S := by
  letI : CharZero (rationalPrimeLocalField p hp) :=
    Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)
  letI : Module.Finite (IsLocalRing.ResidueField O) (ContinuousMatrixAdjointH1 σ hσ) :=
    arithmeticContinuousAdjointH1_finiteDimensional a ha p hp hpa σ hσ
  obtain ⟨S, hS, hunique⟩ := traceGeometricCohomology_from_original_universality
    (R := rationalPrimeLocalIntegerRing p hp)
    (F := rationalPrimeLocalField p hp) (K := rationalPrimeLocalClosure p hp)
    (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ)
    (rationalArithmeticGaloisGroup a) σ hσ δ hδ
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom m
    (arithmeticTraceUnframedUniversality_exists (L := L) a ha p hp hpa σ hσ i₀)
  refine ⟨S, ⟨hS, inferInstance⟩, ?_⟩
  intro S' hS'
  exact hunique S' hS'.1

end
end Dubon2026
