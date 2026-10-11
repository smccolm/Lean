import Dubon2026.OriginalDeterminantFiniteFlatCotangentImage

/-! # The intrinsic geometric finite-flat condition is an actual cohomology subspace -/

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

/-- The intrinsic set of continuous adjoint cohomology classes represented by original
prescribed-determinant, geometric finite-flat dual-number deformations. No linear
closure property is built into this definition. -/
def originalGeometricFiniteFlatCohomologyCondition
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : H →* Oˣ) (j : (K ≃ₐ[F] K) →* H) :
    Set (ContinuousMatrixAdjointH1 σ hσ) := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  exact {x | ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H σ,
    (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) H σ δ c ∧
      originalUnframedFiniteFlatScheme R F K (relativeDualNumberResidueEquiv O) H σ j c) ∧
    relativeDualNumberUnframedCohomologyMap H σ hσ c = x}

/-- The genuine quotient cotangent-image theorem proves linear closure of the intrinsic
geometric condition and gives its unique cohomology submodule. Full unrestricted
universality and an actual residual model are upstream inputs; closure is derived. -/
theorem originalGeometricFiniteFlatCohomologySubmodule_existsUnique
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
    ∃! S : Submodule (IsLocalRing.ResidueField O) (ContinuousMatrixAdjointH1 σ hσ),
      ∀ x, x ∈ S ↔ x ∈ originalGeometricFiniteFlatCohomologyCondition
        (R := R) H σ hσ δ j := by
  let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
    matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
  obtain ⟨hquot, hdata⟩ := originalResidualDeterminantFiniteFlatCotangent_classification
    hA eA H σ hσ τ hτ δ hδ j m hwhole
  letI : IsLocalRing (A ⧸ J) := hquot
  obtain ⟨_, hQ, _, hclass⟩ := hdata
  let eQ := originalLocalQuotientResidueEquiv eA J
  let τQ := originalCoefficientQuotientRepresentation H τ J
  let hτQ := originalCoefficientQuotientRepresentation_residue eA H σ τ hτ J
  let LQ := originalCotangentCohomologyClassLinearMap hQ eQ H σ hσ τQ hτQ
  have hmem (x : ContinuousMatrixAdjointH1 σ hσ) :
      x ∈ LinearMap.range LQ ↔ x ∈ originalGeometricFiniteFlatCohomologyCondition
        (R := R) H σ hσ δ j := hclass.2 x
  refine ⟨LinearMap.range LQ, hmem, ?_⟩
  intro S hS
  apply Submodule.ext
  intro x
  exact (hS x).trans (hmem x).symm

end
end Dubon2026
