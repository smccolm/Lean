import Dubon2026.RelativeDualNumberUnframedCohomologyEquiv
import Dubon2026.OriginalResidueCotangentLinearity
import Dubon2026.OriginalResidueDerivationContinuousCocycles
import Dubon2026.OriginalCoefficientRepresentationClass

/-! # The actual cotangent class map is the original coefficient-evaluation class map -/

namespace Dubon2026
noncomputable section
open Matrix

/-- The original continuous cocycle quotient as a linear map with its actual cohomology codomain. -/
private def continuousCocycleClassLinearMap
    {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing k]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]
    (σ : G →* GeneralLinearGroup ι k) (hσ : Continuous σ) :
    continuousMatrixAdjointCocycles σ →ₗ[k] ContinuousMatrixAdjointH1 σ hσ := by
  let q := Submodule.mkQ (R := k) (M := continuousMatrixAdjointCocycles σ)
    (continuousMatrixAdjointCoboundaries σ hσ)
  exact q

variable {ι O A : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Evaluate the genuine cotangent maps as the same continuous adjoint cocycles. -/
private def originalCotangentContinuousCocycleLinearMap
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ) :
    OriginalResidueCotangentMaps eA →ₗ[IsLocalRing.ResidueField O]
      continuousMatrixAdjointCocycles σ :=
  (originalResidueDerivationContinuousCocycleLinearMap hA eA τ.toMonoidHom
    τ.continuous σ hσ hτ).comp
      (originalResidueCotangentDerivationLinearEquiv eA).toLinearMap

/-- Evaluate the genuine universal differentials on the original representation,
then pass the resulting continuous adjoint cocycle to its original cohomology class.
The map is linear over the original residue field. -/
def originalCotangentCohomologyClassLinearMap
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ) :
    OriginalResidueCotangentMaps eA →ₗ[IsLocalRing.ResidueField O]
      ContinuousMatrixAdjointH1 σ hσ :=
  (continuousCocycleClassLinearMap σ hσ).comp
    (originalCotangentContinuousCocycleLinearMap hA eA H σ hσ τ hτ)

omit [IsTopologicalRing A] in
/-- The linear cotangent class is precisely the continuous cohomology class of
the original coefficient-evaluated unframed deformation. The equality consumes
the same original matrices, residue identification and universal differential. -/
theorem originalCotangentCohomologyClassLinearMap_coefficient
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ) (d : OriginalResidueCotangentMaps eA) :
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    originalCotangentCohomologyClassLinearMap hA eA H σ hσ τ hτ d =
      relativeDualNumberUnframedCohomologyMap H σ hσ
        (originalCoefficientRepresentationClass eA (relativeDualNumberResidueEquiv O)
          H σ τ hτ (originalResidueCotangentContinuousFiberEquiv hA eA d)) := by
  let d' := originalResidueCotangentDerivationLinearEquiv eA d
  let t : {t : MatrixFirstOrderLift σ // Continuous t.val} :=
    ⟨originalResidueDerivationFirstOrderLift eA τ.toMonoidHom σ hτ d',
      originalResidueDerivationFirstOrderLift_continuous hA eA τ.toMonoidHom
        τ.continuous σ hτ d'⟩
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  have ht : relativeDualNumberFramedFiberEquiv H σ t =
      originalCoefficientRepresentationFramed eA (relativeDualNumberResidueEquiv O)
        H σ τ hτ (originalResidueCotangentContinuousFiberEquiv hA eA d) := by
    apply Subtype.ext
    apply DFunLike.ext
    intro g
    rfl
  calc
    _ = continuousMatrixFirstOrderClass σ hσ t.val t.property := rfl
    _ = relativeDualNumberUnframedCohomologyMap H σ hσ
        (originalUnframedClass (relativeDualNumberResidueEquiv O) H σ
          (relativeDualNumberFramedFiberEquiv H σ t)) :=
      (relativeDualNumberUnframedCohomologyMap_apply H σ hσ t).symm
    _ = _ := congrArg (relativeDualNumberUnframedCohomologyMap H σ hσ)
      (congrArg (originalUnframedClass (relativeDualNumberResidueEquiv O) H σ) ht)

end
end Dubon2026
