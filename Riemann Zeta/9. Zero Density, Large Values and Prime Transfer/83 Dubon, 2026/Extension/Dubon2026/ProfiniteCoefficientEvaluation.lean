import Dubon2026.CompletedCoefficientRepresentationFibers
import Dubon2026.CompletedUniversalProfiniteRepresentation
import Dubon2026.CompleteLocalAdicCompactness

/-! # Genuine coefficient evaluation of an entire original continuous profinite lift -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- An actual continuous representation is restricted to its original dense abstract group. -/
def profiniteMatrixRestriction
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A) : G →* GeneralLinearGroup ι A :=
  τ.toMonoidHom.comp (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom

/-- The genuine completed coefficient evaluation associated to the original entire continuous lift. -/
def completedCoefficientMapOfProfiniteLift
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ) : ResidualRepresentationCompletion ρ →ₐ[O] A :=
  completedLocalCoefficientCoordinateMap ρ e
    ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm
      ⟨profiniteMatrixRestriction τ, hτ⟩)

omit [Finite (IsLocalRing.ResidueField O)] [Group.FG G] [IsNoetherianRing O] in
/-- The original completed coefficient map evaluates every original abstract-group matrix exactly. -/
theorem completedCoefficientMapOfProfiniteLift_abstract
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ) :
    (GeneralLinearGroup.map (n := ι) (completedCoefficientMapOfProfiniteLift ρ e τ hτ).toRingHom).comp
      (completedUniversalMatrixRepresentation ρ) = profiniteMatrixRestriction τ :=
  completedLocalCoefficientCoordinateMap_representation ρ e ⟨profiniteMatrixRestriction τ, hτ⟩

omit [Finite (IsLocalRing.ResidueField O)] in
/-- The actual coefficient evaluation preserves the entire original residual point. -/
theorem completedCoefficientMapOfProfiniteLift_reduction
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ) :
    (localCoefficientReduction e).comp (completedCoefficientMapOfProfiniteLift ρ e τ hτ) =
      completedResidualRepresentationEvaluation ρ :=
  completedLocalCoefficientCoordinateMap_reduction ρ e _

omit [Finite (IsLocalRing.ResidueField O)] in
/-- The actual coefficient evaluation is uniformly continuous for the original maximal-adic topologies. -/
theorem completedCoefficientMapOfProfiniteLift_uniformContinuous
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ) :
    UniformContinuous (completedCoefficientMapOfProfiniteLift ρ e τ hτ) :=
  completedLocalCoefficientCoordinateMap_uniformContinuous hA ρ e _

/-- The actual completed coefficient evaluation recovers every matrix of the original continuous profinite lift. -/
theorem completedCoefficientMapOfProfiniteLift_entire
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ) :
    (GeneralLinearGroup.map (n := ι) (completedCoefficientMapOfProfiniteLift ρ e τ hτ).toRingHom).comp
      (completedUniversalProfiniteRepresentation ρ).toMonoidHom = τ.toMonoidHom := by
  letI : T2Space A := completeLocalAdic_t2Space hA
  have hf : Continuous (GeneralLinearGroup.map (n := ι)
      (completedCoefficientMapOfProfiniteLift ρ e τ hτ).toRingHom) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (completedCoefficientMapOfProfiniteLift_uniformContinuous hA ρ e τ hτ).continuous.comp
      (continuous_apply_apply i j)
  have he := (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
    (hf.comp (completedUniversalProfiniteRepresentation ρ).continuous) τ.continuous
    (funext fun g => by
      change GeneralLinearGroup.map (n := ι)
        (completedCoefficientMapOfProfiniteLift ρ e τ hτ).toRingHom
        (completedUniversalProfiniteRepresentation ρ
          (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)) = _
      rw [completedUniversalProfiniteRepresentation_eta]
      exact DFunLike.congr_fun (completedCoefficientMapOfProfiniteLift_abstract ρ e τ hτ) g)
  exact MonoidHom.ext (fun g => congrFun he g)

/-- The entire original continuous matrix lift uniquely determines its genuine completed coefficient map. -/
theorem completedCoefficientMapOfProfiniteLift_unique
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ)
    (f : ResidualRepresentationCompletion ρ →ₐ[O] A)
    (hf : (GeneralLinearGroup.map (n := ι) f.toRingHom).comp
      (completedUniversalProfiniteRepresentation ρ).toMonoidHom = τ.toMonoidHom) :
    completedCoefficientMapOfProfiniteLift ρ e τ hτ = f := by
  apply completedLocalCoefficientCoordinateMap_unique ρ e ⟨profiniteMatrixRestriction τ, hτ⟩ f
  apply MonoidHom.ext
  intro g
  have h := DFunLike.congr_fun hf (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)
  change GeneralLinearGroup.map (n := ι) f.toRingHom
    (completedUniversalProfiniteRepresentation ρ
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)) = _ at h
  rw [completedUniversalProfiniteRepresentation_eta] at h
  exact h

end
end Dubon2026
