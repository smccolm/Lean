import Dubon2026.PolarizedRepresentationFromEquations
import Dubon2026.PolarizedBlockContinuity
import Dubon2026.PolarizedRepresentationIdeal
import Dubon2026.OriginalResidualFramedFibers

/-! The genuine continuous polarized deformation fiber and its original
doubled matrix realization. Its component condition follows from residual
reduction; it is not an extra certificate. This is the input to reusing
the native framed classification in DUB-17's CM deformation comparison. -/

namespace Dubon2026
open Matrix
noncomputable section

universe u
variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
  (H : ProfiniteGrp.{u}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : H →* Oˣ)

/-- All genuine continuous source polarized lifts, with original frame, residual map and fixed similitude. -/
abbrev OriginalContinuousPolarizedFiber :=
  {ρ : H →ₜ* PolarizedGaloisGroup ι A //
    (polarizedCoefficientMap (localCoefficientReduction eA).toRingHom).comp ρ.toMonoidHom = σ ∧
    polarizedSimilitude.comp ρ.toMonoidHom = ((Units.map (algebraMap O A)).comp ν)}

/-- A genuine polarized lift gives the corresponding original continuous framed matrix lift. -/
def polarizedFramedMatrixFiber (ρ : OriginalContinuousPolarizedFiber eA H σ ν) :
    OriginalContinuousFramedFiber eA H (polarizedBlockRepresentation.comp σ) := by
  refine ⟨⟨polarizedBlockRepresentation.comp ρ.val.toMonoidHom,
    polarizedBlockRepresentation_continuous.comp ρ.val.continuous⟩, ?_⟩
  apply MonoidHom.ext
  intro g
  change GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom
    (polarizedBlockRepresentation (ρ.val g)) = polarizedBlockRepresentation (σ g)
  rw [polarizedBlockRepresentation_map]
  exact congrArg polarizedBlockRepresentation (DFunLike.congr_fun ρ.property.1 g)

/-- The actual source lift derives every required equation for its same matrix realization. -/
theorem polarizedFramedMatrixFiber_equations (ρ : OriginalContinuousPolarizedFiber eA H σ ν) :
    PolarizedMatrixEquations (polarizedFramedMatrixFiber eA H σ ν ρ).val.toMonoidHom
      (polarizedComponent.comp σ) ((Units.map (algebraMap O A)).comp ν) := by
  apply (polarizedMatrixEquations_iff_relations _ _ _).mpr
  intro g
  apply (polarizedRelationMatrix_eq_zero_iff _ _ _).mpr
  refine ⟨ρ.val g, ?_, DFunLike.congr_fun ρ.property.2 g, rfl⟩
  have hc := congrArg polarizedComponent (DFunLike.congr_fun ρ.property.1 g)
  change polarizedComponent
    (polarizedCoefficientMap (localCoefficientReduction eA).toRingHom (ρ.val g)) = _ at hc
  rwa [polarizedCoefficientMap_component] at hc

end
end Dubon2026
