import Dubon2026.CompletedCoefficientMaximalIdeal
import Mathlib.RingTheory.AdicCompletion.Topology

/-! # The genuine maximal-adic topology of the original residual completion -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- The original completed ring carries its actual maximal-ideal-adic topology. -/
instance residualRepresentationCompletionWithIdeal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    WithIdeal (ResidualRepresentationCompletion ρ) :=
  ⟨IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)⟩

/-- The genuine maximal-adic topology on the original completion is Hausdorff. -/
instance residualRepresentationCompletionT2Space
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    T2Space (ResidualRepresentationCompletion ρ) := by
  letI := residualRepresentationCompletion_completeLocal ρ
  exact (IsAdic.isHausdorff_iff
    (I := IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) rfl).mp inferInstance

/-- The actual maximal-adic uniform space of the original residual completion is complete. -/
instance residualRepresentationCompletionCompleteSpace
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    CompleteSpace (ResidualRepresentationCompletion ρ) := by
  letI := residualRepresentationCompletion_completeLocal ρ
  exact (IsAdic.isPrecomplete_iff
    (I := IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) rfl).mp inferInstance

/-- The actual original completed coefficient map is uniformly continuous for the true maximal-adic topologies. -/
theorem completedLocalCoefficientCoordinateMap_uniformContinuous
    {A : Type*} [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    UniformContinuous (completedLocalCoefficientCoordinateMap ρ e f) := by
  exact WithIdeal.uniformContinuous_of_map_le
    (f := (completedLocalCoefficientCoordinateMap ρ e f).toRingHom)
    (by
      rw [hA]
      exact Ideal.map_le_iff_le_comap.mpr (completedLocalCoefficientCoordinateMap_maximal ρ e f))

end
end Dubon2026
