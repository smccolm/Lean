import Dubon2026.AuxiliaryCharacterParameterConvergence
import Mathlib.RingTheory.AdicCompletion.Topology

/-! Evaluate at the specified original generators, rather than making
a new cyclic choice. This preserves the common variable labels needed
to compare the actual auxiliary group algebra with the arithmetic ring. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- A specified finite family in the maximal ideal of a complete
local algebra gives a power-series map with those exact variable values. -/
theorem completeLocal_exists_specified_powerSeriesMap
    (O : Type*) [CommRing O] {A η : Type*}
    [CommRing A] [IsLocalRing A] [Algebra O A] [Finite η]
    [IsAdicComplete (maximalIdeal A) A]
    (x : η → A) (hx : ∀ i, x i ∈ maximalIdeal A) :
    ∃ f : MvPowerSeries η O →ₐ[O] A, ∀ i, f (MvPowerSeries.X i) = x i := by
  letI : TopologicalSpace O := ⊥
  letI : DiscreteTopology O := ⟨rfl⟩
  letI : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  letI : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  letI : WithIdeal A := ⟨maximalIdeal A⟩
  have htop : IsAdic (maximalIdeal A) := rfl
  have hcomplete := htop.isAdicComplete_iff.mp (inferInstance : IsAdicComplete (maximalIdeal A) A)
  letI : CompleteSpace A := hcomplete.1
  letI : T2Space A := hcomplete.2
  letI : ContinuousSMul O A := ⟨by
    have hc : Continuous (algebraMap O A) := continuous_of_discreteTopology
    simpa only [Algebra.smul_def] using (hc.comp continuous_fst).mul continuous_snd⟩
  let hEval := maximalAdic_finiteFamily_hasEval rfl x hx
  refine ⟨MvPowerSeries.aeval hEval, fun i => ?_⟩
  rw [MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X]

end
end Dubon2026
