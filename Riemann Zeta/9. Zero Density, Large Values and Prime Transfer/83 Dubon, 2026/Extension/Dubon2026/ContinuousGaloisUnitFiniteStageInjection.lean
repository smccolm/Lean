import Dubon2026.FiniteContinuousGaloisH2InflationInjection
import Dubon2026.ContinuousGaloisUnitH2FiniteZeroDetection

/-! # Original finite Galois H2 embeds in the actual continuous Galois H2 -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : FiniteGaloisIntermediateField K Ω)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- An original finite-stage class whose actual inflation vanishes was
already zero. The actual continuous coboundary descends to a finite larger
field, where Hilbert 90 and the proved inflation injection detect zero. -/
theorem galoisUnitFiniteStageH2Inflation_eq_zero_iff
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    galoisUnitFiniteStageH2Inflation E x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨F, hEF, hF⟩ := continuousGaloisUnitH2_zero_detected_at_finite_stage E x hx
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    apply finiteGaloisUnitTowerH2Inflation_injective K E F
    simpa only [map_zero] using hF
  · rintro rfl
    exact map_zero _

/-- Actual inflation embeds each genuine finite Galois stage into the
original continuous unit H2, with its original Krull topology. -/
theorem galoisUnitFiniteStageH2Inflation_injective :
    Function.Injective (galoisUnitFiniteStageH2Inflation E) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (galoisUnitFiniteStageH2Inflation_eq_zero_iff E (x - y)).mp
  rw [map_sub, hxy, sub_self]

end
end Dubon2026
