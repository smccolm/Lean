import Dubon2026.FiniteNilpotentAdicCoefficients
import Mathlib.Topology.Instances.TrivSqZeroExt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Equality of the original product and maximal-adic dual-number topologies -/

namespace Dubon2026

noncomputable section

/-- Over a discrete field, the actual maximal-adic topology of the original dual-number algebra is exactly its original product topology. Both topologies are proved discrete. -/
theorem dualNumber_maximal_adicTopology_eq
    (K : Type*) [Field K] [TopologicalSpace K] [DiscreteTopology K] :
    (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology =
      (inferInstance : TopologicalSpace (DualNumber K)) := by
  letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
  have hAdic : @DiscreteTopology (DualNumber K)
      (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology :=
    nilpotentAdic_discreteTopology 2 (dualNumber_maximalIdeal_sq_zero K)
  have hProduct : DiscreteTopology (DualNumber K) :=
    inferInstanceAs (DiscreteTopology (K × K))
  exact hAdic.eq_bot.trans hProduct.eq_bot.symm

/-- Continuity of actual dual-number matrices is unchanged between the proved original product and maximal-adic topologies. -/
theorem dualNumberGL_continuous_iff
    (K : Type*) [Field K] [TopologicalSpace K] [DiscreteTopology K]
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (f : X → Matrix.GeneralLinearGroup ι (DualNumber K)) :
    (letI : TopologicalSpace (DualNumber K) :=
       (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
     Continuous f) ↔ Continuous f := by
  rw [dualNumber_maximal_adicTopology_eq K]

end
end Dubon2026
