import Dubon2026.IntegralInducedEvaluationTopology
import Dubon2026.GeneralLinearRegularEvaluationContinuity

/-! Continuity of the original integral induced right-translation orbits.
The module carries its canonical finite coefficient-module topology.
Its proved compact faithful evaluation embedding reduces continuity to
the original regular functions on coefficient-field matrices. This is a
required source coefficient-action obligation, not an assumed algebraic
representation or continuous lattice action.
-/

namespace Dubon2026
noncomputable section
open Matrix Topology

universe u

/-- The actual general-linear coefficient map is continuous whenever its original coefficient ring map is continuous. -/
theorem generalLinearCoefficientMap_continuous
    {R E : Type u} [CommRing R] [CommRing E] [TopologicalSpace R] [TopologicalSpace E]
    (n : ℕ) (f : R →+* E) (hf : Continuous f) :
    Continuous (GeneralLinearGroup.map (n := Fin n) f) := by
  apply Continuous.units_map
  exact continuous_id.matrix_map hf

/-- Every original induced vector has a continuous right-translation orbit in the canonical source coefficient-module topology. -/
theorem integralLocalInducedRepresentation_orbit_continuous
    (R E : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
    [TopologicalSpace R] [CompactSpace R]
    [Field E] [Infinite E] [Algebra R E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    [ContinuousSMul R E] [T2Space E]
    {n : ℕ} (lam : Fin (n + 1) → ℤ)
    [TopologicalSpace (generalLinearIntegralInducedSubmodule R (n + 1) lam)]
    [IsModuleTopology R (generalLinearIntegralInducedSubmodule R (n + 1) lam)]
    (hRE : Function.Injective (algebraMap R E)) (hcont : Continuous (algebraMap R E))
    (p : generalLinearIntegralInducedSubmodule R (n + 1) lam) :
    Continuous (fun g : GeneralLinearGroup (Fin (n + 1)) R =>
      generalLinearIntegralInducedRepresentation R (n + 1) lam g p) := by
  apply (integralLocalInducedFieldEvaluation_isClosedEmbedding R E lam hRE).isEmbedding.continuous_iff.mpr
  apply continuous_pi
  intro x
  change Continuous (fun g : GeneralLinearGroup (Fin (n + 1)) R =>
    generalLinearRegularEval x
      (generalLinearIntegralInducedRepresentation R (n + 1) lam g p).val)
  simp_rw [generalLinearIntegralInducedRepresentation_eval]
  have hx : Continuous (fun g : GeneralLinearGroup (Fin (n + 1)) R =>
      x * GeneralLinearGroup.map (algebraMap R E) g) :=
    continuous_const.mul (generalLinearCoefficientMap_continuous (n + 1) (algebraMap R E) hcont)
  have hc := (generalLinearRegularEval_continuous R E (n + 1) p.val).comp hx
  exact hc

end
end Dubon2026
