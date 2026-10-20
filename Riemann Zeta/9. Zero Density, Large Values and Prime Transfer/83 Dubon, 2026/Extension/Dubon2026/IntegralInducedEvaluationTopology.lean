import Dubon2026.GeneralLinearRegularFieldEvaluation
import Dubon2026.IntegralInducedFiniteFree
import Dubon2026.Reuse.Imperial.Patching.Utils.AdicTopology

/-! The literal integral induced module embeds topologically in its
original coefficient-field evaluations. Native automatic continuity of
linear maps and the already adapted compact finite-module theorem are
reused. The original induced module is finite by its proved uniform
denominator/degree bounds; no compact coefficient lattice is supplied.
This is the faithful evaluation route to the required action continuity.
-/

namespace Dubon2026
noncomputable section
open Matrix Topology

universe u
variable (R E : Type u) [CommRing R] [Field E] [Algebra R E] (n : ℕ) (lam : Fin n → ℤ)

/-- Restrict the actual coefficient-field evaluation map to the literal source induced module. -/
def integralInducedFieldEvaluation :
    generalLinearIntegralInducedSubmodule R n lam →ₗ[R] (GeneralLinearGroup (Fin n) E → E) :=
  (generalLinearRegularFieldEvaluation R E n).comp
    (generalLinearIntegralInducedSubmodule R n lam).subtype

/-- Original field-valued evaluations separate the actual original induced functions. -/
theorem integralInducedFieldEvaluation_injective [Infinite E]
    (hRE : Function.Injective (algebraMap R E)) :
    Function.Injective (integralInducedFieldEvaluation R E n lam) :=
  (generalLinearRegularFieldEvaluation_injective R E n hRE).comp Subtype.val_injective

/-- The original evaluation family is continuous for the canonical coefficient-module topology. -/
theorem integralInducedFieldEvaluation_continuous
    [TopologicalSpace R] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul R E]
    [TopologicalSpace (generalLinearIntegralInducedSubmodule R n lam)]
    [IsModuleTopology R (generalLinearIntegralInducedSubmodule R n lam)] :
    Continuous (integralInducedFieldEvaluation R E n lam) :=
  IsModuleTopology.continuous_of_linearMap _

/-- Over the source compact local coefficient PID, the exact induced module is a closed topological subspace of its faithful original field-valued evaluations. -/
theorem integralLocalInducedFieldEvaluation_isClosedEmbedding
    [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
    [TopologicalSpace R] [CompactSpace R]
    [Infinite E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul R E] [T2Space E]
    {m : ℕ} (weight : Fin (m + 1) → ℤ)
    [TopologicalSpace (generalLinearIntegralInducedSubmodule R (m + 1) weight)]
    [IsModuleTopology R (generalLinearIntegralInducedSubmodule R (m + 1) weight)]
    (hRE : Function.Injective (algebraMap R E)) :
    IsClosedEmbedding (integralInducedFieldEvaluation R E (m + 1) weight) := by
  letI : CompactSpace (generalLinearIntegralInducedSubmodule R (m + 1) weight) :=
    IsModuleTopology.compactSpace R (generalLinearIntegralInducedSubmodule R (m + 1) weight)
  exact (integralInducedFieldEvaluation_continuous R E (m + 1) weight).isClosedEmbedding
    (integralInducedFieldEvaluation_injective R E (m + 1) weight hRE)

end
end Dubon2026
