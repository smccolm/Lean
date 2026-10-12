import Dubon2026.LocalFieldContinuousInvariantFiniteRestriction
import Mathlib.GroupTheory.Divisible

/-! # Surjectivity of original continuous local H2 restriction -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- Actual restriction on original continuous local H2 is surjective
for every finite separable intermediate field. The preimage is obtained
from the proved degree formula and divisibility of the genuine rational circle. -/
theorem localFieldContinuousH2_restriction_surjective :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    Function.Surjective (continuousGaloisUnitBaseChangeH2 K E Ω Ω) := by
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  letI : Fact (0 < (1 : ℚ)) := ⟨zero_lt_one⟩
  letI : DivisibleBy (AddCircle (1 : ℚ)) ℕ := AddGroup.divisibleByNatOfDivisibleByInt _
  intro y
  obtain ⟨q, hq⟩ := (DivisibleBy.surjective_smul (AddCircle (1 : ℚ)) ℕ
    (Module.finrank_pos (R := K) (M := E)).ne') (localFieldContinuousH2InvariantEquiv E Ω y)
  obtain ⟨x, hx⟩ := (localFieldContinuousH2InvariantEquiv K Ω).surjective q
  refine ⟨x, (localFieldContinuousH2InvariantEquiv E Ω).injective ?_⟩
  rw [localFieldContinuousH2InvariantEquiv_finite_restriction, hx]
  exact hq

end
end Dubon2026
