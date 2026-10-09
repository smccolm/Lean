import Dubon2026.FixedResidualQuotientSubgroup
import Dubon2026.FixedProPTopologicalGeneration
import Dubon2026.ContinuousImageTopologicalGenerators
import Dubon2026.FiniteIndexTopologicalGenerators

/-! # Genuine topological generators of the actual fixed ambient residual quotient -/

namespace Dubon2026

noncomputable section

/-- Original residual character finiteness and the actual finite residual quotient give genuine finite topological generators of the entire fixed ambient quotient. -/
theorem fixedResidualQuotient_finitely_generated
    (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    [Finite (G ⧸ K)] (hK : IsClosed (K : Set G))
    [Finite (K →ₜ* Multiplicative (ZMod p))] :
    ∃ S : Finset (G ⧸ fixedResidualProPKernel p G K hK),
      (Subgroup.closure (S : Set (G ⧸ fixedResidualProPKernel p G K hK))).topologicalClosure = ⊤ := by
  classical
  letI : Finite (closedSubgroupProfinite G K hK →ₜ* Multiplicative (ZMod p)) :=
    inferInstanceAs (Finite (K →ₜ* Multiplicative (ZMod p)))
  obtain ⟨S, hS⟩ := profiniteProPQuotient_finitely_generated p hp
    (closedSubgroupProfinite G K hK)
  let f := fixedResidualQuotientSubgroupFactor p G K hK
  have hgen := continuous_surjective_image_topological_generators f
    (fixedResidualQuotientSubgroupFactor_continuous p G K hK)
    (fixedResidualQuotientSubgroupFactor_surjective p G K hK) S hS
  letI := fixedResidualQuotientSubgroup_finite_quotient p G K hK
  exact finiteIndex_normal_topological_generators
    (FixedResidualQuotientSubgroup p G K hK) (S.image f) hgen

end
end Dubon2026
