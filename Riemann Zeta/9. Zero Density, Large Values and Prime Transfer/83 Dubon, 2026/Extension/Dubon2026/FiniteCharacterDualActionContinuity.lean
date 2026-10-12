import Dubon2026.CharacterDualCoefficientSequence

/-! # Continuity of the actual finite character-valued dual action

Finite original coefficient values make the evaluation map an embedding into
the finite product. Continuity of the actual action and character therefore
supplies the dual-action continuity needed to apply the connecting-cup identity
to the original finite-module dual sequence in DUB-17's local duality route.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]

omit [IsTopologicalRing k] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] in
/-- The actual dual evaluation function embeds the finite original coefficient
dual into the original finite product, with the supplied discrete topology. -/
theorem finiteCharacterDualEvaluation_isEmbedding :
    Topology.IsEmbedding (fun ℓ : characterDualCoefficientRep A χ => (ℓ : A → k)) := by
  exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    continuous_of_discreteTopology DFunLike.coe_injective
    (fun _ _ => isOpen_discrete _)).isEmbedding

/-- The original continuous coefficient action and actual character give joint
continuity of the genuine character-valued dual action. -/
theorem finiteCharacterDualAction_continuous
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hχ : Continuous χ) :
    Continuous (fun z : G × characterDualCoefficientRep A χ =>
      (characterDualCoefficientRep A χ).ρ z.1 z.2) := by
  apply (finiteCharacterDualEvaluation_isEmbedding A χ).continuous_iff.mpr
  apply continuous_pi
  intro a
  change Continuous (fun z : G × characterDualCoefficientRep A χ =>
    χ z.1 * z.2 (A.ρ z.1⁻¹ a))
  apply (hχ.comp continuous_fst).mul
  have he : Continuous (fun z : characterDualCoefficientRep A χ × A => z.1 z.2) :=
    continuous_of_discreteTopology
  exact he.comp (continuous_snd.prodMk
    (hA.comp (continuous_fst.inv.prodMk continuous_const)))

end
end Dubon2026
