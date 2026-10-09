import Dubon2026.FinitePGroupCharacters
import Dubon2026.ProfiniteClosedSubgroupQuotients
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod

/-! # Actual continuous prime-order characters detect proper closed subgroups -/

namespace Dubon2026

noncomputable section

/-- A genuine proper closed subgroup of an original profinite group with p-group finite quotients is killed by an actual continuous surjective prime-order character. -/
theorem proP_closed_subgroup_character (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp)
    (hP : ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup))
    (K : Subgroup G) (hclosed : IsClosed (K : Set G)) (hK : K ≠ ⊤) :
    ∃ f : G →ₜ* Multiplicative (ZMod p),
      Function.Surjective f ∧ K ≤ f.toMonoidHom.ker := by
  obtain ⟨U, hU⟩ := profinite_closed_subgroup_proper_quotient G K hclosed hK
  obtain ⟨χ, hχ, hker⟩ := finitePGroup_proper_subgroup_character p hp (hP U)
    (K.map (QuotientGroup.mk' U.toSubgroup)) hU
  letI : DiscreteTopology (G ⧸ U.toSubgroup) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  let f : G →ₜ* Multiplicative (ZMod p) := {
    toMonoidHom := χ.comp (QuotientGroup.mk' U.toSubgroup)
    continuous_toFun := (continuous_of_discreteTopology : Continuous χ).comp
      (QuotientGroup.continuous_mk : Continuous (QuotientGroup.mk' U.toSubgroup)) }
  refine ⟨f, hχ.comp (QuotientGroup.mk'_surjective U.toSubgroup), ?_⟩
  intro g hg
  exact hker (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

end
end Dubon2026
