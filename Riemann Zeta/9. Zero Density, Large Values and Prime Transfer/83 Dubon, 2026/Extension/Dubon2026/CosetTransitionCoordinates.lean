import Dubon2026.OriginalSubgroupCosetCoordinates
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Tactic.Group

/-! # Literal subgroup transition coordinates for the original finite coset trace -/

namespace Dubon2026
noncomputable section

variable {G : Type} [Group G] (S : Subgroup G)

/-- The actual subgroup element relating the chosen representatives
of q and g q. It is computed inside the original group. -/
def cosetTransition (g : G) (q : G ⧸ S) : S :=
  ⟨(g • q).out⁻¹ * (g * q.out), by
    apply QuotientGroup.leftRel_apply.mp
    apply Quotient.exact'
    exact (Quotient.out_eq' (g • q)).trans (MulAction.Quotient.mk_smul_out S g q).symm⟩

/-- Transition coordinates recover the original product exactly. -/
theorem cosetTransition_factor (g : G) (q : G ⧸ S) :
    (g • q).out * (cosetTransition S g q : G) = g * q.out := by
  change (g • q).out * ((g • q).out⁻¹ * (g * q.out)) = _
  group

/-- The genuine transition coordinates satisfy their crossed-product
identity inside the original subgroup. -/
theorem cosetTransition_mul (g h : G) (q : G ⧸ S) :
    cosetTransition S (g * h) q = cosetTransition S g (h • q) * cosetTransition S h q := by
  apply Subtype.ext
  dsimp only [cosetTransition, Subgroup.coe_mul]
  rw [mul_smul]
  group

/-- For an open original subgroup, its actual coset transition is
jointly continuous. No topology on an abstract replacement is used. -/
theorem cosetTransition_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    (hS : IsOpen (S : Set G)) :
    Continuous (fun z : G × (G ⧸ S) => cosetTransition S z.1 z.2) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  apply Continuous.subtype_mk
  exact (hout.comp (continuous_fst.smul continuous_snd)).inv.mul
    (continuous_fst.mul (hout.comp continuous_snd))

end
end Dubon2026
