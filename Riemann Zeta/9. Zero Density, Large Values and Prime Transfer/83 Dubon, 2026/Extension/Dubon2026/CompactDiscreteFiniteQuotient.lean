import Dubon2026.CompactDiscreteFunctionPeriods
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Exact finite quotient functions from genuine open normal periods -/

namespace Dubon2026
noncomputable section

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Descend the original function through an actual open normal period subgroup.
The actual quotient topology is discrete, so the quotient function is continuous. -/
def compactDiscreteQuotientFunction (f : C(G, A)) (U : OpenNormalSubgroup G)
    (hU : ∀ g u, u ∈ U → f (g * u) = f g) : C(G ⧸ U.toSubgroup, A) := by
  letI : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
  refine ⟨Quotient.lift (fun g => f g) ?_, continuous_of_discreteTopology⟩
  intro x y hxy
  have he : QuotientGroup.mk' U.toSubgroup x = QuotientGroup.mk' U.toSubgroup y :=
    Quotient.sound hxy
  obtain ⟨u, hu, hxu⟩ := (QuotientGroup.mk'_eq_mk' U.toSubgroup).mp he
  rw [← hxu]
  exact (hU x u hu).symm

omit [DiscreteTopology A] in
/-- The actual quotient function recovers the same original function exactly. -/
theorem compactDiscreteQuotientFunction_apply (f : C(G, A)) (U : OpenNormalSubgroup G)
    (hU : ∀ g u, u ∈ U → f (g * u) = f g) (g : G) :
    compactDiscreteQuotientFunction f U hU (QuotientGroup.mk' U.toSubgroup g) = f g := by
  rfl

/-- Every original continuous discrete-valued function on a compact group
factors through an actual finite quotient group, with exact representative values. -/
theorem compactDiscreteFunction_exists_finiteQuotient [CompactSpace G] (f : C(G, A)) :
    ∃ U : OpenNormalSubgroup G, Finite (G ⧸ U.toSubgroup) ∧
      ∃ q : C(G ⧸ U.toSubgroup, A), ∀ g, q (QuotientGroup.mk' U.toSubgroup g) = f g := by
  obtain ⟨U, hU⟩ := compactDiscreteFunction_exists_openNormalPeriods f
  exact ⟨U, Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen,
    compactDiscreteQuotientFunction f U hU, compactDiscreteQuotientFunction_apply f U hU⟩

/-- A genuine jointly continuous two-cochain has a common open normal period
subgroup in both variables, obtained from its actual product-group periods. -/
theorem compactDiscreteTwoFunction_exists_commonPeriods [CompactSpace G] (f : C(G × G, A)) :
    ∃ V : OpenNormalSubgroup G, ∀ g h u v, u ∈ V → v ∈ V → f (g * u, h * v) = f (g, h) := by
  obtain ⟨U, hU⟩ := compactDiscreteFunction_exists_openNormalPeriods f
  let left : G →* G × G := (MonoidHom.id G).prod 1
  let right : G →* G × G := (1 : G →* G).prod (MonoidHom.id G)
  have hl : Continuous left := continuous_id.prodMk continuous_const
  have hr : Continuous right := continuous_const.prodMk continuous_id
  let V : OpenNormalSubgroup G := {
    toSubgroup := U.toSubgroup.comap left ⊓ U.toSubgroup.comap right
    isOpen' := (U.isOpen.preimage hl).inter (U.isOpen.preimage hr)
    isNormal' := inferInstance }
  refine ⟨V, ?_⟩
  intro g h u v hu hv
  have hlu : left u ∈ U := hu.1
  have hrv : right v ∈ U := hv.2
  have huv : (u, v) ∈ U := by
    simpa only [left, right, MonoidHom.prod_apply, MonoidHom.id_apply,
      MonoidHom.one_apply, Prod.mk_mul_mk, mul_one, one_mul] using U.mul_mem hlu hrv
  exact hU (g, h) (u, v) huv

end
end Dubon2026
