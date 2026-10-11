import Dubon2026.CompactDiscreteTwoQuotientFunction
import Dubon2026.ContinuousRepresentationCocycles

/-! # Genuine finite-quotient descent of original continuous trivial-action two-cocycles -/

namespace Dubon2026
noncomputable section

variable {R G V : Type} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul R V]

/-- The same original continuous two-cocycle descends to the genuine finite
quotient when both arguments have the given actual periods. Triviality of the
coefficient action is explicit; arbitrary actions are not silently replaced. -/
def continuousTrivialTwoCocycleOnQuotient
    (c : continuousRepresentationCocyclesTwo (Rep.of (1 : Representation R G V)))
    (U : OpenNormalSubgroup G)
    (hU : ∀ g h u v, u ∈ U → v ∈ U → c.val (g * u, h * v) = c.val (g, h)) :
    continuousRepresentationCocyclesTwo
      (Rep.of (1 : Representation R (G ⧸ U.toSubgroup) V)) := by
  let f : C(G × G, V) := ⟨fun z => c.val z, c.property⟩
  let q := compactDiscreteTwoQuotientFunction f U hU
  refine ⟨⟨q, ?_⟩, q.continuous⟩
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro x y z
  obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective U.toSubgroup) x
  obtain ⟨h, rfl⟩ := (QuotientGroup.mk'_surjective U.toSubgroup) y
  obtain ⟨j, rfl⟩ := (QuotientGroup.mk'_surjective U.toSubgroup) z
  change q (QuotientGroup.mk' U.toSubgroup (g * h), QuotientGroup.mk' U.toSubgroup j) +
      q (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) =
    q (QuotientGroup.mk' U.toSubgroup h, QuotientGroup.mk' U.toSubgroup j) +
      q (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup (h * j))
  simp only [q, compactDiscreteTwoQuotientFunction_apply]
  exact (groupCohomology.mem_cocycles₂_iff _).mp c.val.property g h j

/-- The actual quotient two-cocycle recovers the entire original two-cocycle,
not merely its cohomology class. -/
theorem continuousTrivialTwoCocycleOnQuotient_apply
    (c : continuousRepresentationCocyclesTwo (Rep.of (1 : Representation R G V)))
    (U : OpenNormalSubgroup G)
    (hU : ∀ g h u v, u ∈ U → v ∈ U → c.val (g * u, h * v) = c.val (g, h)) (g h : G) :
    (continuousTrivialTwoCocycleOnQuotient c U hU).val
        (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) = c.val (g, h) := by
  rfl

/-- Compactness and original joint continuity provide the actual finite
quotient and a genuine descended two-cocycle for the original trivial action. -/
theorem continuousTrivialTwoCocycle_exists_finiteQuotient [CompactSpace G]
    (c : continuousRepresentationCocyclesTwo (Rep.of (1 : Representation R G V))) :
    ∃ U : OpenNormalSubgroup G, Finite (G ⧸ U.toSubgroup) ∧
      ∃ d : continuousRepresentationCocyclesTwo
          (Rep.of (1 : Representation R (G ⧸ U.toSubgroup) V)),
        ∀ g h, d.val (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) =
          c.val (g, h) := by
  obtain ⟨U, hU⟩ := compactDiscreteTwoFunction_exists_commonPeriods
    (⟨fun z => c.val z, c.property⟩ : C(G × G, V))
  exact ⟨U, Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen,
    continuousTrivialTwoCocycleOnQuotient c U hU, continuousTrivialTwoCocycleOnQuotient_apply c U hU⟩

end
end Dubon2026
