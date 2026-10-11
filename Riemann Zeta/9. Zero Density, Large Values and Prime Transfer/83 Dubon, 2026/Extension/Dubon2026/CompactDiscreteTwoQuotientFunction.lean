import Dubon2026.CompactDiscreteFiniteQuotient

/-! # Actual two-variable quotient functions from the original common periods -/

namespace Dubon2026
noncomputable section

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Descend both arguments through the same genuine open normal period subgroup.
The relation proof uses the original simultaneous right-period identity. -/
def compactDiscreteTwoQuotientFunction (f : C(G × G, A)) (U : OpenNormalSubgroup G)
    (hU : ∀ g h u v, u ∈ U → v ∈ U → f (g * u, h * v) = f (g, h)) :
    C((G ⧸ U.toSubgroup) × (G ⧸ U.toSubgroup), A) := by
  letI : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
  let q : (G ⧸ U.toSubgroup) → (G ⧸ U.toSubgroup) → A :=
    Quotient.lift₂ (fun g h => f (g, h)) (by
      intro g h g' h' hgg hhh
      have hg : QuotientGroup.mk' U.toSubgroup g = QuotientGroup.mk' U.toSubgroup g' :=
        Quotient.sound hgg
      have hh : QuotientGroup.mk' U.toSubgroup h = QuotientGroup.mk' U.toSubgroup h' :=
        Quotient.sound hhh
      obtain ⟨u, hu, hgu⟩ := (QuotientGroup.mk'_eq_mk' U.toSubgroup).mp hg
      obtain ⟨v, hv, hhv⟩ := (QuotientGroup.mk'_eq_mk' U.toSubgroup).mp hh
      rw [← hgu, ← hhv]
      exact (hU g h u v hu hv).symm)
  exact ⟨fun z => q z.1 z.2, continuous_of_discreteTopology⟩

omit [DiscreteTopology A] in
/-- The descended two-variable function has exactly the original values on
the genuine quotient representatives, with no change of either argument. -/
theorem compactDiscreteTwoQuotientFunction_apply (f : C(G × G, A))
    (U : OpenNormalSubgroup G)
    (hU : ∀ g h u v, u ∈ U → v ∈ U → f (g * u, h * v) = f (g, h)) (g h : G) :
    compactDiscreteTwoQuotientFunction f U hU
        (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) = f (g, h) := by
  rfl

/-- Joint continuity into the original discrete coefficient space gives an
actual continuous function on a common finite quotient in both variables. -/
theorem compactDiscreteTwoFunction_exists_finiteQuotient [CompactSpace G]
    (f : C(G × G, A)) :
    ∃ U : OpenNormalSubgroup G, Finite (G ⧸ U.toSubgroup) ∧
      ∃ q : C((G ⧸ U.toSubgroup) × (G ⧸ U.toSubgroup), A),
        ∀ g h, q (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) = f (g, h) := by
  obtain ⟨U, hU⟩ := compactDiscreteTwoFunction_exists_commonPeriods f
  exact ⟨U, Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen,
    compactDiscreteTwoQuotientFunction f U hU, compactDiscreteTwoQuotientFunction_apply f U hU⟩

end
end Dubon2026
