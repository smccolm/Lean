import Dubon2026.CompactDiscreteFiniteQuotient
import Dubon2026.ContinuousFiniteCohomologyVanishing

/-! # Actual compact continuous H1 vanishing for discrete characteristic-zero trivial coefficients -/

namespace Dubon2026
noncomputable section

variable {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul K V]

/-- The original trivial-action continuous one-cocycle descends through an
actual open normal period subgroup, preserving its exact original cocycle law. -/
def continuousTrivialOneCocycleOnQuotient
    (c : continuousRepresentationCocyclesOne (Rep.of (1 : Representation K G V)))
    (U : OpenNormalSubgroup G) (hU : ∀ g u, u ∈ U → c.val (g * u) = c.val g) :
    continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation K (G ⧸ U.toSubgroup) V)) := by
  let f : C(G, V) := ⟨fun g => c.val g, c.property⟩
  let q := compactDiscreteQuotientFunction f U hU
  refine ⟨⟨q, ?_⟩, q.continuous⟩
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro x y
  obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective U.toSubgroup) x
  obtain ⟨h, rfl⟩ := (QuotientGroup.mk'_surjective U.toSubgroup) y
  change q (QuotientGroup.mk' U.toSubgroup (g * h)) =
    q (QuotientGroup.mk' U.toSubgroup h) + q (QuotientGroup.mk' U.toSubgroup g)
  simp only [q, compactDiscreteQuotientFunction_apply]
  exact (groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h

/-- The quotient one-cocycle has exactly the original function values. -/
theorem continuousTrivialOneCocycleOnQuotient_apply
    (c : continuousRepresentationCocyclesOne (Rep.of (1 : Representation K G V)))
    (U : OpenNormalSubgroup G) (hU : ∀ g u, u ∈ U → c.val (g * u) = c.val g) (g : G) :
    (continuousTrivialOneCocycleOnQuotient c U hU).val (QuotientGroup.mk' U.toSubgroup g) =
      c.val g := by
  rfl

variable [CompactSpace G] [CharZero K]

/-- The same original continuous trivial-action one-cocycle vanishes pointwise.
Compactness produces its actual finite quotient; finite averaging and the zero
original degree-zero differential prove the result in characteristic zero. -/
theorem continuousCompactTrivialOneCocycle_eq_zero
    (c : continuousRepresentationCocyclesOne (Rep.of (1 : Representation K G V))) : c = 0 := by
  obtain ⟨U, hU⟩ := compactDiscreteFunction_exists_openNormalPeriods
    (⟨fun g => c.val g, c.property⟩ : C(G, V))
  let Q := G ⧸ U.toSubgroup
  letI : Finite Q := Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen
  letI : Fintype Q := Fintype.ofFinite Q
  let d := continuousTrivialOneCocycleOnQuotient c U hU
  have hn : (Fintype.card Q : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he := finiteOneCocycle_average_coboundary (Rep.of (1 : Representation K Q V)) hn d.val
  have hd : ∀ q : Q, d.val q = 0 := by
    intro q
    have hq := congrFun he q
    change (-((Fintype.card Q : K)⁻¹ • ∑ t, d.val t)) -
      (-((Fintype.card Q : K)⁻¹ • ∑ t, d.val t)) = d.val q at hq
    rw [sub_self] at hq
    exact hq.symm
  apply Subtype.ext
  apply groupCohomology.cocycles₁_ext
  intro g
  exact (continuousTrivialOneCocycleOnQuotient_apply c U hU g).symm.trans
    (hd (QuotientGroup.mk' U.toSubgroup g))

/-- The original continuous H1 quotient vanishes for the same explicitly
trivial action and original discrete characteristic-zero coefficient topology. -/
theorem continuousCompactTrivialH1_eq_zero
    (x : ContinuousRepresentationH1 (Rep.of (1 : Representation K G V)) continuous_snd) :
    x = 0 := by
  induction x using Quotient.inductionOn' with
  | h c =>
    rw [continuousCompactTrivialOneCocycle_eq_zero c]
    rfl

end
end Dubon2026
