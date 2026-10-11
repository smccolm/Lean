import Dubon2026.ContinuousTrivialCocycleFiniteQuotient
import Dubon2026.ContinuousFiniteCohomologyVanishing

/-! # Actual compact-group continuous H2 vanishing for discrete characteristic-zero trivial coefficients -/

namespace Dubon2026
noncomputable section

variable {K G V : Type} [Field K] [CharZero K] [Group G] [AddCommGroup V] [Module K V]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul K V]

/-- Descend the original continuous trivial-action two-cocycle to an actual
finite quotient, average there, and pull the genuine continuous witness back.
The field characteristic and original discrete coefficient topology are explicit. -/
theorem continuousCompactTrivialTwoCocycle_coboundary
    (c : continuousRepresentationCocyclesTwo (Rep.of (1 : Representation K G V))) :
    ∃ w : C(G, V), groupCohomology.d₁₂ (Rep.of (1 : Representation K G V)) w = c.val.val := by
  obtain ⟨U, hfinite, d, hd⟩ := continuousTrivialTwoCocycle_exists_finiteQuotient c
  let Q := G ⧸ U.toSubgroup
  letI : Finite Q := hfinite
  letI : Fintype Q := Fintype.ofFinite Q
  letI : DiscreteTopology Q := QuotientGroup.discreteTopology U.isOpen
  have hn : (Fintype.card Q : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let average : Q → V := fun q => (Fintype.card Q : K)⁻¹ • ∑ t, d.val (q, t)
  have ha : Continuous average := continuous_of_discreteTopology
  let w : C(G, V) := ⟨fun g => average (QuotientGroup.mk' U.toSubgroup g),
    ha.comp QuotientGroup.continuous_mk⟩
  refine ⟨w, ?_⟩
  funext z
  rcases z with ⟨g, h⟩
  have he := congrFun
    (finiteTwoCocycle_average_coboundary (Rep.of (1 : Representation K Q V)) hn d.val)
    (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h)
  change average (QuotientGroup.mk' U.toSubgroup h) -
      average (QuotientGroup.mk' U.toSubgroup g * QuotientGroup.mk' U.toSubgroup h) +
      average (QuotientGroup.mk' U.toSubgroup g) =
    d.val (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) at he
  rw [← map_mul] at he
  change average (QuotientGroup.mk' U.toSubgroup h) -
      average (QuotientGroup.mk' U.toSubgroup (g * h)) +
      average (QuotientGroup.mk' U.toSubgroup g) = c.val (g, h)
  exact he.trans (hd g h)

/-- The exact original continuous H2 quotient vanishes for the explicitly
trivial action on discrete characteristic-zero coefficients. The proof produces
an original continuous cochain witness for each representative. -/
theorem continuousCompactTrivialH2_eq_zero
    (x : ContinuousRepresentationH2 (Rep.of (1 : Representation K G V)) continuous_snd) :
    x = 0 := by
  induction x using Quotient.inductionOn' with
  | h c =>
    obtain ⟨w, hw⟩ := continuousCompactTrivialTwoCocycle_coboundary c
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨w, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hw

end
end Dubon2026
