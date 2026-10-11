import Dubon2026.FiniteCoefficientCocycleAveraging
import Dubon2026.ContinuousRepresentationCohomology

/-! # Genuine continuous finite-group H1 and H2 vanish by explicit averaging -/

namespace Dubon2026
noncomputable section

variable {K G : Type} [Field K] [Group G] [Fintype G]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep K G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul K A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

omit [IsTopologicalGroup G] in
/-- Averaging a genuine jointly continuous two-cocycle in its second variable
produces a continuous original one-cochain in the unchanged coefficient topology. -/
theorem continuousTwoCocycle_average_continuous
    (c : continuousRepresentationCocyclesTwo A) :
    Continuous (fun g => (Fintype.card G : K)⁻¹ • ∑ t, c.val (g, t)) := by
  apply Continuous.const_smul
  apply continuous_finsetSum
  intro t _
  exact c.property.comp (continuous_id.prodMk continuous_const)

omit [IsTopologicalGroup G] in
/-- Every genuine continuous H1 class vanishes when the actual finite group
order is invertible in the original coefficient field. The witness is explicit. -/
theorem continuousFiniteH1_eq_zero
    (hn : (Fintype.card G : K) ≠ 0) (x : ContinuousRepresentationH1 A hA) : x = 0 := by
  induction x using Quotient.inductionOn' with
  | h c =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨-((Fintype.card G : K)⁻¹ • ∑ h, c.val h), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact finiteOneCocycle_average_coboundary A hn c.val

/-- Every genuine continuous H2 class vanishes under the same invertibility
condition, with a continuous averaging witness rather than an algebraic-only one. -/
theorem continuousFiniteH2_eq_zero
    (hn : (Fintype.card G : K) ≠ 0) (x : ContinuousRepresentationH2 A hA) : x = 0 := by
  induction x using Quotient.inductionOn' with
  | h c =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    let w : C(G, A) := ⟨fun g => (Fintype.card G : K)⁻¹ • ∑ t, c.val (g, t),
      continuousTwoCocycle_average_continuous A c⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact finiteTwoCocycle_average_coboundary A hn c.val

end
end Dubon2026
