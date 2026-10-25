import Dubon2026.SourceCoverStarConvexLift

/-! DUB-17/18 -> cover geometric reciprocity -> exhaustive lifted cells.
The pinned lifting uniqueness theorem makes the lifted original chart sheets
disjoint and exhaustive. The fiber indexing is literal; no cardinality or
abstract sheet-existence premise is introduced. -/
namespace Dubon2026.SourceFunctionField.SheetCover
noncomputable section
open Set Topology
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

theorem exists_open_lift_family_of_starConvex (p : E → X) (hp : IsCoveringMap p)
    (e : OpenPartialHomeomorph X ℂ) {V : Set ℂ} (hV : IsOpen V)
    {q : ℂ} (hq : q ∈ V) (hc : StarConvex ℝ q V) (hVe : V ⊆ e.target) :
    ∃ s : (p ⁻¹' {e.symm q}) → C(V, E),
      (∀ i, s i ⟨q, hq⟩ = i.1) ∧
      (∀ i (z : V), p (s i z) = e.symm z) ∧
      (∀ i, IsOpenEmbedding (s i)) ∧
      (Pairwise fun i j => Disjoint (Set.range (s i)) (Set.range (s j))) ∧
      (∀ (w : E) (z : V), p w = e.symm z → ∃ i, s i z = w) := by
  classical
  letI : ContractibleSpace V := hc.contractibleSpace ⟨q, hq⟩
  letI : LocPathConnectedSpace V := hV.locPathConnectedSpace
  have hex (i : p ⁻¹' {e.symm q}) :=
    exists_open_lift_of_starConvex p hp e hV hq hc hVe i.1 i.2
  choose s hsq hsp hs using hex
  refine ⟨s, hsq, hsp, hs, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro w ⟨x, hx⟩ ⟨y, hy⟩
    have hxy : x = y := Subtype.ext (e.symm.injOn (hVe x.2) (hVe y.2)
      ((hsp i x).symm.trans ((congrArg p (hx.trans hy.symm)).trans (hsp j y))))
    subst y
    have he : (s i : V → E) = s j := hp.eq_of_comp_eq (s i).continuous (s j).continuous
      (funext fun z => (hsp i z).trans (hsp j z).symm) x (hx.trans hy.symm)
    exact hij (Subtype.ext ((hsq i).symm.trans ((congrFun he ⟨q, hq⟩).trans (hsq j))))
  · intro w z hw
    let b : C(V, X) := ⟨fun t => e.symm t,
      (e.continuousOn_symm.mono hVe).comp_continuous continuous_subtype_val Subtype.prop⟩
    obtain ⟨t, ht, _⟩ := hp.existsUnique_continuousMap_lifts b z w hw
    let i : p ⁻¹' {e.symm q} := ⟨t ⟨q, hq⟩, congrFun ht.2 ⟨q, hq⟩⟩
    have he : (s i : V → E) = t := hp.eq_of_comp_eq (s i).continuous t.continuous
      (funext fun u => (hsp i u).trans (congrFun ht.2 u).symm) ⟨q, hq⟩ (hsq i)
    exact ⟨i, (congrFun he z).trans ht.1⟩

end
end Dubon2026.SourceFunctionField.SheetCover
