import Dubon2026.SourceCoverStarConvexLiftFamily
import Dubon2026.SourceCoverLiftedCoordinate

/-! DUB-17/18 -> finite lifted dissection -> all coordinate sheets of a cell.
Assemble the proved open lift family into disjoint coordinates. Keeping this
pure topological deduction generic avoids expanding the Kummer field while
retaining the exact maps and complete coverage. -/
namespace Dubon2026.SourceFunctionField.SheetCover
noncomputable section
open Set Topology
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

theorem exists_coordinate_family_of_starConvex (p : E → X) (hp : IsCoveringMap p)
    (e : OpenPartialHomeomorph X ℂ) {V : Set ℂ} (hV : IsOpen V)
    {q : ℂ} (hq : q ∈ V) (hc : StarConvex ℝ q V) (hVe : V ⊆ e.target) :
    ∃ ζ : (p ⁻¹' {e.symm q}) → OpenPartialHomeomorph E ℂ,
      (∀ i, (ζ i).target = V ∧ i.1 ∈ (ζ i).source ∧ ζ i i.1 = q) ∧
      (∀ i z, z ∈ V → p ((ζ i).symm z) = e.symm z) ∧
      (∀ i w, w ∈ (ζ i).source → p w ∈ e.source ∧ ζ i w = e (p w)) ∧
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
      (∀ w z, z ∈ V → p w = e.symm z → ∃ i, (ζ i).symm z = w) := by
  classical
  obtain ⟨s, hsq, hsp, hs, hd, hx⟩ :=
    exists_open_lift_family_of_starConvex p hp e hV hq hc hVe
  have hco (i : p ⁻¹' {e.symm q}) :=
    exists_coordinate_of_open_lift p e hV hq hVe (s i) (hs i) (hsp i)
  choose ζ hsource htarget hforward hinverse hmap using hco
  refine ⟨ζ, ?_, ?_, hmap, ?_, ?_⟩
  · intro i
    refine ⟨htarget i, ?_, ?_⟩
    · rw [hsource i]
      exact ⟨⟨q, hq⟩, hsq i⟩
    · rw [← hsq i]
      exact hforward i ⟨q, hq⟩
  · intro i z hz
    rw [hinverse i z hz]
    exact hsp i ⟨z, hz⟩
  · intro i j hij
    rw [hsource i, hsource j]
    exact hd hij
  · intro w z hz he
    obtain ⟨i, hi⟩ := hx w ⟨z, hz⟩ he
    exact ⟨i, (hinverse i z hz).trans hi⟩

end
end Dubon2026.SourceFunctionField.SheetCover
