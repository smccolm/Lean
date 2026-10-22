import Dubon2026.SourceSimplyConnectedCovering
import Dubon2026.SourceOriginalAnalyticJSheets
import Mathlib.Analysis.Convex.Contractible

/-! DUB-17/18 -> original Abel-Jacobi -> actual ordinary dissection cells.
Every nonempty convex open set avoiding the two finite branch values has
exactly dedekindPsi(N) disjoint analytic j sheets, exhausting its entire
original preimage. Native lifting replaces all near-branch slit arguments
for ordinary squares; the ramified cells still use their normal coordinates.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_j_analytic_sheets_on_convex {U : Set ℂ} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hne : U.Nonempty) (h0 : (0 : ℂ) ∉ U) (h1728 : (1728 : ℂ) ∉ U) :
    ∃ A : Fin (SourceLevelProjective.dedekindPsi N) → AnalyticCoord N,
      IsOriginalSheetFamily (jOver N ℂ) U (fun i => (A i).ζ) := by
  classical
  obtain ⟨b, hb⟩ := hne
  haveI : ContractibleSpace U := hconv.contractibleSpace ⟨b, hb⟩
  haveI : LocPathConnectedSpace U := hU.locPathConnectedSpace
  let E := {P : Place ℂ F // jOver N ℂ ∈ P.toValuationSubring}
  let ev : E → ℂ := fun P => originalPlaceEval N ℂ P.1 (jOver N ℂ)
  have hcov : IsCoveringMapOn ev U := (OriginalChart.isCoveringMapOn_original_j N).mono <| by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun he => h0 (he ▸ hz), fun he => h1728 (he ▸ hz)⟩
  have hpre : IsOpen (ev ⁻¹' U) := isOpen_iff_mem_nhds.mpr fun e he =>
    (hcov.continuousAt he).preimage_mem_nhds (hU.mem_nhds he)
  let ev' : (ev ⁻¹' U) → U := fun P => ⟨ev P.1, P.2⟩
  have hcov' : IsCoveringMap ev' := hcov.isCoveringMap_restrictPreimage
  let b' : U := ⟨b, hb⟩
  let I := ev' ⁻¹' {b'}
  let e : I ≃ {P : Place ℂ F // jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) = b} :=
    { toFun := fun P => ⟨P.1.1.1, P.1.1.2, congr_arg Subtype.val P.2⟩
      invFun := fun P => ⟨⟨⟨P.1, P.2.1⟩, by
        change originalPlaceEval N ℂ P.1 (jOver N ℂ) ∈ U
        rw [P.2.2]
        exact hb⟩, Subtype.ext P.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card I = SourceLevelProjective.dedekindPsi N :=
    (Nat.card_congr e).trans (OriginalChart.card_original_j_regular_fiber N b
      (fun he => h0 (he ▸ hb)) (fun he => h1728 (he ▸ hb)))
  have hpos : 0 < Nat.card I := by
    rw [hc]
    exact SourceLevelProjective.dedekindPsi_pos (NeZero.ne N)
  haveI : Nonempty I := (Nat.card_pos_iff.mp hpos).1
  haveI : Finite I := (Nat.card_pos_iff.mp hpos).2
  haveI : DiscreteTopology I := (hcov' b').discreteTopology_fiber
  let q : I := Classical.arbitrary I
  haveI : Nonempty (ev ⁻¹' U) := ⟨q.1⟩
  haveI : Nonempty E := ⟨q.1.1⟩
  obtain ⟨H, hH⟩ := SheetCover.exists_simply_connected_trivialization hcov' b'
  obtain ⟨ζ', ht, hf, _, hd, hx⟩ := SheetCover.sheet_decomposition (f := ev) hpre H
    (fun P => congr_arg Subtype.val (hH P)) hU (Subset.refl U)
  obtain ⟨ζ, hζ⟩ := exists_original_sheet_family_of_subtype ζ' ht
    (fun i P hP => (hf i P hP).2) hd (fun P hP => hx P hP hP)
  let ei : Fin (SourceLevelProjective.dedekindPsi N) ≃ I := (Finite.equivFinOfCardEq hc).symm
  have hr := hζ.reindex ei
  exact ⟨hr.analyticJCoord h0 h1728, hr⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
