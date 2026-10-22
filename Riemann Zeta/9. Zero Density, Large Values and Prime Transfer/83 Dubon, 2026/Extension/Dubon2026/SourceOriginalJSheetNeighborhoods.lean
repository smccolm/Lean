import Dubon2026.SourceCoveringSheetDecomposition
import Dubon2026.SourceOriginalSheetFamilies
import Dubon2026.SourceLevelPsiPrimeStep

/-! DUB-17/18 -> geometric cell dissection -> ordinary grid-cell sheets.
The actual j covering gives a complete finite family of disjoint coordinate
sheets around each ordinary value. Its already proved degree fixes the
index set to Fin(dedekindPsi N); no sheet existence or sheet count is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_j_sheet_neighborhood (b : ℂ) (hb0 : b ≠ 0) (hb1728 : b ≠ 1728) :
    ∃ (V : Set ℂ)
      (ζ : Fin (SourceLevelProjective.dedekindPsi N) → OpenPartialHomeomorph (Place ℂ F) ℂ),
      IsOpen V ∧ b ∈ V ∧ (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
        IsOriginalSheetFamily (jOver N ℂ) V ζ := by
  classical
  let E := {P : Place ℂ F // jOver N ℂ ∈ P.toValuationSubring}
  let ev : E → ℂ := fun P => originalPlaceEval N ℂ P.1 (jOver N ℂ)
  let I := ev ⁻¹' {b}
  let e : I ≃ {P : Place ℂ F // jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) = b} :=
    { toFun := fun P => ⟨P.1.1, P.1.2, P.2⟩
      invFun := fun P => ⟨⟨P.1, P.2.1⟩, P.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card I = SourceLevelProjective.dedekindPsi N :=
    (Nat.card_congr e).trans (OriginalChart.card_original_j_regular_fiber N b hb0 hb1728)
  have hpos : 0 < Nat.card I := by
    rw [hc]
    exact SourceLevelProjective.dedekindPsi_pos (NeZero.ne N)
  haveI : Nonempty I := (Nat.card_pos_iff.mp hpos).1
  haveI : Finite I := (Nat.card_pos_iff.mp hpos).2
  let q : I := Classical.arbitrary I
  haveI : Nonempty E := ⟨q.1⟩
  have hb : b ∈ ({0, 1728} : Set ℂ)ᶜ := by
    simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using And.intro hb0 hb1728
  obtain ⟨hdisc, U, hbU, hU, hpre, H, hH⟩ := OriginalChart.isCoveringMapOn_original_j N b hb
  haveI : DiscreteTopology I := hdisc
  haveI : Nonempty (ev ⁻¹' U) := by
    refine ⟨⟨q.1, ?_⟩⟩
    change ev q.1 ∈ U
    rw [show ev q.1 = b from q.2]
    exact hbU
  let V := U ∩ ({0, 1728} : Set ℂ)ᶜ
  have hV : IsOpen V := hU.inter ((finite_singleton (1728 : ℂ)).insert 0).isClosed.isOpen_compl
  obtain ⟨ζ', htarget, hfwd, _, hdisj, hexh⟩ := SheetCover.sheet_decomposition
    (f := ev) hpre H hH hV (show V ⊆ U from inter_subset_left)
  obtain ⟨ζ, hζ⟩ := exists_original_sheet_family_of_subtype ζ' htarget
    (fun i P hP => (hfwd i P hP).2) hdisj (fun P hP => hexh P hP.1 hP)
  let ei : Fin (SourceLevelProjective.dedekindPsi N) ≃ I := (Finite.equivFinOfCardEq hc).symm
  refine ⟨V, fun i => ζ (ei i), hV, ⟨hbU, hb⟩, ?_, ?_, hζ.reindex ei⟩
  · exact fun h => h.2 (mem_insert 0 {1728})
  · exact fun h => h.2 (mem_insert_of_mem 0 (mem_singleton 1728))

end
end Dubon2026.SourceFunctionField.CellGeometry
