import Dubon2026.SourceOriginalRegularEvaluation
import Mathlib.Topology.Covering.Basic

/-! DUB-17/18 -> geometric dissection -> ordinary covering sheets.
The actual residue-evaluation map on its regular locus is closed. Reuse the
proved prescribed-fiber exhaustion and the native neighborhood criterion
for closed maps. This avoids a new argument about limits at poles.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter Metric
open scoped Topology
attribute [local instance] placeTopology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem isClosedMap_original_regular_evaluation {f : F}
    (hf : ∀ c : ℂ, f ≠ algebraMap ℂ F c) :
    IsClosedMap (fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} =>
      originalPlaceEval N ℂ P.1 f) := by
  classical
  let L : Set (Place ℂ F) := {P | f ∈ P.toValuationSubring}
  let ev : L → ℂ := fun P => originalPlaceEval N ℂ P.1 f
  have hL : IsOpen L := isOpen_original_regular_locus N f
  apply isClosedMap_iff_comap_nhds_le.mpr
  intro b U hU
  obtain ⟨V, hV, hfibV, hVU⟩ := mem_nhdsSet_iff_exists.mp hU
  let W : Set (Place ℂ F) := Subtype.val '' V
  have hW : IsOpen W := hL.isOpenMap_subtype_val V hV
  have hne : f - algebraMap ℂ F b ≠ 0 := sub_ne_zero.mpr (hf b)
  let S := originalPositiveFiber N f b
  have hSW : ∀ v ∈ S, v ∈ W := by
    intro v hv
    obtain ⟨hvm, hve⟩ := (mem_originalPositiveFiber_iff_regular_eval N hne v).mp hv
    exact ⟨⟨v, hvm⟩, hfibV hve, rfl⟩
  obtain ⟨ε, hε, hcover⟩ := exists_original_prescribed_fiber_cover N b hne S
    (mem_originalPositiveFiber N f b) (fun _ => W) (fun _ _ => hW) hSW
  apply Filter.mem_comap.mpr
  refine ⟨ball b ε, ball_mem_nhds b hε, ?_⟩
  intro P hP
  have heq : originalPlaceEval N ℂ P.1 f = ev P := rfl
  have hpos : 0 < P.1.ord (f - algebraMap ℂ F (ev P)) := by
    apply (mem_originalPositiveFiber N f (ev P) P.1).mp
    exact (mem_originalPositiveFiber_iff_regular_eval N
      (sub_ne_zero.mpr (hf (ev P))) P.1).mpr ⟨P.2, heq⟩
  obtain ⟨_, _, hPW⟩ := hcover (ev P) hP P.1 hpos
  obtain ⟨Q, hQV, hQP⟩ := hPW
  have hQP' : Q = P := Subtype.ext hQP
  exact hVU (hQP' ▸ hQV)

end
end Dubon2026.SourceFunctionField.OriginalChart
