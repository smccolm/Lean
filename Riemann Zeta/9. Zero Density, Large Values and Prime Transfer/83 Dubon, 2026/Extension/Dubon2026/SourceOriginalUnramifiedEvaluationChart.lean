import Dubon2026.SourceOriginalPowerCoordinate
import Dubon2026.SourceOriginalRegularEvaluation
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! DUB-17/18 -> geometric dissection -> ordinary j-covering sheets.
At an actual order-one fiber point, the proved power coordinate is the
original evaluation map itself after translation. Restrict to the open
regular locus and extend only the forward function outside the chart source
to obtain the literal map required by Mathlib's covering criterion.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set
attribute [local instance] placeTopology placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_unramified_evaluation_chart {f : F}
    (hf : ∀ c : ℂ, f ≠ algebraMap ℂ F c)
    (v : {P : Place ℂ F // f ∈ P.toValuationSubring})
    (ho : v.1.ord (f - algebraMap ℂ F (originalPlaceEval N ℂ v.1 f)) = 1) :
    ∃ φ : OpenPartialHomeomorph {P : Place ℂ F // f ∈ P.toValuationSubring} ℂ,
      v ∈ φ.source ∧ ⇑φ = fun P => originalPlaceEval N ℂ P.1 f := by
  let c := originalPlaceEval N ℂ v.1 f
  let g := f - algebraMap ℂ F c
  have hg : g ≠ 0 := sub_ne_zero.mpr (hf c)
  have hgm : g ∈ v.1.toValuationSubring := sub_mem v.2 (v.1.algebraMap_mem' c)
  have hgz : originalPlaceEval N ℂ v.1 g = 0 := by
    rw [originalPlaceEval_sub_algebraMap N ℂ v.1 v.2]
    exact sub_self _
  obtain ⟨ζ, _, _, hv, _, _, _, _, _, hform⟩ := exists_original_power_coordinate N v.1 hg hgm hgz
  let e := ζ.trans (Homeomorph.addRight c).toOpenPartialHomeomorph
  have hev : v.1 ∈ e.source := ⟨hv, Set.mem_univ _⟩
  have heq : ∀ P ∈ e.source, originalPlaceEval N ℂ P f = e P := by
    intro P hP
    have hPm : f ∈ P.toValuationSubring := (original_sub_const_mem_iff N P f c).mp (hform P hP.1).1
    have hh := (hform P hP.1).2
    change originalPlaceEval N ℂ P (f - algebraMap ℂ F c) = ζ P ^ (v.1.ord g).toNat at hh
    rw [originalPlaceEval_sub_algebraMap N ℂ P hPm,
      show v.1.ord g = 1 from ho, Int.toNat_one, pow_one] at hh
    change originalPlaceEval N ℂ P f = ζ P + c
    exact sub_eq_iff_eq_add.mp hh
  let L : TopologicalSpace.Opens (Place ℂ F) :=
    ⟨{P | f ∈ P.toValuationSubring}, isOpen_original_regular_locus N f⟩
  have hL : Nonempty L := ⟨v⟩
  let B := e.subtypeRestr (s := L) hL
  have hvB : v ∈ B.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hev
  have hB : ∀ P ∈ B.source, originalPlaceEval N ℂ P.1 f = B P := by
    intro P hP
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hP
    exact heq P.1 hP
  let φ : OpenPartialHomeomorph {P : Place ℂ F // f ∈ P.toValuationSubring} ℂ :=
    { toFun := fun P => originalPlaceEval N ℂ P.1 f
      invFun := B.symm
      source := B.source
      target := B.target
      map_source' := fun P hP => by rw [hB P hP]; exact B.map_source hP
      map_target' := fun {z} hz => B.map_target (x := z) hz
      left_inv' := fun P hP => by rw [hB P hP]; exact B.left_inv hP
      right_inv' := fun z hz => by rw [hB _ (B.map_target hz)]; exact B.right_inv hz
      open_source := B.open_source
      open_target := B.open_target
      continuousOn_toFun := B.continuousOn.congr hB
      continuousOn_invFun := B.continuousOn_symm }
  exact ⟨φ, hvB, rfl⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
