import Dubon2026.SourceOriginalExtendedPlaceMap
import Dubon2026.SourceConstantFieldTraceOrders
import Dubon2026.SourceCurveCoordinateValues

/-! DUB-17/18 -> arithmetic Picard injectivity -> principal-divisor descent
-> regular coordinate traces. A complex place over j=c, with c outside Qbar,
and every place containing its coordinate local ring, is outside the image
of original arithmetic places. Existing rational residue values and exact constant-field orders discharge this geometric condition.
Adapted from S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, trace_mem/hnew.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ

theorem new_of_mem_coordinate_localRing {c : ℂ} (hc : c ∉ Set.range sigma)
    (v' : Place ℂ FC) (hv' : 0 < v'.ord (jOver N ℂ - algebraMap ℂ FC c))
    (W : Place ℂ FC)
    (hmemW : ∀ g : FC, g ∈ IntermediateField.adjoin ℂ (Set.singleton (jOver N ℂ)) →
      g ∈ v'.toValuationSubring → g ∈ W.toValuationSubring) :
    ∀ v : Place Qbar FQ, W ≠ liftPlace N v := by
  intro v hW
  have hj' : jOver N ℂ ∈ v'.toValuationSubring := by
    simpa only [sub_add_cancel] using add_mem (v'.mem_of_ord_nonneg hv'.le) (v'.algebraMap_mem' c)
  have hjk := IntermediateField.mem_adjoin_simple_self ℂ (jOver N ℂ)
  have hj : jOver N Qbar ∈ v.toValuationSubring := by
    apply (mem_liftPlace_iff N v _).mp
    rw [← hW, fieldMap_j]
    exact hmemW _ hjk hj'
  obtain ⟨a, ha, _⟩ := v.exists_unique_coordinate_value
    (original_place_residue_algebraMap_bijective N Qbar v).surjective
    (transcendental_jOver N Qbar) hj
  let u : FQ := jOver N Qbar - algebraMap Qbar FQ a
  have hφu : fieldMap N u = jOver N ℂ - algebraMap ℂ FC (sigma a) := by
    dsimp only [u]
    rw [map_sub, fieldMap_j, fieldMap_constants]
  have hca : c - sigma a ≠ 0 := fun h => hc ⟨a, (sub_eq_zero.mp h).symm⟩
  have hord : v'.ord (fieldMap N u) = 0 := by
    rw [hφu, show jOver N ℂ - algebraMap ℂ FC (sigma a) =
      algebraMap ℂ FC (c - sigma a) + (jOver N ℂ - algebraMap ℂ FC c) by
        rw [map_sub]; ring]
    exact ConstantField.ord_algebraMap_add_eq_zero v' hca hv'
  have hi : fieldMap N u⁻¹ ∈ W.toValuationSubring := by
    rw [map_inv₀]
    apply hmemW
    · rw [hφu]
      exact inv_mem (sub_mem hjk ((IntermediateField.adjoin ℂ {jOver N ℂ}).algebraMap_mem _))
    · apply v'.mem_of_ord_nonneg
      rw [v'.ord_inv, hord, neg_zero]
  rw [hW, mem_liftPlace_iff] at hi
  have hnn := v.ord_nonneg_of_mem hi
  rw [v.ord_inv] at hnn
  change 0 < v.ord u at ha
  omega

end
end Dubon2026.SourceFunctionField.OriginalConstantField
