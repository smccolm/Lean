import Dubon2026.SourceOriginalPlaceEvaluation

/-! DUB-17/18 -> original torsion cardinality -> Hausdorff complex curve.
Distinct original places have incomparable rank-one valuation rings.
Subtracting the actual residue from an element regular at the first and
polar at the second gives positive and negative orders, respectively.
This supplies precisely the separation needed for Hausdorff charts,
without a general simultaneous-approximation construction.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem original_places_separating_function (N : ℕ) [NeZero N]
    (v w : Place ℂ (modularFunctionFieldOver N ℂ)) (hne : v ≠ w) :
    ∃ f : modularFunctionFieldOver N ℂ, f ≠ 0 ∧ 0 < v.ord f ∧ w.ord f < 0 := by
  classical
  have hle : ¬v.toValuationSubring ≤ w.toValuationSubring :=
    fun h => hne (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ h w.ne_top'))
  change ¬∀ f, f ∈ v.toValuationSubring → f ∈ w.toValuationSubring at hle
  push Not at hle
  obtain ⟨f, hfv, hfw⟩ := hle
  let c := originalPlaceEval N ℂ v f
  let g := f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c
  have hgv : g ∈ v.toValuationSubring := sub_mem hfv (v.algebraMap_mem' c)
  have hgw : g ∉ w.toValuationSubring := by
    intro h
    apply hfw
    have he := add_mem h (w.algebraMap_mem' c)
    simpa only [g, sub_add_cancel] using he
  have hg0 : g ≠ 0 := fun h => hgw (h ▸ zero_mem _)
  have hge : originalPlaceEval N ℂ v g = 0 := by
    dsimp only [g]
    rw [originalPlaceEval_sub_algebraMap N ℂ v hfv c]
    exact sub_self _
  exact ⟨g, hg0, (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v hgv hg0).mp hge,
    lt_of_not_ge (fun h => hgw (w.mem_of_ord_nonneg h))⟩

end
end Dubon2026.SourceFunctionField
