import Dubon2026.SourceOriginalPlaceEvaluation

/-! DUB-17/18 -> original Weil pairing descent -> moving arithmetic
Picard representatives. The already proved original complex place separation
argument works over every closed rational-algebra constant field: actual
residues and incomparable valuation rings supply the same separator.
This extension is required for the arithmetic field, before quotient descent. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem original_closed_places_separating_function (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (v w : Place L (modularFunctionFieldOver N L)) (hne : v ≠ w) :
    ∃ f : modularFunctionFieldOver N L, f ≠ 0 ∧ 0 < v.ord f ∧ w.ord f < 0 := by
  classical
  have hle : ¬v.toValuationSubring ≤ w.toValuationSubring :=
    fun h => hne (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ h w.ne_top'))
  change ¬∀ f, f ∈ v.toValuationSubring → f ∈ w.toValuationSubring at hle
  push Not at hle
  obtain ⟨f, hfv, hfw⟩ := hle
  let c := originalPlaceEval N L v f
  let g := f - algebraMap L (modularFunctionFieldOver N L) c
  have hgv : g ∈ v.toValuationSubring := sub_mem hfv (v.algebraMap_mem' c)
  have hgw : g ∉ w.toValuationSubring := by
    intro h
    apply hfw
    have he := add_mem h (w.algebraMap_mem' c)
    simpa only [g, sub_add_cancel] using he
  have hg0 : g ≠ 0 := fun h => hgw (h ▸ zero_mem _)
  have hge : originalPlaceEval N L v g = 0 := by
    dsimp only [g]
    rw [originalPlaceEval_sub_algebraMap N L v hfv c]
    exact sub_self _
  exact ⟨g, hg0, (originalPlaceEval_eq_zero_iff_ord_pos N L v hgv hg0).mp hge,
    lt_of_not_ge (fun h => hgw (w.mem_of_ord_nonneg h))⟩

end
end Dubon2026.SourceFunctionField
