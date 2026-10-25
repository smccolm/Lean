import Dubon2026.SourceCurveRationalResidueValues

/-! DUB-17/18 -> auxiliary cover manifold -> Hausdorff separation.
Distinct actual rank-one place rings are incomparable. Subtracting the
actual residue gives a function with positive order at the first place
and negative order at the second, as in the existing original-curve proof. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section

theorem exists_order_separating_function {EE : Type*} [Field EE] [Algebra ℂ EE]
    (v w : Place ℂ EE) (hv : Function.Bijective (algebraMap ℂ v.ResidueField))
    (hne : v ≠ w) : ∃ a : EE, a ≠ 0 ∧ 0 < v.ord a ∧ w.ord a < 0 := by
  classical
  have hle : ¬v.toValuationSubring ≤ w.toValuationSubring :=
    fun h => hne (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ h w.ne_top'))
  change ¬∀ f, f ∈ v.toValuationSubring → f ∈ w.toValuationSubring at hle
  push Not at hle
  obtain ⟨f, hfv, hfw⟩ := hle
  let c := v.rationalEval hv f
  let g := f - algebraMap ℂ EE c
  have hgv : g ∈ v.toValuationSubring := sub_mem hfv (v.algebraMap_mem' c)
  have hgw : g ∉ w.toValuationSubring := by
    intro h
    apply hfw
    have he := add_mem h (w.algebraMap_mem' c)
    simpa only [g, sub_add_cancel] using he
  have hg0 : g ≠ 0 := fun h => hgw (h ▸ zero_mem _)
  have hge : v.rationalEval hv g = 0 := by
    dsimp only [g]
    rw [v.rationalEval_sub_algebraMap hv hfv c]
    exact sub_self _
  exact ⟨g, hg0, (v.rationalEval_eq_zero_iff_ord_pos hv hgv hg0).mp hge,
    lt_of_not_ge (fun h => hgw (w.mem_of_ord_nonneg h))⟩

end
end Dubon2026.SourceCurve.Place
