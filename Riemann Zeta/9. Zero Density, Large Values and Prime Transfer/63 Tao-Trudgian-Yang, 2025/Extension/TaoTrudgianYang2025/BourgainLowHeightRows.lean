import TaoTrudgianYang2025.BourgainNinthRow

/-!
# Additional optimized Bourgain rows in the low-height source range

These rows are deductions from the actual region dichotomy, not archived
polytope memberships. The closed height-one boundary uses classical mean
square. Every remaining physical height lies strictly above one.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- Five-term simplification with the genuine cardinality side conditions
visible; the analytic dichotomy itself is supplied internally. -/
theorem InCardinalityEnergyRegion.bourgain_five_terms
    {σ τ ρ energy χ α : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hr : ρ ≤ 1) (hrt : ρ ≤ 4-2*τ) :
    ρ ≤ max
      (max (max (χ+2-2*σ) (α+χ/2+2-2*σ)) (-χ+2*τ+4-8*σ))
      (max (-2*α+τ+12-16*σ) (4*α+2+max 1 (2*τ-2)-4*σ)) :=
  bourgain_simplify_log_dichotomy hr hrt (h.bourgain_log_dichotomy hσ hχ hmargin)

/-- The first affine optimized row on its full closed low-height cell. -/
theorem InCardinalityEnergyRegion.bourgain_first_affine_row
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (htlo : 1 ≤ τ) (hthi : τ ≤ 3/2)
    (hlower : 14*σ-10 ≤ τ) (hslant : 5*τ ≤ 4+4*σ)
    (hupper : τ ≤ 16*σ-11) :
    ρ ≤ (16-20*σ+τ)/3 := by
  by_cases ht : τ = 1
  · have hc := h.classical_cardinality
    have hm := min_le_left (1-2*σ) (4-6*σ)
    have hmax : classicalLargeValueExponent σ τ ≤ 2-2*σ := by
      unfold classicalLargeValueExponent
      apply max_le le_rfl
      rw [ht]
      linarith
    exact (hc.trans hmax).trans (by linarith)
  · have hr := h.bourgain_cardinality_le_one hσ.le hthi
    have hb := h.bourgain_five_terms (χ := 0) (α := (10-14*σ+τ)/3)
      hσ le_rfl (by simpa only [sub_zero] using lt_of_le_of_ne htlo (Ne.symm ht)) hr (by linarith)
    apply hb.trans
    rw [max_eq_left (by linarith : 2*τ-2 ≤ (1 : ℝ))]
    refine max_le (max_le (max_le ?_ ?_) ?_) (max_le ?_ ?_) <;> linarith

/-- The mixed affine optimized row in the closed interval 1<=tau<=3/2.
The two active upper-height conditions are retained from the frozen cell. -/
theorem InCardinalityEnergyRegion.bourgain_mixed_affine_row
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hthi : τ ≤ 3/2)
    (hslant : 4+4*σ ≤ 5*τ) (hlower : 48-60*σ ≤ τ)
    (hupper : τ ≤ 8-8*σ) :
    ρ ≤ 5-7*σ+3*τ/4 := by
  have hχ : 0 ≤ (5*τ-4*σ-4)/4 := by linarith
  have hmargin : 1 < τ-(5*τ-4*σ-4)/4 := by linarith
  have hr := h.bourgain_cardinality_le_one hσ.le hthi
  have hb := h.bourgain_five_terms
    (χ := (5*τ-4*σ-4)/4) (α := (28-36*σ+τ)/8)
    hσ hχ hmargin hr (by linarith)
  apply hb.trans
  rw [max_eq_left (by linarith : 2*τ-2 ≤ (1 : ℝ))]
  refine max_le (max_le (max_le ?_ ?_) ?_) (max_le ?_ ?_) <;> linarith

/-- The diagonal optimized row, including its height-one boundary. -/
theorem InCardinalityEnergyRegion.bourgain_diagonal_row
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (htlo : 1 ≤ τ) (hthi : τ ≤ 3/2)
    (hupper : τ ≤ 14*σ-10) (hslant : τ ≤ 3*σ-1) :
    ρ ≤ 2-2*σ := by
  by_cases ht : τ = 1
  · apply h.classical_cardinality.trans
    unfold classicalLargeValueExponent
    apply max_le le_rfl
    have hm := min_le_left (1-2*σ) (4-6*σ)
    rw [ht]
    linarith
  · have hr := h.bourgain_cardinality_le_one hσ.le hthi
    have hb := h.bourgain_five_terms (χ := 0) (α := 0)
      hσ le_rfl (by simpa only [sub_zero] using lt_of_le_of_ne htlo (Ne.symm ht)) hr (by linarith)
    apply hb.trans
    rw [max_eq_left (by linarith : 2*τ-2 ≤ (1 : ℝ))]
    refine max_le (max_le (max_le ?_ ?_) ?_) (max_le ?_ ?_) <;> linarith

end TaoTrudgianYang2025
