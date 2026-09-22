import TaoTrudgianYang2025.HeathBrownDoubleZeta

/-!
# Exact algebra following Bourgain's large-values dichotomy

These are conditional scalar deductions from the explicitly displayed upstream
dichotomy in frozen `bourgain-lvt`. They do not prove that dichotomy for actual
patterns and do not establish an unconditional Bourgain large-values bound.
The optimized row is the one needed near the left endpoint of Add-est (ix).
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- The smaller-cardinality double-zeta maximum in Bourgain's simplification. -/
theorem bourgain_doubleZeta_max_eq {τ ρ : ℝ}
    (hρ : ρ ≤ 1) (hτ : ρ ≤ 4 - 2 * τ) :
    heathBrownDoubleZetaExponent τ ρ = ρ + 2 := by
  have h₁ : 2 * ρ + 1 ≤ ρ + 2 := by linarith
  have h₂ : 5 / 4 * ρ + 1 / 2 * τ + 1 ≤ ρ + 2 := by linarith
  simp only [heathBrownDoubleZetaExponent, max_eq_right h₁, max_eq_left h₂]

/-- The auxiliary maximum is bounded by two affine terms. The mixed term is
`5*x/4 + τ/2 + 1`, as in the displayed source formula. -/
theorem bourgain_auxiliary_doubleZeta_max_le (τ x : ℝ) :
    heathBrownDoubleZetaExponent τ x ≤
      max (x + 2) (2 * x + max 1 (2 * τ - 2)) := by
  have hc₁ : (1 : ℝ) ≤ max 1 (2 * τ - 2) := le_max_left _ _
  have hc₂ : 2 * τ - 2 ≤ max 1 (2 * τ - 2) := le_max_right _ _
  have hm₁ := le_max_left (x + 2) (2 * x + max 1 (2 * τ - 2))
  have hm₂ := le_max_right (x + 2) (2 * x + max 1 (2 * τ - 2))
  unfold heathBrownDoubleZetaExponent
  refine max_le (max_le ?_ hm₁) ?_ <;> linarith

/-- Eliminating the auxiliary witness from the second branch of `bourgain-lvt`.
The displayed analytic inequality remains an explicit, narrower premise. -/
theorem bourgain_eliminate_auxiliary_witness
    {σ τ ρ α₁ α₂ x : ℝ} (hρ : ρ ≤ 1) (hτ : ρ ≤ 4 - 2 * τ)
    (hwitness :
      max (-2 * α₁ + 2 * σ + x + ρ)
        (-α₁ - α₂ / 2 + 2 * σ + x / 2 + 3 * ρ / 2) ≤
      heathBrownDoubleZetaExponent τ ρ / 2 + heathBrownDoubleZetaExponent τ x / 2) :
    ρ ≤ max (α₁ + α₂ / 2 + 2 - 2 * σ)
      (4 * α₁ + 2 + max 1 (2 * τ - 2) - 4 * σ) := by
  rw [bourgain_doubleZeta_max_eq hρ hτ] at hwitness
  have hx := bourgain_auxiliary_doubleZeta_max_le τ x
  have h₁ := (le_max_left (-2 * α₁ + 2 * σ + x + ρ)
    (-α₁ - α₂ / 2 + 2 * σ + x / 2 + 3 * ρ / 2)).trans hwitness
  have h₂ := (le_max_right (-2 * α₁ + 2 * σ + x + ρ)
    (-α₁ - α₂ / 2 + 2 * σ + x / 2 + 3 * ρ / 2)).trans hwitness
  rcases le_total (x + 2) (2 * x + max 1 (2 * τ - 2)) with hcase | hcase
  · rw [max_eq_right hcase] at hx
    exact le_trans (by linarith : ρ ≤ 4 * α₁ + 2 + max 1 (2 * τ - 2) - 4 * σ)
      (le_max_right _ _)
  · rw [max_eq_left hcase] at hx
    exact le_trans (by linarith : ρ ≤ α₁ + α₂ / 2 + 2 - 2 * σ)
      (le_max_left _ _)

/-- Full five-term simplification conditional on the source's explicit dichotomy.
No large-values theorem or region membership is postulated by this declaration. -/
theorem bourgain_simplify_log_dichotomy
    {σ τ ρ α₁ α₂ : ℝ} (hρ : ρ ≤ 1) (hτ : ρ ≤ 4 - 2 * τ)
    (hdichotomy :
      ρ ≤ max (max (α₂ + 2 - 2 * σ) (-α₂ + 2 * τ + 4 - 8 * σ))
        (-2 * α₁ + τ + 12 - 16 * σ) ∨
      ∃ x : ℝ, 0 ≤ x ∧
        max (-2 * α₁ + 2 * σ + x + ρ)
          (-α₁ - α₂ / 2 + 2 * σ + x / 2 + 3 * ρ / 2) ≤
        heathBrownDoubleZetaExponent τ ρ / 2 + heathBrownDoubleZetaExponent τ x / 2) :
    ρ ≤ max
      (max (max (α₂ + 2 - 2 * σ) (α₁ + α₂ / 2 + 2 - 2 * σ))
        (-α₂ + 2 * τ + 4 - 8 * σ))
      (max (-2 * α₁ + τ + 12 - 16 * σ)
        (4 * α₁ + 2 + max 1 (2 * τ - 2) - 4 * σ)) := by
  rcases hdichotomy with hfirst | ⟨x, _, hx⟩
  · apply hfirst.trans
    exact max_le (max_le
      ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
      ((le_max_right _ _).trans (le_max_left _ _)))
      ((le_max_left _ _).trans (le_max_right _ _))
  · apply (bourgain_eliminate_auxiliary_witness hρ hτ hx).trans
    exact max_le
      ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
      ((le_max_right _ _).trans (le_max_right _ _))

/-- An explicit nonnegative parameter choice for the final frozen Bourgain row. -/
theorem bourgain_ninth_row_parameters_nonneg {σ τ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hlower : 16 * σ - 11 ≤ τ) :
    0 ≤ (τ + 9 - 12 * σ) / 6 ∧ 0 ≤ max 0 (4 * σ + 4 * τ / 3 - 5) := by
  constructor
  · linarith
  · exact le_max_left _ _

/-- All five terms are certified on the complete closed polyhedral row.
This is exact rational algebra, not evidence that the analytic dichotomy holds. -/
theorem bourgain_ninth_row_certificate {σ τ : ℝ}
    (hτlo : 1 ≤ τ) (hτhi : τ ≤ 3 / 2)
    (hlower : 16 * σ - 11 ≤ τ) (hupper : 20 * σ + τ / 3 ≤ 16) :
    let α₁ := (τ + 9 - 12 * σ) / 6
    let α₂ := max 0 (4 * σ + 4 * τ / 3 - 5)
    max
      (max (max (α₂ + 2 - 2 * σ) (α₁ + α₂ / 2 + 2 - 2 * σ))
        (-α₂ + 2 * τ + 4 - 8 * σ))
      (max (-2 * α₁ + τ + 12 - 16 * σ)
        (4 * α₁ + 2 + max 1 (2 * τ - 2) - 4 * σ)) ≤
      9 - 12 * σ + 2 * τ / 3 := by
  dsimp only
  rw [max_eq_left (show 2 * τ - 2 ≤ (1 : ℝ) by linarith)]
  rcases le_total 0 (4 * σ + 4 * τ / 3 - 5) with ha | ha
  · rw [max_eq_right ha]
    refine max_le (max_le (max_le ?_ ?_) ?_) (max_le ?_ ?_) <;> linarith
  · rw [max_eq_left ha]
    refine max_le (max_le (max_le ?_ ?_) ?_) (max_le ?_ ?_) <;> linarith

/-- The selected row follows from the actual upstream dichotomy if supplied.
The missing analytic source entry remains explicit rather than hidden in a class. -/
theorem bourgain_ninth_row_of_log_dichotomy
    {σ τ ρ : ℝ} (hρ : ρ ≤ 1) (hτlo : 1 ≤ τ) (hτhi : τ ≤ 3 / 2)
    (hlower : 16 * σ - 11 ≤ τ) (hupper : 20 * σ + τ / 3 ≤ 16)
    (hdichotomy :
      let α₁ := (τ + 9 - 12 * σ) / 6
      let α₂ := max 0 (4 * σ + 4 * τ / 3 - 5)
      ρ ≤ max (max (α₂ + 2 - 2 * σ) (-α₂ + 2 * τ + 4 - 8 * σ))
        (-2 * α₁ + τ + 12 - 16 * σ) ∨
      ∃ x : ℝ, 0 ≤ x ∧
        max (-2 * α₁ + 2 * σ + x + ρ)
          (-α₁ - α₂ / 2 + 2 * σ + x / 2 + 3 * ρ / 2) ≤
        heathBrownDoubleZetaExponent τ ρ / 2 + heathBrownDoubleZetaExponent τ x / 2) :
    ρ ≤ 9 - 12 * σ + 2 * τ / 3 := by
  exact (bourgain_simplify_log_dichotomy hρ (by linarith) hdichotomy).trans
    (bourgain_ninth_row_certificate hτlo hτhi hlower hupper)

end TaoTrudgianYang2025

