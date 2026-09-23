import TaoTrudgianYang2025.LargeValueExponent

/-! Exact infimum-to-uniform-bound bridge for general large values. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem isLargeValueBound_of_exponent_le {σ τ B : ℝ}
    (h : largeValueExponent σ τ ≤ (B:EReal)) :
    IsLargeValueBound σ τ B := by
  intro ε hε
  have hlt : largeValueExponent σ τ < ((B+ε/2:ℝ):EReal) :=
    h.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨x,⟨ρ,hρ,rfl⟩,hx⟩ := sInf_lt_iff.mp hlt
  have hρB : ρ < B+ε/2 := EReal.coe_lt_coe_iff.mp hx
  obtain ⟨C,hC,δ,hδ,hbound⟩ := hρ (ε/2) (by linarith)
  refine ⟨C,hC,δ,hδ,?_⟩
  intro P hN hTl hTu hVl hVu
  exact (hbound P hN hTl hTu hVl hVu).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
      (zero_le_one.trans hC))

theorem largeValueExponent_le_iff {σ τ B : ℝ} :
    largeValueExponent σ τ ≤ (B:EReal) ↔ IsLargeValueBound σ τ B :=
  ⟨isLargeValueBound_of_exponent_le,largeValueExponent_le_of_bound⟩

end TaoTrudgianYang2025

