import TaoTrudgianYang2025.LargeValueBlockExponents

/-! Actual source patterns at every integral scale with the desired lower exponents. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_lower_largeValuePattern (N : ℕ) (hN : 2 ≤ N)
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    ∃ P : LargeValuePattern, P.N = (N:ℝ) ∧ P.T = (N:ℝ)^τ ∧
      (1/8)*(N:ℝ)^σ ≤ P.V ∧ P.V ≤ (N:ℝ)^σ ∧
      (N:ℝ)^(min τ (2-2*σ)) ≤ 24*(P.ordinates.card:ℝ) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hb := exponentBlockLength_bounds hNr hσ hσ₁
  have hL : 0 < exponentBlockLength N σ := by omega
  have hLN : exponentBlockLength N σ ≤ N := by exact_mod_cast hb.2.2.2
  obtain ⟨P,hscale,hT,hV,hcard⟩ := exists_block_largeValuePattern N
    (exponentBlockLength N σ) hN hL hLN ((N:ℝ)^τ)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hNr) _)
  have hv := exponentBlockLength_value_sandwich hNr hσ hσ₁
  have hc := exponentBlockLength_height_lower (τ:=τ) hNr hσ hσ₁
  refine ⟨P,hscale,hT,?_,?_,?_⟩
  · rw [hV]
    exact hv.1
  · rw [hV]
    exact hv.2
  · nlinarith

end TaoTrudgianYang2025

