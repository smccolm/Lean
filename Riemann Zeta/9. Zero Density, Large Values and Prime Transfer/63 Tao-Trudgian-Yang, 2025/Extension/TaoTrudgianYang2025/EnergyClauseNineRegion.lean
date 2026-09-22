import TaoTrudgianYang2025.EnergyClauseNineBranches
import TaoTrudgianYang2025.EnergyClauseEightCaps
import TaoTrudgianYang2025.BourgainLowHeightRows

/-!
# Actual Bourgain region consumers for Add-est (ix)

Only proved low-height source rows are used. The finite case split covers
the whole middle-height interval, including all shared cell boundaries.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InCardinalityEnergyRegion.energyClauseNine_middle
    {σ t r e : ℝ} (h : InCardinalityEnergyRegion σ t r e)
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+18/5-(28/5)*σ)) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t := by
  by_cases htcap : (27*σ-18)/2 ≤ t
  · exact energyClauseNine_cap_bound hlo hhi htcap hcap
  by_cases htmixcap : (16*σ-8)/3 ≤ t
  · exact energyClauseNine_cap_mixed_bound hlo hhi htmixcap hcap
  by_cases hs : σ ≤ 17/22
  · by_cases ht : t ≤ (81-96*σ)/5
    · exact energyClauseNine_middle_low_bound hlo hs htlo ht hj
    · have hr := h.bourgain_ninth_row (by linarith) (by linarith) hthi
        (by linarith) (by linarith)
      exact energyClauseNine_middle_ninth_bound hlo hhi (by linarith)
        (by linarith) hr
  · have hs' : 17/22 ≤ σ := le_of_not_ge hs
    by_cases ht : t ≤ (13-8*σ)/5
    · exact energyClauseNine_middle_high_bound hs' htlo ht hj
    by_cases hfirst : t ≤ 16*σ-11
    · by_cases hslant : 5*t ≤ 4+4*σ
      · have hr := h.bourgain_first_affine_row (by linarith) (by linarith)
          hthi (by linarith) hslant hfirst
        exact energyClauseNine_middle_first_bound hs' hhi (by linarith) (by linarith) hr
      · have hr := h.bourgain_mixed_affine_row (by linarith) hthi
          (by linarith) (by linarith) (by linarith)
        exact energyClauseNine_middle_mixed_bound hlo hhi (by linarith) (by linarith) hr
    · by_cases hninth : t ≤ 48-60*σ
      · have hr := h.bourgain_ninth_row (by linarith) (by linarith) hthi
          (by linarith) (by linarith)
        exact energyClauseNine_middle_ninth_bound hlo hhi (by linarith)
          (by linarith) hr
      · have hr := h.bourgain_mixed_affine_row (by linarith) hthi
          (by linarith) (by linarith) (by linarith)
        exact energyClauseNine_middle_mixed_bound hlo hhi (by linarith) (by linarith) hr

end TaoTrudgianYang2025
