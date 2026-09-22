import TaoTrudgianYang2025.EnergyClauseNineRegion
import TaoTrudgianYang2025.EnergyRegionSupremum

/-!
# Full general-energy range for Add-est (ix)

The source cutoff is tau0=8sigma-4. Corrected cardinality witnesses at q
and q+1 supply the cap; the independent energy witness uses q or q-1.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InCardinalityEnergyRegion.energyClauseNine_general
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6)
    (htlo : 8*σ-4 ≤ τ) (hthi : τ ≤ 2*(8*σ-4)) :
    e ≤ energyClauseNineRate σ*τ := by
  by_cases hs : 4/5 ≤ σ
  · exact (h.energyClauseOneGeneral (by linarith) hhi htlo hthi).trans
      (mul_le_mul_of_nonneg_right (energyClauseOneGeneralRate_le_nine hs)
        (by linarith : 0 ≤ τ))
  have hs' : σ ≤ 4/5 := le_of_not_ge hs
  obtain ⟨q,hq,hlow,hhigh⟩ := energyClauseOneGeneral_power_cover htlo hthi
  have hqNat : 2 ≤ q := by rcases hq with rfl|rfl <;> omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨hcap,_⟩ := h.energyClauseOneGeneral_cardinality_cap
    (by linarith) q hqNat hlow hhigh
  have htlow : 4*σ-2 ≤ τ/q := (le_div_iff₀ hqpos).2 hlow
  have hthigh : τ/q ≤ 6*σ-3 := by
    apply (div_le_iff₀ hqpos).2
    have hq' : (0 : ℝ) ≤ (q : ℝ)-2 := by
      exact_mod_cast (show (0 : ℤ) ≤ (q : ℤ)-2 by omega)
    push_cast at hhigh
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4*σ-2) hq']
  have hj := h.jutila_five_cardinality_powered q (by omega)
  rw [jutila_five_high_sigma (by linarith : 33/43 ≤ σ)] at hj
  have hscaled : e/q ≤ energyClauseNineRate σ*(τ/q) := by
    by_cases htshort : τ/q ≤ 6/5
    · obtain ⟨i,hi⟩ := h.heathBrown_nine_branches_powered q (q-1)
        (by omega) (by omega)
      have halo : (1 : ℝ)/2 ≤ ((q-1 : ℕ) : ℝ)/q := by
        rcases hq with rfl|rfl <;> norm_num
      have hahi : ((q-1 : ℕ) : ℝ)/q ≤ (2 : ℝ)/3 := by
        rcases hq with rfl|rfl <;> norm_num
      exact energyClauseNine_short_branch hlo hs' htlow htshort halo hahi hj i hi
    by_cases htmid : τ/q ≤ 3/2
    · obtain ⟨e',hcard,_⟩ :=
        (correctedCardinalityEnergyPowering _ _ _ _ q (by omega) h).1
      exact (h.heathBrown_two_branches_powered q (by omega) htmid (by linarith)).trans
        (hcard.energyClauseNine_middle hlo hs' (by linarith) htmid hj hcap)
    · obtain ⟨i,hi⟩ := exists_heathBrownEnergyBranch
        (by linarith : ρ/q ≤ 1) (h.heathBrown_powered q (by omega))
      exact hi.trans (energyClauseNine_tall_branch hlo hs' (by linarith) hthigh hcap i)
  exact (div_le_div_iff_of_pos_right hqpos).1
    (show e/q ≤ (energyClauseNineRate σ*τ)/q by
      simpa only [mul_div_assoc] using hscaled)

theorem energyClauseNine_general_bound {σ τ : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6)
    (htlo : 8*σ-4 ≤ τ) (hthi : τ ≤ 2*(8*σ-4)) :
    IsLargeValueEnergyBound σ τ (energyClauseNineRate σ*τ) := by
  by_contra hnot
  obtain ⟨ρ,e,s,hregion,hlarge⟩ := energyRegion_exists_rhoStar_gt_of_not_bound
    (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
  exact (not_lt_of_ge ((show InCardinalityEnergyRegion σ τ ρ e from
    ⟨s,hregion⟩).energyClauseNine_general hlo hhi htlo hthi)) hlarge

end TaoTrudgianYang2025
