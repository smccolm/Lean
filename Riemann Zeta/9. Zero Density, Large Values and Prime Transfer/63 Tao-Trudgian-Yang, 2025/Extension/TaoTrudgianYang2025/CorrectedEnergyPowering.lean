import TaoTrudgianYang2025.EnergyPoweringLimits

/-!
# Corrected cardinality/energy powering

This module proves the owner-authorized two-witness replacement of printed
Lemma 62. The original counterexample remains imported. The two new double-
zeta coordinates are independently extracted; no fifth-coordinate scaling
or third witness is asserted.
-/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

/-- Full corrected powering theorem, from actual input energy-region
membership. Both witnesses are constructed from normalized powered
Dirichlet polynomials, with uniform coefficient constants and independent
coordinate-preserving subsequences. -/
theorem correctedCardinalityEnergyPowering : CorrectedCardinalityEnergyPowering := by
  intro σ τ ρ energy k hk hregion
  have hkNat : 0 < k := by omega
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hkNat
  obtain ⟨s, hs⟩ := hregion
  have hconstants (n : ℕ) := exists_normalized_powered_subpatterns k hkNat
    (poweringAccuracy n) (poweringAccuracy_pos n)
  let C : ℕ → ℝ := fun n => Classical.choose (hconstants n)
  have hC (n : ℕ) : 0 < C n := (Classical.choose_spec (hconstants n)).1
  obtain ⟨F⟩ := exists_powering_input_family (show InCardinalityEnergyRegion σ τ ρ energy from ⟨s, hs⟩) C
  have hselect (n : ℕ) := (Classical.choose_spec (hconstants n)).2 (F.pattern n) (F.value_gt_one n)
  choose Qcard Qenergy hcardLoss henergyLoss using hselect
  have hcardTime := F.powered_time_value_limits k hkNat hC Qcard
  have henergyTime := F.powered_time_value_limits k hkNat hC Qenergy
  have hscale (Q : ∀ n, NormalizedPoweredSubpattern (F.pattern n) k (C n) (poweringAccuracy n)) :=
    normalizedPoweredSubpattern_scale_log_limit F.pattern k C poweringAccuracy Q F.scale_top
  have hcardPos (n : ℕ) : 0 < ((Qcard n).pattern.ordinates.card : ℝ) := by
    have hpos := F.card_pos n
    have hbound := hcardLoss n
    nlinarith
  have hcardEnergyPos (n : ℕ) : 0 < (finsetAdditiveEnergy (Qcard n).pattern.ordinates : ℝ) := by
    have hb : ((Qcard n).pattern.ordinates.card : ℝ) ^ 2 ≤
        (finsetAdditiveEnergy (Qcard n).pattern.ordinates : ℝ) := by
      exact_mod_cast finset_card_square_le_additiveEnergy (Qcard n).pattern.ordinates
    exact (sq_pos_of_pos (hcardPos n)).trans_le hb
  have henergyPos (n : ℕ) : 0 < (finsetAdditiveEnergy (Qenergy n).pattern.ordinates : ℝ) := by
    have hpos := F.energy_pos n
    have hb := henergyLoss n
    have hfactor : 0 < 9 * (k : ℝ) ^ 4 := by positivity
    nlinarith
  have henergyCardPos (n : ℕ) : 0 < ((Qenergy n).pattern.ordinates.card : ℝ) := by
    by_contra hnot
    have hz : (Qenergy n).pattern.ordinates.card = 0 := by
      exact_mod_cast le_antisymm (le_of_not_gt hnot) (Nat.cast_nonneg _)
    have hb := finset_additiveEnergy_le_three_mul_cube
      (Qenergy n).pattern.ordinates (Qenergy n).pattern.ordinates_oneSeparated
    rw [hz] at hb
    have he : finsetAdditiveEnergy (Qenergy n).pattern.ordinates = 0 := by
      simpa using hb
    have hp := henergyPos n
    simp only [he, Nat.cast_zero, lt_self_iff_false] at hp
  have hcardLogInput : Tendsto (fun n => Real.logb (F.pattern n).N
      ((Qcard n).pattern.ordinates.card : ℝ)) atTop (nhds ρ) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (F.pattern n).N)
      (fun n => ((F.pattern n).ordinates.card : ℝ)) _ ρ (1 / k) 1
      (fun n => (F.pattern n).one_lt_N) F.scale_top F.card_pos
      (by positivity) zero_lt_one _ F.card_log
    intro n
    constructor
    · rw [one_div, ← div_eq_inv_mul]
      exact (div_le_iff₀ hkReal).2 (by simpa only [mul_comm] using hcardLoss n)
    · simpa only [one_mul] using (show ((Qcard n).pattern.ordinates.card : ℝ) ≤
        (F.pattern n).ordinates.card by exact_mod_cast (Qcard n).card_le)
  have henergyLogInput : Tendsto (fun n => Real.logb (F.pattern n).N
      (finsetAdditiveEnergy (Qenergy n).pattern.ordinates : ℝ)) atTop (nhds energy) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (F.pattern n).N)
      (fun n => (finsetAdditiveEnergy (F.pattern n).ordinates : ℝ)) _ energy
      (1 / (9 * (k : ℝ) ^ 4)) 1 (fun n => (F.pattern n).one_lt_N)
      F.scale_top F.energy_pos (by positivity) zero_lt_one _ F.energy_log
    intro n
    constructor
    · rw [one_div, ← div_eq_inv_mul]
      exact (div_le_iff₀ (by positivity : 0 < 9 * (k : ℝ) ^ 4)).2
        (by simpa only [mul_comm] using henergyLoss n)
    · simpa only [one_mul] using (show (finsetAdditiveEnergy (Qenergy n).pattern.ordinates : ℝ) ≤
        finsetAdditiveEnergy (F.pattern n).ordinates by exact_mod_cast (Qenergy n).energy_le)
  have hcardLog := tendsto_logb_rebase (fun n => (F.pattern n).N)
    (fun n => (Qcard n).pattern.N) (fun n => ((Qcard n).pattern.ordinates.card : ℝ))
    ρ k hkReal.ne' (fun n => (F.pattern n).one_lt_N) (hscale Qcard) hcardLogInput
  have henergyLog := tendsto_logb_rebase (fun n => (F.pattern n).N)
    (fun n => (Qenergy n).pattern.N) (fun n => (finsetAdditiveEnergy (Qenergy n).pattern.ordinates : ℝ))
    energy k hkReal.ne' (fun n => (F.pattern n).one_lt_N) (hscale Qenergy) henergyLogInput
  have hcardUpperLog := tendsto_logb_rebase (fun n => (F.pattern n).N)
    (fun n => (Qenergy n).pattern.N) (fun n => ((F.pattern n).ordinates.card : ℝ))
    ρ k hkReal.ne' (fun n => (F.pattern n).one_lt_N) (hscale Qenergy) F.card_log
  have henergyUpperLog := tendsto_logb_rebase (fun n => (F.pattern n).N)
    (fun n => (Qcard n).pattern.N) (fun n => (finsetAdditiveEnergy (F.pattern n).ordinates : ℝ))
    energy k hkReal.ne' (fun n => (F.pattern n).one_lt_N) (hscale Qcard) F.energy_log
  have hτ : 0 ≤ τ / k := div_nonneg hs.2.2.1 hkReal.le
  constructor
  · obtain ⟨x, φ, hφ, hlim, hmem⟩ := energyRegion_subsequence_of_log_limits
      hs.1 hs.2.1 hτ (fun n => (Qcard n).pattern)
      hcardTime.1 hcardTime.2.1 hcardTime.2.2 hcardPos
    have hfirst : Tendsto (fun n => Real.logb (Qcard (φ n)).pattern.N
        ((Qcard (φ n)).pattern.ordinates.card : ℝ)) atTop (nhds x.1) := by
      simpa only [energyLogCoordinates, Function.comp_def] using
        (continuous_fst.tendsto x).comp hlim
    have hsecond : Tendsto (fun n => Real.logb (Qcard (φ n)).pattern.N
        (finsetAdditiveEnergy (Qcard (φ n)).pattern.ordinates : ℝ)) atTop (nhds x.2.1) := by
      simpa only [energyLogCoordinates, Function.comp_def] using
        ((continuous_fst.comp continuous_snd).tendsto x).comp hlim
    have hcardEq : x.1 = ρ / k := tendsto_nhds_unique hfirst (hcardLog.comp hφ.tendsto_atTop)
    have henergyLe : x.2.1 ≤ energy / k := by
      apply le_of_tendsto_of_tendsto' hsecond (henergyUpperLog.comp hφ.tendsto_atTop)
      intro n
      apply (Real.logb_le_logb (Qcard (φ n)).pattern.one_lt_N
        (hcardEnergyPos (φ n)) (F.energy_pos (φ n))).2
      exact_mod_cast (Qcard (φ n)).energy_le
    exact ⟨x.2.1, ⟨x.2.2, by simpa only [hcardEq] using hmem⟩, henergyLe⟩
  · obtain ⟨x, φ, hφ, hlim, hmem⟩ := energyRegion_subsequence_of_log_limits
      hs.1 hs.2.1 hτ (fun n => (Qenergy n).pattern)
      henergyTime.1 henergyTime.2.1 henergyTime.2.2 henergyCardPos
    have hfirst : Tendsto (fun n => Real.logb (Qenergy (φ n)).pattern.N
        ((Qenergy (φ n)).pattern.ordinates.card : ℝ)) atTop (nhds x.1) := by
      simpa only [energyLogCoordinates, Function.comp_def] using
        (continuous_fst.tendsto x).comp hlim
    have hsecond : Tendsto (fun n => Real.logb (Qenergy (φ n)).pattern.N
        (finsetAdditiveEnergy (Qenergy (φ n)).pattern.ordinates : ℝ)) atTop (nhds x.2.1) := by
      simpa only [energyLogCoordinates, Function.comp_def] using
        ((continuous_fst.comp continuous_snd).tendsto x).comp hlim
    have henergyEq : x.2.1 = energy / k := tendsto_nhds_unique hsecond (henergyLog.comp hφ.tendsto_atTop)
    have hcardLe : x.1 ≤ ρ / k := by
      apply le_of_tendsto_of_tendsto' hfirst (hcardUpperLog.comp hφ.tendsto_atTop)
      intro n
      apply (Real.logb_le_logb (Qenergy (φ n)).pattern.one_lt_N
        (henergyCardPos (φ n)) (F.card_pos (φ n))).2
      exact_mod_cast (Qenergy (φ n)).card_le
    exact ⟨x.1, ⟨x.2.2, by simpa only [henergyEq] using hmem⟩, hcardLe⟩

/-- Source-facing form of the repair: the two fifth coordinates are
separately existential and unrestricted. -/
theorem InLargeValueEnergyRegion.corrected_powering
    {σ τ ρ energy s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ energy s)
    (k : ℕ) (hk : 1 ≤ k) :
    (∃ eCard sCard : ℝ,
      InLargeValueEnergyRegion σ (τ / k) (ρ / k) eCard sCard ∧ eCard ≤ energy / k) ∧
    (∃ rEnergy sEnergy : ℝ,
      InLargeValueEnergyRegion σ (τ / k) rEnergy (energy / k) sEnergy ∧ rEnergy ≤ ρ / k) :=
  (cardinalityEnergyPoweringWitnesses_iff σ τ ρ energy k).mp
    (correctedCardinalityEnergyPowering σ τ ρ energy k hk ⟨s, h⟩)

/-- The powered Heath--Brown inequality now consumes actual input region
membership. Only the independently stated analytic Heath--Brown relation
remains a mathematical hypothesis; the powering witnesses are proved. -/
theorem InCardinalityEnergyRegion.powered_heathBrown_relation
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (k : ℕ) (hk : 1 ≤ k)
    (hHeathBrown : ∀ card e : ℝ, InCardinalityEnergyRegion σ (τ / k) card e →
      e ≤ heathBrownEnergyRHS σ (τ / k) card e) :
    energy / k ≤ heathBrownEnergyRHS σ (τ / k) (ρ / k) (energy / k) :=
  (correctedCardinalityEnergyPowering σ τ ρ energy k hk h).heathBrown_relation hHeathBrown

end TaoTrudgianYang2025
