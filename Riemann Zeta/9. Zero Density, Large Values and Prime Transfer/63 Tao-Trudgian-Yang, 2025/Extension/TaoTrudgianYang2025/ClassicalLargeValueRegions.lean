import TaoTrudgianYang2025.HeathBrownEnergyFinite
import TaoTrudgianYang2025.EnergyLogLimits
import TaoTrudgianYang2025.CorrectedEnergyPowering
import GuthMaynard.ClassicalLargeValues

/-!
# Classical large-value constraints on actual energy regions

The full Montgomery--Halász--Huxley finite estimate is transferred with the
closed-support endpoint loss explicit. Keeping both terms of its minimum
removes physical height padding even when the source exponent is below one.
-/

open Filter Topology
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Native classical large values on the actual closed-support source
patterns. Reflection, coefficient conjugation, and endpoint loss are proved. -/
theorem classical_largeValuePattern_estimate :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (P : LargeValuePattern) (H : ℝ), 1 ≤ H → P.N ≤ H → P.T ≤ H →
        1 < P.V →
        (P.ordinates.card : ℝ) ≤ C * H ^ ε *
          (P.N ^ 2 / (P.V - 1) ^ 2 + H *
            min (P.N / (P.V - 1) ^ 2) (P.N ^ 4 / (P.V - 1) ^ 6)) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := classical_montgomery_halasz_huxley_native ε hε
  refine ⟨C, hC, ?_⟩
  intro P H hH hNH hTH hV
  have hN : (P.scale : ℝ) ≤ H := by simpa only [P.N_eq_scale] using hNH
  have hcoeff : ∀ n ∈ dyadicInterval P.scale,
      ‖conjugateCoeffs P.reflectedCoeffs n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact P.reflectedCoeffs_one_bounded n
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩)
  have hbase : InBaseInterval H P.reflectedOrdinates := by
    intro t ht
    exact ⟨(P.reflectedOrdinates_inBaseInterval t ht).1,
      (P.reflectedOrdinates_inBaseInterval t ht).2.trans hTH⟩
  have hlarge : ∀ t ∈ P.reflectedOrdinates, P.V - 1 ≤
      ‖dirichletPoly P.scale (conjugateCoeffs P.reflectedCoeffs) t‖ := by
    intro t ht
    rw [← norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs]
    exact P.reflectedHalfOpen_large t ht
  have h := hbound P.scale H (P.V - 1) P.reflectedOrdinates
    (conjugateCoeffs P.reflectedCoeffs) P.scale_pos hH hN (by linarith)
    hcoeff P.reflectedOrdinates_isSeparated hbase hlarge
  simpa only [P.reflectedOrdinates_card, ← P.N_eq_scale] using h

/-- The exponent of the full classical finite estimate, before discarding
either branch of the minimum. -/
def classicalLargeValueExponent (σ τ : ℝ) : ℝ :=
  max (2 - 2 * σ) (τ + min (1 - 2 * σ) (4 - 6 * σ))

/-- The mean-square branch removes height padding exactly. -/
theorem classicalLargeValueExponent_max_one (σ τ : ℝ) :
    classicalLargeValueExponent σ (max 1 τ) = classicalLargeValueExponent σ τ := by
  by_cases hτ : τ ≤ 1
  · have hmin := min_le_left (1 - 2 * σ) (4 - 6 * σ)
    have hfirst : 1 + min (1 - 2 * σ) (4 - 6 * σ) ≤ 2 - 2 * σ := by linarith
    have hsecond : τ + min (1 - 2 * σ) (4 - 6 * σ) ≤ 2 - 2 * σ := by linarith
    simp only [classicalLargeValueExponent, max_eq_left hτ, max_eq_left hfirst,
      max_eq_left hsecond]
  · rw [max_eq_right (le_of_not_ge hτ)]

/-- Any actual positive-threshold family with linked physical logarithmic
limits satisfies the classical cardinality exponent bound. -/
theorem PoweringInputFamily.classical_cardinality
    {σ τ ρ e : ℝ} {D : ℕ → ℝ} (F : PoweringInputFamily σ τ ρ e D) :
    ρ ≤ classicalLargeValueExponent σ τ := by
  let N : ℕ → ℝ := fun n => (F.pattern n).N
  let H : ℕ → ℝ := fun n => max (N n) (F.pattern n).T
  let V : ℕ → ℝ := fun n => (F.pattern n).V - 1
  have hN (n : ℕ) : 1 < N n := (F.pattern n).one_lt_N
  have hNpos (n : ℕ) : 0 < N n := zero_lt_one.trans (hN n)
  have hHpos (n : ℕ) : 0 < H n := (hNpos n).trans_le (le_max_left _ _)
  have hVpos (n : ℕ) : 0 < V n := sub_pos.mpr (F.value_gt_one n)
  have hNlog : Tendsto (fun n => Real.logb (N n) (N n)) atTop (nhds 1) := by
    simpa only [Real.logb_self_eq_one (hN _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  have hHlog := tendsto_logb_max hN hNpos (fun n => (F.pattern n).T_pos) hNlog F.time_log
  have hVlog := tendsto_logb_sub_one N (fun n => (F.pattern n).V) σ
    F.scale_top F.value_top F.value_log
  let X : ℕ → ℝ := fun n => N n ^ 2 / V n ^ 2
  let Y : ℕ → ℝ := fun n => H n * min (N n / V n ^ 2) (N n ^ 4 / V n ^ 6)
  have hXpos (n : ℕ) : 0 < X n := div_pos (pow_pos (hNpos n) 2) (pow_pos (hVpos n) 2)
  have hYpos (n : ℕ) : 0 < Y n := by
    dsimp only [Y]
    have := hNpos n
    have := hHpos n
    have := hVpos n
    positivity
  have hXlog : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds (2 - 2 * σ)) := by
    convert tendsto_logb_div (fun n => pow_pos (hNpos n) 2) (fun n => pow_pos (hVpos n) 2)
      (tendsto_logb_pow 2 hNlog) (tendsto_logb_pow 2 hVlog) using 1
    norm_num
  have hYlog : Tendsto (fun n => Real.logb (N n) (Y n)) atTop
      (nhds (max 1 τ + min (1 - 2 * σ) (4 - 6 * σ))) := by
    apply tendsto_logb_mul hHpos (fun n => by have := hNpos n; have := hVpos n; positivity) hHlog
    apply tendsto_logb_min hN (fun n => by have := hNpos n; have := hVpos n; positivity)
      (fun n => by have := hNpos n; have := hVpos n; positivity)
    · exact tendsto_logb_div hNpos (fun n => pow_pos (hVpos n) 2)
        hNlog (tendsto_logb_pow 2 hVlog)
    · convert tendsto_logb_div (fun n => pow_pos (hNpos n) 4) (fun n => pow_pos (hVpos n) 6)
        (tendsto_logb_pow 4 hNlog) (tendsto_logb_pow 6 hVlog) using 1
      norm_num
  have hsum := tendsto_logb_add hN F.scale_top hXpos hYpos hXlog hYlog
  change Tendsto _ _ (nhds (classicalLargeValueExponent σ (max 1 τ))) at hsum
  rw [classicalLargeValueExponent_max_one] at hsum
  have hε (ε : ℝ) (hε : 0 < ε) : ρ ≤ ε * max 1 τ + classicalLargeValueExponent σ τ := by
    obtain ⟨C, hC, hbound⟩ := classical_largeValuePattern_estimate ε hε
    have hClog : Tendsto (fun n => Real.logb (N n) C) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp F.scale_top)
    have hRlog := tendsto_logb_mul (fun n => mul_pos hC (Real.rpow_pos_of_pos (hHpos n) ε))
      (fun n => add_pos (hXpos n) (hYpos n))
      (tendsto_logb_mul (fun _ => hC) (fun n => Real.rpow_pos_of_pos (hHpos n) ε)
        hClog (tendsto_logb_rpow ε hHpos hHlog)) hsum
    simp only [zero_add] at hRlog
    apply le_of_tendsto_of_tendsto' F.card_log hRlog
    intro n
    apply (Real.logb_le_logb (hN n) (F.card_pos n) (by
      have := hHpos n; have := hXpos n; have := hYpos n; positivity)).2
    exact hbound (F.pattern n) (H n) ((hN n).le.trans (le_max_left _ _))
      (le_max_left _ _) (le_max_right _ _) (F.value_gt_one n)
  have hlim := (poweringAccuracy_tendsto.mul_const (max 1 τ)).add_const
    (classicalLargeValueExponent σ τ)
  simp only [zero_mul, zero_add] at hlim
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun n => hε _ (poweringAccuracy_pos n))

theorem InCardinalityEnergyRegion.classical_cardinality
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ ≤ classicalLargeValueExponent σ τ := by
  obtain ⟨F⟩ := exists_powering_input_family h (fun _ => 1)
  exact F.classical_cardinality

theorem InCardinalityEnergyRegion.huxley_cardinality
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ ≤ max (2 - 2 * σ) (4 + τ - 6 * σ) := by
  apply h.classical_cardinality.trans
  apply max_le_max le_rfl
  have := min_le_right (1 - 2 * σ) (4 - 6 * σ)
  linarith

/-- Cardinality, not energy, is the coordinate preserved by this witness. -/
theorem InCardinalityEnergyRegion.huxley_cardinality_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) :
    ρ / k ≤ max (2 - 2 * σ) (4 + τ / k - 6 * σ) := by
  obtain ⟨energy, hregion, _⟩ := (correctedCardinalityEnergyPowering _ _ _ _ k hk h).1
  exact hregion.huxley_cardinality

end TaoTrudgianYang2025
