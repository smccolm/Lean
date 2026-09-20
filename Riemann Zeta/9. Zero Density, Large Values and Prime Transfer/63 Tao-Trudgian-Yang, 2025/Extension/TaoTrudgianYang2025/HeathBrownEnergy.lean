import TaoTrudgianYang2025.HeathBrownEnergyFinite
import TaoTrudgianYang2025.EnergyLogLimits
import TaoTrudgianYang2025.CorrectedEnergyPowering

/-!
# Heath--Brown's energy relation and its corrected powered application

The proof consumes actual realizing patterns and the native second/fourth
moments. No energy-region inequality is assumed. Padding the physical
height to `max N T` is removed by exact max algebra, including `τ < 1`.
-/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

/-- Height padding does not change this exponent bound on the admissible
cardinality range. In particular the theorem remains valid below `τ=1`. -/
theorem heathBrownEnergyRHS_max_one
    (σ τ ρ e : ℝ) (hρ : ρ ≤ τ) :
    heathBrownEnergyRHS σ (max 1 τ) ρ e = heathBrownEnergyRHS σ τ ρ e := by
  by_cases hτ : τ ≤ 1
  · have hfirst : 5 / 4 * ρ + 1 / 2 ≤ max (ρ + 1) (2 * ρ) := by
      have := le_max_left (ρ + 1) (2 * ρ)
      linarith
    have hsecond : 3 / 4 * e + ρ + 1 / 2 ≤ max (e + 1) (4 * ρ) := by
      have h₁ := le_max_left (e + 1) (4 * ρ)
      have h₂ := le_max_right (e + 1) (4 * ρ)
      linarith
    have hfirstτ : 5 / 4 * ρ + τ / 2 ≤ max (ρ + 1) (2 * ρ) := by linarith
    have hsecondτ : 3 / 4 * e + ρ + τ / 2 ≤ max (e + 1) (4 * ρ) := by linarith
    simp only [heathBrownEnergyRHS, max_eq_left hτ, max_eq_left hfirst,
      max_eq_left hsecond, max_eq_left hfirstτ, max_eq_left hsecondτ]
  · rw [max_eq_right (le_of_not_ge hτ)]

private theorem heathBrown_exponent_sum (τ ρ e : ℝ) :
    max (max (2 * ρ + 1) (ρ + 2)) (5 / 4 * ρ + 1 / 2 * τ + 1) +
      max (max (4 * ρ + 1) (e + 2)) (3 / 4 * e + ρ + 1 / 2 * τ + 1) =
    2 + max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) +
      max (max (e + 1) (4 * ρ)) (3 / 4 * e + ρ + τ / 2) := by
  have hρ : ρ + 2 = (ρ + 1) + 1 := by ring
  have he : e + 2 = (e + 1) + 1 := by ring
  rw [hρ, he, max_add_add_right, max_add_add_right,
    max_add_add_right, max_add_add_right]
  rw [max_comm (2 * ρ) (ρ + 1), max_comm (4 * ρ) (e + 1)]
  ring_nf

/-- Actual realizing sequences satisfy the energy relation at the padded
height exponent. Uniform finite constants disappear only after the scale
tends to infinity. -/
theorem PoweringInputFamily.heathBrown_energy_padded
    {σ τ ρ e : ℝ} {D : ℕ → ℝ} (F : PoweringInputFamily σ τ ρ e D) :
    e ≤ heathBrownEnergyRHS σ (max 1 τ) ρ e := by
  let N : ℕ → ℝ := fun n => (F.pattern n).N
  let H : ℕ → ℝ := fun n => max (N n) (F.pattern n).T
  let R : ℕ → ℝ := fun n => ((F.pattern n).ordinates.card : ℝ)
  let E : ℕ → ℝ := fun n => (finsetAdditiveEnergy (F.pattern n).ordinates : ℝ)
  let V : ℕ → ℝ := fun n => (F.pattern n).V - 1
  have hN (n : ℕ) : 1 < N n := (F.pattern n).one_lt_N
  have hNpos (n : ℕ) : 0 < N n := zero_lt_one.trans (hN n)
  have hHpos (n : ℕ) : 0 < H n := (hNpos n).trans_le (le_max_left _ _)
  have hVpos (n : ℕ) : 0 < V n := sub_pos.mpr (F.value_gt_one n)
  have hNlog : Tendsto (fun n => Real.logb (N n) (N n)) atTop (nhds 1) := by
    simpa only [Real.logb_self_eq_one (hN _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  have hHlog := tendsto_logb_max hN hNpos (fun n => (F.pattern n).T_pos) hNlog F.time_log
  have hHtop : Tendsto H atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left (N n) (F.pattern n).T) F.scale_top
  have hVlog := tendsto_logb_sub_one N (fun n => (F.pattern n).V) σ
    F.scale_top F.value_top F.value_log
  let A : ℕ → ℝ := fun n => R n ^ 2 * N n + R n * N n ^ 2 +
    R n ^ (5 / 4 : ℝ) * H n ^ (1 / 2 : ℝ) * N n
  let B : ℕ → ℝ := fun n => R n ^ 4 * N n + E n * N n ^ 2 +
    E n ^ (3 / 4 : ℝ) * R n * H n ^ (1 / 2 : ℝ) * N n
  have hApos (n : ℕ) : 0 < A n := by
    dsimp only [A]
    have := F.card_pos n
    have := hNpos n
    have := hHpos n
    positivity
  have hBpos (n : ℕ) : 0 < B n := by
    dsimp only [B]
    have := F.card_pos n
    have := F.energy_pos n
    have := hNpos n
    have := hHpos n
    positivity
  let a : ℝ := max (max (2 * ρ + 1) (ρ + 2)) (5 / 4 * ρ + 1 / 2 * max 1 τ + 1)
  let b : ℝ := max (max (4 * ρ + 1) (e + 2)) (3 / 4 * e + ρ + 1 / 2 * max 1 τ + 1)
  have hAlog : Tendsto (fun n => Real.logb (N n) (A n)) atTop (nhds a) := by
    apply tendsto_logb_add hN F.scale_top
      (fun n => by have := F.card_pos n; have := hNpos n; positivity)
      (fun n => by have := F.card_pos n; have := hNpos n; have := hHpos n; positivity)
    · apply tendsto_logb_add hN F.scale_top
        (fun n => by have := F.card_pos n; have := hNpos n; positivity)
        (fun n => by have := F.card_pos n; have := hNpos n; positivity)
      · exact tendsto_logb_mul (fun n => pow_pos (F.card_pos n) 2) hNpos
          (tendsto_logb_pow 2 F.card_log) hNlog
      · convert tendsto_logb_mul F.card_pos (fun n => pow_pos (hNpos n) 2)
          F.card_log (tendsto_logb_pow 2 hNlog) using 1
        norm_num
    · exact tendsto_logb_mul (fun n => by have := F.card_pos n; have := hHpos n; positivity) hNpos
        (tendsto_logb_mul (fun n => Real.rpow_pos_of_pos (F.card_pos n) _)
          (fun n => Real.rpow_pos_of_pos (hHpos n) _)
          (tendsto_logb_rpow (5 / 4) F.card_pos F.card_log)
          (tendsto_logb_rpow (1 / 2) hHpos hHlog)) hNlog
  have hBlog : Tendsto (fun n => Real.logb (N n) (B n)) atTop (nhds b) := by
    apply tendsto_logb_add hN F.scale_top
      (fun n => by have := F.card_pos n; have := F.energy_pos n; have := hNpos n; positivity)
      (fun n => by have := F.card_pos n; have := F.energy_pos n; have := hNpos n; have := hHpos n; positivity)
    · apply tendsto_logb_add hN F.scale_top
        (fun n => by have := F.card_pos n; have := hNpos n; positivity)
        (fun n => by have := F.energy_pos n; have := hNpos n; positivity)
      · exact tendsto_logb_mul (fun n => pow_pos (F.card_pos n) 4) hNpos
          (tendsto_logb_pow 4 F.card_log) hNlog
      · convert tendsto_logb_mul F.energy_pos (fun n => pow_pos (hNpos n) 2)
          F.energy_log (tendsto_logb_pow 2 hNlog) using 1
        norm_num
    · exact tendsto_logb_mul
        (fun n => by have := F.card_pos n; have := F.energy_pos n; have := hHpos n; positivity) hNpos
        (tendsto_logb_mul (fun n => by have := F.card_pos n; have := F.energy_pos n; positivity)
          (fun n => Real.rpow_pos_of_pos (hHpos n) _)
          (tendsto_logb_mul (fun n => Real.rpow_pos_of_pos (F.energy_pos n) _)
            F.card_pos (tendsto_logb_rpow (3 / 4) F.energy_pos F.energy_log) F.card_log)
          (tendsto_logb_rpow (1 / 2) hHpos hHlog)) hNlog
  have hLlog := tendsto_logb_pow 2 (tendsto_logb_mul F.energy_pos
    (fun n => pow_pos (hVpos n) 2) F.energy_log (tendsto_logb_pow 2 hVlog))
  have hε (ε : ℝ) (hε : 0 < ε) :
      2 * (e + 2 * σ) ≤ ε * max 1 τ + a + b := by
    obtain ⟨C, H₀, hC, _, hbound⟩ := heathBrown_largeValuePattern_energy_squared ε hε
    have hClog : Tendsto (fun n => Real.logb (N n) C) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp F.scale_top)
    have hRlog := tendsto_logb_mul (fun n => by have := hHpos n; have := hApos n; positivity) hBpos
      (tendsto_logb_mul (fun n => mul_pos hC (Real.rpow_pos_of_pos (hHpos n) ε)) hApos
        (tendsto_logb_mul (fun _ => hC) (fun n => Real.rpow_pos_of_pos (hHpos n) ε)
          hClog (tendsto_logb_rpow ε hHpos hHlog)) hAlog) hBlog
    simp only [zero_add] at hRlog
    apply le_of_tendsto_of_tendsto hLlog hRlog
    filter_upwards [hHtop.eventually_ge_atTop H₀] with n hn
    have := F.energy_pos n
    have := hVpos n
    have := hHpos n
    have := hApos n
    have := hBpos n
    apply (Real.logb_le_logb (hN n) (by positivity) (by positivity)).2
    exact hbound (F.pattern n) (H n) hn (le_max_left _ _) (le_max_right _ _)
      (F.value_gt_one n)
  have hfinal : 2 * (e + 2 * σ) ≤ a + b := by
    have hlim := ((poweringAccuracy_tendsto.mul_const (max 1 τ)).add_const a).add_const b
    simp only [zero_mul, zero_add] at hlim
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      (fun n => hε _ (poweringAccuracy_pos n))
  have hexp := heathBrown_exponent_sum (max 1 τ) ρ e
  change a + b = _ at hexp
  rw [hexp] at hfinal
  unfold heathBrownEnergyRHS
  linarith

/-- The source Heath--Brown two-max relation, for every actual projected
region point and the full source parameter domain. -/
theorem InCardinalityEnergyRegion.heathBrown_relation
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    e ≤ heathBrownEnergyRHS σ τ ρ e := by
  obtain ⟨F⟩ := exists_powering_input_family h (fun _ => 1)
  obtain ⟨s, hs⟩ := h
  simpa only [heathBrownEnergyRHS_max_one σ τ ρ e hs.rho_le_tau] using
    F.heathBrown_energy_padded

/-- Five-coordinate source-facing form; there is no constraint on a
powered fifth coordinate and no assumed analytic relation. -/
theorem InLargeValueEnergyRegion.heathBrown_relation
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s) :
    e ≤ heathBrownEnergyRHS σ τ ρ e :=
  (show InCardinalityEnergyRegion σ τ ρ e from ⟨s, h⟩).heathBrown_relation

/-- The repaired powering theorem now feeds the proved analytic relation,
so the powered inequality has no remaining mathematical theorem parameter. -/
theorem InCardinalityEnergyRegion.heathBrown_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) :
    e / k ≤ heathBrownEnergyRHS σ (τ / k) (ρ / k) (e / k) :=
  h.powered_heathBrown_relation k hk (fun _ _ hregion => hregion.heathBrown_relation)

/-- The source three-branch simplification for `τ ≤ 3/2`. This is an
actual-region constraint ready for optimization, not an assumed polytope. -/
theorem InLargeValueEnergyRegion.heathBrown_small_height
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hτ : τ ≤ 3 / 2) :
    e ≤ max (max (3 * ρ + 1 - 2 * σ) (ρ + 4 - 4 * σ))
      (5 / 2 * ρ + (3 - 4 * σ) / 2) := by
  have hfirst : 5 / 4 * ρ + τ / 2 ≤ max (ρ + 1) (2 * ρ) := by
    have := le_max_left (ρ + 1) (2 * ρ)
    have := le_max_right (ρ + 1) (2 * ρ)
    linarith
  have hsecond : 3 / 4 * e + ρ + τ / 2 ≤ max (e + 1) (4 * ρ) := by
    have := le_max_left (e + 1) (4 * ρ)
    have := le_max_right (e + 1) (4 * ρ)
    linarith
  have hHB := h.heathBrown_relation
  simp only [heathBrownEnergyRHS, max_eq_left hfirst, max_eq_left hsecond] at hHB
  let B : ℝ := max (max (3 * ρ + 1 - 2 * σ) (ρ + 4 - 4 * σ))
    (5 / 2 * ρ + (3 - 4 * σ) / 2)
  have hB₁ : 3 * ρ + 1 - 2 * σ ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB₂ : ρ + 4 - 4 * σ ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hB₃ : 5 / 2 * ρ + (3 - 4 * σ) / 2 ≤ B := le_max_right _ _
  change e ≤ B
  rcases le_total (ρ + 1) (2 * ρ) with hcard | hcard <;>
    rcases le_total (e + 1) (4 * ρ) with henergy | henergy
  · rw [max_eq_right hcard, max_eq_right henergy] at hHB
    linarith
  · rw [max_eq_right hcard, max_eq_left henergy] at hHB
    have hσ := h.1
    linarith
  · rw [max_eq_left hcard, max_eq_right henergy] at hHB
    linarith
  · rw [max_eq_left hcard, max_eq_left henergy] at hHB
    linarith

/-- The small-height optimization constraint applied to the corrected
energy witness. It retains the original cardinality as an upper bound. -/
theorem InCardinalityEnergyRegion.heathBrown_small_height_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) (hτ : τ / k ≤ 3 / 2) :
    e / k ≤ max (max (3 * (ρ / k) + 1 - 2 * σ) (ρ / k + 4 - 4 * σ))
      (5 / 2 * (ρ / k) + (3 - 4 * σ) / 2) := by
  obtain ⟨r, ⟨s, hs⟩, hr⟩ := (correctedCardinalityEnergyPowering _ _ _ _ k hk h).2
  exact (hs.heathBrown_small_height hτ).trans
    (max_le_max (max_le_max (by linarith) (by linarith)) (by linarith))

end TaoTrudgianYang2025
