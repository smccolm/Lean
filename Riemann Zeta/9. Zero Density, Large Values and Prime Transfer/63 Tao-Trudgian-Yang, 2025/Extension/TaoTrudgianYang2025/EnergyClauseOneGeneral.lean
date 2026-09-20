import TaoTrudgianYang2025.ClassicalLargeValueRegions
import TaoTrudgianYang2025.HeathBrownEnergy
import TaoTrudgianYang2025.EnergyPoweringBounds

/-!
# General-energy optimization for Add-est (i)

This is the general large-value half of the source proof. It uses separate
corrected cardinality and energy witnesses, with no scaled fifth coordinate.
The zeta half and the final zero-energy estimate are separate obligations.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- Six affine alternatives after eliminating the self-referential energy
coordinate in Heath--Brown's inequality, when cardinality is at most one. -/
def heathBrownEnergyBranch (σ t r : ℝ) : Fin 6 → ℝ :=
  ![4 - 4 * σ + r, (3 - 4 * σ + 5 * r) / 2,
    (12 - 16 * σ + 8 * r + 2 * t) / 5,
    3 - 4 * σ + 5 / 4 * r + t / 2,
    1 - 2 * σ + 21 / 8 * r + t / 4,
    (8 - 16 * σ + 9 * r + 4 * t) / 5]

theorem exists_heathBrownEnergyBranch
    {σ t r e : ℝ} (hr : r ≤ 1) (h : e ≤ heathBrownEnergyRHS σ t r e) :
    ∃ i : Fin 6, e ≤ heathBrownEnergyBranch σ t r i := by
  by_contra hnot
  push Not at hnot
  have h₀ := hnot 0
  have h₁ := hnot 1
  have h₂ := hnot 2
  have h₃ := hnot 3
  have h₄ := hnot 4
  have h₅ := hnot 5
  change (12 - 16 * σ + 8 * r + 2 * t) / 5 < e at h₂
  change 3 - 4 * σ + 5 / 4 * r + t / 2 < e at h₃
  change 1 - 2 * σ + 21 / 8 * r + t / 4 < e at h₄
  change (8 - 16 * σ + 9 * r + 4 * t) / 5 < e at h₅
  norm_num [heathBrownEnergyBranch] at h₀ h₁
  have hcard : 2 * r ≤ r + 1 := by linarith
  have hstrict : heathBrownEnergyRHS σ t r e < e := by
    simp only [heathBrownEnergyRHS, max_eq_left hcard,
      mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      add_max, max_add, max_lt_iff]
    repeat' constructor
    all_goals linarith
  exact (not_lt_of_ge h) hstrict

theorem heathBrownEnergyBranch_mono_card (σ t : ℝ) (i : Fin 6) :
    Monotone (fun r => heathBrownEnergyBranch σ t r i) := by
  intro r₁ r₂ hr
  fin_cases i <;> norm_num [heathBrownEnergyBranch] <;> linarith

private theorem affine_le_mul_of_endpoints
    (a b t u v B : ℝ) (hat : a ≤ t) (htb : t ≤ b)
    (ha : u * a + v ≤ B * a) (hb : u * b + v ≤ B * b) :
    u * t + v ≤ B * t := by
  by_cases hu : u ≤ B
  · nlinarith [mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hu)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr htb) (sub_nonneg.mpr (le_of_not_ge hu))]

/-- The rate in the paper's two-piece general-energy intermediate bound. -/
def energyClauseOneGeneralRate (σ : ℝ) : ℝ :=
  max ((18 - 19 * σ) / (2 * (3 * σ - 1))) (7 * (1 - σ) / (3 * σ - 1))

theorem energyClauseOneGeneralRate_lower_piece {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 4 / 5) :
    energyClauseOneGeneralRate σ = (18 - 19 * σ) / (2 * (3 * σ - 1)) := by
  have hd : 0 < 3 * σ - 1 := by linarith
  apply max_eq_left
  apply (div_le_div_iff₀ hd (by positivity : 0 < 2 * (3 * σ - 1))).2
  nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 4 - 5 * σ)]

theorem energyClauseOneGeneralRate_upper_piece {σ : ℝ}
    (hlo : 4 / 5 ≤ σ) :
    energyClauseOneGeneralRate σ = 7 * (1 - σ) / (3 * σ - 1) := by
  have hd : 0 < 3 * σ - 1 := by linarith
  apply max_eq_right
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (3 * σ - 1)) hd).2
  nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 5 * σ - 4)]

private theorem generalRate_endpoint_bounds {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6) :
    6 * (1 - σ) ≤ energyClauseOneGeneralRate σ * (4 * σ - 2) ∧
      7 * (1 - σ) ≤ energyClauseOneGeneralRate σ * (3 * σ - 1) ∧
      9 - 19 / 2 * σ ≤ energyClauseOneGeneralRate σ * (3 * σ - 1) := by
  have hd : 0 < 3 * σ - 1 := by linarith
  have hfirst := le_max_left ((18 - 19 * σ) / (2 * (3 * σ - 1)))
    (7 * (1 - σ) / (3 * σ - 1))
  have hsecond := le_max_right ((18 - 19 * σ) / (2 * (3 * σ - 1)))
    (7 * (1 - σ) / (3 * σ - 1))
  change _ ≤ energyClauseOneGeneralRate σ at hfirst hsecond
  refine ⟨?_, ?_, ?_⟩
  · by_cases hs : σ ≤ 4 / 5
    · rw [energyClauseOneGeneralRate_lower_piece hlo hs]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : 0 < 2 * (3 * σ - 1))).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ σ - 3 / 4)
        (by linarith : 0 ≤ 4 / 5 - σ)]
    · rw [energyClauseOneGeneralRate_upper_piece (le_of_not_ge hs)]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hd).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - σ) (by linarith : 0 ≤ 5 * σ - 4)]
  · have hm := mul_le_mul_of_nonneg_right hsecond hd.le
    simpa only [div_mul_cancel₀ _ hd.ne'] using hm
  · have hm := mul_le_mul_of_nonneg_right hfirst hd.le
    have heq : (18 - 19 * σ) / (2 * (3 * σ - 1)) * (3 * σ - 1) =
        9 - 19 / 2 * σ := by
      rw [← div_div, div_mul_cancel₀ _ hd.ne']
      ring
    rwa [heq] at hm

/-- Exact finite endpoint certificate for all six Heath--Brown branches.
The cardinality cap is the minimum supplied by powers `k` and `k+1`. -/
theorem energyClauseOneGeneral_branch_bound
    {σ t r : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 4 * σ - 2 ≤ t) (hthi : t ≤ 6 * σ - 3)
    (hr₁ : r ≤ 3 - 3 * σ) (hr₂ : r ≤ 4 - 6 * σ + t)
    (i : Fin 6) :
    heathBrownEnergyBranch σ t r i ≤ energyClauseOneGeneralRate σ * t := by
  obtain ⟨hA, hB, hC⟩ := generalRate_endpoint_bounds hlo hhi
  by_cases ht : t ≤ 3 * σ - 1
  · apply (heathBrownEnergyBranch_mono_card σ t i hr₂).trans
    have hlow : heathBrownEnergyBranch σ (4 * σ - 2) (2 - 2 * σ) i ≤
        energyClauseOneGeneralRate σ * (4 * σ - 2) := by
      fin_cases i <;> norm_num [heathBrownEnergyBranch] <;> linarith
    have hmid : heathBrownEnergyBranch σ (3 * σ - 1) (3 - 3 * σ) i ≤
        energyClauseOneGeneralRate σ * (3 * σ - 1) := by
      fin_cases i <;> norm_num [heathBrownEnergyBranch] <;> linarith
    fin_cases i <;> norm_num [heathBrownEnergyBranch] at hlow hmid ⊢
    · convert affine_le_mul_of_endpoints (4 * σ - 2) (3 * σ - 1) t
          1 (8 - 10 * σ) (energyClauseOneGeneralRate σ) htlo ht (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (4 * σ - 2) (3 * σ - 1) t
          (5 / 2) ((23 - 34 * σ) / 2) (energyClauseOneGeneralRate σ) htlo ht (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (4 * σ - 2) (3 * σ - 1) t
          2 ((44 - 64 * σ) / 5) (energyClauseOneGeneralRate σ) htlo ht (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (4 * σ - 2) (3 * σ - 1) t
          (7 / 4) (8 - 23 / 2 * σ) (energyClauseOneGeneralRate σ) htlo ht (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (4 * σ - 2) (3 * σ - 1) t
          (23 / 8) (23 / 2 - 71 / 4 * σ) (energyClauseOneGeneralRate σ) htlo ht (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (4 * σ - 2) (3 * σ - 1) t
          (13 / 5) ((44 - 70 * σ) / 5) (energyClauseOneGeneralRate σ) htlo ht (by linarith) (by linarith) using 1
      ring
  · apply (heathBrownEnergyBranch_mono_card σ t i hr₁).trans
    have hmid : heathBrownEnergyBranch σ (3 * σ - 1) (3 - 3 * σ) i ≤
        energyClauseOneGeneralRate σ * (3 * σ - 1) := by
      fin_cases i <;> norm_num [heathBrownEnergyBranch] <;> linarith
    have hhigh : heathBrownEnergyBranch σ (6 * σ - 3) (3 - 3 * σ) i ≤
        energyClauseOneGeneralRate σ * (6 * σ - 3) := by
      fin_cases i <;> norm_num [heathBrownEnergyBranch] <;> nlinarith
    fin_cases i <;> norm_num [heathBrownEnergyBranch] at hmid hhigh ⊢
    · convert affine_le_mul_of_endpoints (3 * σ - 1) (6 * σ - 3) t
          0 (7 - 7 * σ) (energyClauseOneGeneralRate σ) (le_of_not_ge ht) hthi (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (3 * σ - 1) (6 * σ - 3) t
          0 (9 - 19 / 2 * σ) (energyClauseOneGeneralRate σ) (le_of_not_ge ht) hthi (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (3 * σ - 1) (6 * σ - 3) t
          (2 / 5) ((36 - 40 * σ) / 5) (energyClauseOneGeneralRate σ) (le_of_not_ge ht) hthi (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (3 * σ - 1) (6 * σ - 3) t
          (1 / 2) ((27 - 31 * σ) / 4) (energyClauseOneGeneralRate σ) (le_of_not_ge ht) hthi (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (3 * σ - 1) (6 * σ - 3) t
          (1 / 4) ((71 - 79 * σ) / 8) (energyClauseOneGeneralRate σ) (le_of_not_ge ht) hthi (by linarith) (by linarith) using 1
      ring
    · convert affine_le_mul_of_endpoints (3 * σ - 1) (6 * σ - 3) t
          (4 / 5) ((35 - 43 * σ) / 5) (energyClauseOneGeneralRate σ) (le_of_not_ge ht) hthi (by linarith) (by linarith) using 1
      ring

/-- Powers two and three cover the exact compact general-height interval. -/
theorem energyClauseOneGeneral_power_cover {σ τ : ℝ}
    (hlo : 8 * σ - 4 ≤ τ) (hhi : τ ≤ 2 * (8 * σ - 4)) :
    ∃ k : ℕ, (k = 2 ∨ k = 3) ∧
      (4 * σ - 2) * k ≤ τ ∧ τ ≤ (4 * σ - 2) * (k + 1 : ℕ) := by
  by_cases h : τ ≤ 3 * (4 * σ - 2)
  · refine ⟨2, Or.inl rfl, ?_, ?_⟩ <;> norm_num <;> linarith
  · refine ⟨3, Or.inr rfl, ?_, ?_⟩ <;> norm_num <;> linarith

/-- The paper's minimum cardinality cap comes from two different corrected
cardinality witnesses, at powers `k` and `k+1`. -/
theorem InCardinalityEnergyRegion.energyClauseOneGeneral_cardinality_cap
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hhi : σ ≤ 1) (k : ℕ) (hk : 2 ≤ k)
    (htlo : (4 * σ - 2) * k ≤ τ)
    (hthi : τ ≤ (4 * σ - 2) * (k + 1 : ℕ)) :
    ρ / k ≤ 3 - 3 * σ ∧ ρ / k ≤ 4 - 6 * σ + τ / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hksucc : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have htlo' : 4 * σ - 2 ≤ τ / k := (le_div_iff₀ hkpos).2 htlo
  have hthi' : τ / (k + 1 : ℕ) ≤ 4 * σ - 2 := (div_le_iff₀ hksucc).2 hthi
  have hlow := h.huxley_cardinality_powered k (by omega)
  have hhigh := h.huxley_cardinality_powered (k + 1) (by omega)
  rw [max_eq_right (by linarith : 2 - 2 * σ ≤ 4 + τ / k - 6 * σ)] at hlow
  rw [max_eq_left (by linarith : 4 + τ / (k + 1 : ℕ) - 6 * σ ≤ 2 - 2 * σ)] at hhigh
  refine ⟨?_, by linarith⟩
  apply (div_le_iff₀ hkpos).2
  have hmul := (div_le_iff₀ hksucc).1 hhigh
  have hknonneg : (0 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  push_cast at hmul
  nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hknonneg]

/-- The exact general-energy intermediate inequality in the proof of
`Add-est (i)`. This consumes real region membership, both corrected
cardinality witnesses, the corrected energy witness, and the finite
endpoint certificate. No analytic or optimization inequality is assumed. -/
theorem InCardinalityEnergyRegion.energyClauseOneGeneral
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 8 * σ - 4 ≤ τ) (hthi : τ ≤ 2 * (8 * σ - 4)) :
    e ≤ energyClauseOneGeneralRate σ * τ := by
  obtain ⟨k, hkcases, hlow, hhigh⟩ := energyClauseOneGeneral_power_cover htlo hthi
  have hk : 2 ≤ k := by rcases hkcases with rfl | rfl <;> omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨hr₁, hr₂⟩ := h.energyClauseOneGeneral_cardinality_cap (by linarith) k hk hlow hhigh
  have htlo' : 4 * σ - 2 ≤ τ / k := (le_div_iff₀ hkpos).2 hlow
  have hthi' : τ / k ≤ 6 * σ - 3 := by
    apply (div_le_iff₀ hkpos).2
    have hk' : (0 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    push_cast at hhigh
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * σ - 2) hk']
  obtain ⟨i, hi⟩ := exists_heathBrownEnergyBranch
    (by linarith : ρ / k ≤ 1) (h.heathBrown_powered k (by omega))
  have hbound := hi.trans (energyClauseOneGeneral_branch_bound hlo hhi htlo' hthi' hr₁ hr₂ i)
  have hm := (div_le_iff₀ hkpos).1 hbound
  simpa only [mul_assoc, div_mul_cancel₀ _ hkpos.ne'] using hm

/-- Exact first source piece, including the crossover by continuity. -/
theorem InLargeValueEnergyRegion.energyClauseOneGeneral_lower_piece
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 4 / 5)
    (htlo : 8 * σ - 4 ≤ τ) (hthi : τ ≤ 2 * (8 * σ - 4)) :
    e / τ ≤ (18 - 19 * σ) / (2 * (3 * σ - 1)) := by
  have hτ : 0 < τ := by linarith
  apply (div_le_iff₀ hτ).2
  simpa only [energyClauseOneGeneralRate_lower_piece hlo hhi] using
    (show InCardinalityEnergyRegion σ τ ρ e from ⟨s, h⟩).energyClauseOneGeneral
      hlo (by linarith) htlo hthi

/-- Exact second source piece on the full closed upper sigma interval. -/
theorem InLargeValueEnergyRegion.energyClauseOneGeneral_upper_piece
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 4 / 5 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 8 * σ - 4 ≤ τ) (hthi : τ ≤ 2 * (8 * σ - 4)) :
    e / τ ≤ 7 * (1 - σ) / (3 * σ - 1) := by
  have hτ : 0 < τ := by linarith
  apply (div_le_iff₀ hτ).2
  simpa only [energyClauseOneGeneralRate_upper_piece hlo] using
    (show InCardinalityEnergyRegion σ τ ρ e from ⟨s, h⟩).energyClauseOneGeneral
      (by linarith) hhi htlo hthi

/-- Compactness converts the actual-region optimization into the uniform
epsilon--delta energy bound, including its boundary exponent. -/
theorem energyClauseOneGeneral_uniform_bound
    {σ τ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 8 * σ - 4 ≤ τ) (hthi : τ ≤ 2 * (8 * σ - 4)) :
    IsLargeValueEnergyBound σ τ (energyClauseOneGeneralRate σ * τ) := by
  by_contra hnot
  obtain ⟨ρ, e, s, hregion, hlarge⟩ := energyRegion_exists_rhoStar_gt_of_not_bound
    (by linarith : 1 / 2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
  have hbound := (show InCardinalityEnergyRegion σ τ ρ e from ⟨s, hregion⟩).energyClauseOneGeneral
    hlo hhi htlo hthi
  linarith

/-- Corrected energy powering extends the certified compact interval to
all larger general heights. The separate zeta range is not claimed here. -/
theorem energyClauseOneGeneral_high_height_bound
    {σ τ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 8 * σ - 4 ≤ τ) :
    IsLargeValueEnergyBound σ τ (energyClauseOneGeneralRate σ * τ) := by
  exact isLargeValueEnergyBound_of_bounded_power_range
    (by linarith) (by linarith) (by linarith : 0 < 8 * σ - 4)
    (fun _ ht => energyClauseOneGeneral_uniform_bound hlo hhi ht.1 ht.2) τ htlo

/-- Exact two-function right side advertised in `Add-est (i)`. Defining
this function is not a proof of the zero-energy claim. -/
def energyClauseOnePublicRate (σ : ℝ) : ℝ :=
  max ((18 - 19 * σ) / (2 * (3 * σ - 1)))
    (4 * (10 - 9 * σ) / (5 * (4 * σ - 1)))

theorem energyClauseOnePublicRate_pos {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6) :
    0 < energyClauseOnePublicRate σ := by
  apply lt_of_lt_of_le _ (le_max_left _ _)
  exact div_pos (by linarith) (by linarith)

/-- The exact general-energy rate is dominated by the advertised maximum.
The crossover and denominator signs are checked over the full interval. -/
theorem energyClauseOneGeneralRate_le_public {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6) :
    energyClauseOneGeneralRate σ ≤ energyClauseOnePublicRate σ := by
  by_cases hs : σ ≤ 4 / 5
  · rw [energyClauseOneGeneralRate_lower_piece hlo hs]
    exact le_max_left _ _
  · rw [energyClauseOneGeneralRate_upper_piece (le_of_not_ge hs)]
    apply le_trans _ (le_max_right _ _)
    apply (div_le_div_iff₀ (by linarith : 0 < 3 * σ - 1)
      (by linarith : 0 < 5 * (4 * σ - 1))).2
    nlinarith [sq_nonneg (σ - 4 / 5)]

theorem energyClauseOneGeneral_public_rate_bound
    {σ τ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 8 * σ - 4 ≤ τ) :
    IsLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ := energyClauseOneGeneral_high_height_bound hlo hhi htlo ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTl hTu hVl hVu
  apply (hbound P hN hTl hTu hVl hVu).trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  apply Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
  have := mul_le_mul_of_nonneg_right (energyClauseOneGeneralRate_le_public hlo hhi)
    (by linarith : 0 ≤ τ)
  linarith

/-- Conditional final assembly with the general range fully discharged.
The remaining premise is the real zeta energy bound on `[1,8σ-4)`, not
the zero-energy conclusion. Endpoint one is intentional: lowering the
required zeta range to endpoint two is a separate, still-open proof. -/
theorem energyClauseOne_of_zeta_range
    {σ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (hZeta : ∀ τ ∈ Set.Ico (1 : ℝ) (8 * σ - 4),
      IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ)) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ / (1 - σ)) := by
  exact isZeroDensityEnergyBound_of_bounded_energy_ranges σ (energyClauseOnePublicRate σ)
    (8 * σ - 4) (by linarith) (by linarith)
    (energyClauseOnePublicRate_pos hlo hhi).le (by linarith) hZeta
    (fun _ ht => energyClauseOneGeneral_public_rate_bound hlo hhi ht.1)

end TaoTrudgianYang2025
