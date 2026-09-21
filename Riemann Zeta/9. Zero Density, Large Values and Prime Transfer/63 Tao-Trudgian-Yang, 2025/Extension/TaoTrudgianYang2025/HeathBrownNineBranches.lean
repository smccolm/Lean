import TaoTrudgianYang2025.HeathBrownEnergy

/-!
# Nine affine Heath--Brown branches at an independent power

The auxiliary scale is a positive ratio of integer powers. Its occurrence
is obtained by multiplying an actual energy-preserving witness inequality;
it is not a scaling assertion about the fifth energy-region coordinate.
-/

noncomputable section

namespace TaoTrudgianYang2025

def heathBrownNineBranch (σ t r a : ℝ) : Fin 9 → ℝ :=
  ![(4-4*σ)*a+r, ((3-4*σ)*a+5*r)/2,
    ((12-16*σ)*a+8*r+2*t)/5,
    (3-4*σ)*a+2*r, (1-2*σ)*a+3*r,
    ((8-16*σ)*a+12*r+2*t)/5,
    (3-4*σ)*a+5/4*r+t/2,
    (1-2*σ)*a+21/8*r+t/4,
    ((8-16*σ)*a+9*r+4*t)/5]

theorem exists_heathBrownNineBranch {σ t r e : ℝ}
    (h : e ≤ heathBrownEnergyRHS σ t r e) :
    ∃ i : Fin 9, e ≤ heathBrownNineBranch σ t r 1 i := by
  by_contra hnot
  push Not at hnot
  have h₀ := hnot 0
  have h₁ := hnot 1
  have h₂ := hnot 2
  have h₃ := hnot 3
  have h₄ := hnot 4
  have h₅ := hnot 5
  have h₆ := hnot 6
  have h₇ := hnot 7
  have h₈ := hnot 8
  change ((12-16*σ)*1+8*r+2*t)/5 < e at h₂
  change (3-4*σ)*1+2*r < e at h₃
  change (1-2*σ)*1+3*r < e at h₄
  change ((8-16*σ)*1+12*r+2*t)/5 < e at h₅
  change (3-4*σ)*1+5/4*r+t/2 < e at h₆
  change (1-2*σ)*1+21/8*r+t/4 < e at h₇
  change ((8-16*σ)*1+9*r+4*t)/5 < e at h₈
  norm_num [heathBrownNineBranch] at h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  have hstrict : heathBrownEnergyRHS σ t r e < e := by
    simp only [heathBrownEnergyRHS,
      mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
      add_max,max_add,max_lt_iff]
    repeat' constructor
    all_goals linarith
  exact (not_lt_of_ge h) hstrict

theorem heathBrownNineBranch_mono_card (σ t a : ℝ) (i : Fin 9) :
    Monotone (fun r => heathBrownNineBranch σ t r a i) := by
  intro r₁ r₂ hr
  fin_cases i <;> norm_num [heathBrownNineBranch] <;> linarith

theorem heathBrownNineBranch_rescale (σ τ ρ : ℝ) {k l : ℝ}
    (hk : k ≠ 0) (hl : l ≠ 0) (i : Fin 9) :
    (l/k)*heathBrownNineBranch σ (τ/l) (ρ/l) 1 i =
      heathBrownNineBranch σ (τ/k) (ρ/k) (l/k) i := by
  fin_cases i <;> norm_num [heathBrownNineBranch] <;> field_simp

theorem InCardinalityEnergyRegion.heathBrown_nine_branches_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∃ i : Fin 9, e/k ≤ heathBrownNineBranch σ (τ/k) (ρ/k) ((l:ℝ)/k) i := by
  obtain ⟨i,hi⟩ := exists_heathBrownNineBranch (h.heathBrown_powered l hl)
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlpos : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  refine ⟨i,?_⟩
  calc
    e/k = ((l:ℝ)/k)*(e/l) := by field_simp
    _ ≤ ((l:ℝ)/k)*heathBrownNineBranch σ (τ/l) (ρ/l) 1 i :=
      mul_le_mul_of_nonneg_left hi (div_nonneg hlpos.le hkpos.le)
    _ = _ := heathBrownNineBranch_rescale σ τ ρ hkpos.ne' hlpos.ne' i

theorem heathBrown_small_height_two_branches {σ r e : ℝ} (hr : r ≤ 1)
    (h : e ≤ max (max (3*r+1-2*σ) (r+4-4*σ))
      (5/2*r+(3-4*σ)/2)) :
    e ≤ max (r+4-4*σ) ((3-4*σ+5*r)/2) := by
  apply h.trans
  apply max_le
  · apply max_le
    · apply le_trans _ (le_max_right _ _)
      linarith
    · exact le_max_left _ _
  · apply le_trans _ (le_max_right _ _)
    ring_nf
    exact le_rfl

theorem InCardinalityEnergyRegion.heathBrown_two_branches_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) (hτ : τ/k ≤ 3/2) (hr : ρ/k ≤ 1) :
    e/k ≤ max (ρ/k+4-4*σ) ((3-4*σ+5*(ρ/k))/2) :=
  heathBrown_small_height_two_branches hr (h.heathBrown_small_height_powered k hk hτ)

end TaoTrudgianYang2025
