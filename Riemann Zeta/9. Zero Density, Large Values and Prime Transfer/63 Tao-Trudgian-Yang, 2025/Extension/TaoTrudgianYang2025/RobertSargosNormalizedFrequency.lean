import TaoTrudgianYang2025.RobertSargosNormalizedSystem

/-! Integer support permits the normalized frequency scale max(1,Q/k),
including the large-coordinate-gcd range without dropping any solutions. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem RobertSargosReducedSystem.frequency_at_least_one {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p)
    (hH : 0 ≤ H) (hQ : 0 < Q) (hδ : 0 ≤ δ) :
    RobertSargosReducedSystem R H (max 1 Q) δ p := by
  have hq₁n : p.q₁ ≠ 0 := by
    have hn : (p.q₁:ℝ) ≠ 0 := abs_pos.mp (lt_of_lt_of_le hQ h.q₁_support.1)
    exact_mod_cast hn
  have hq₂n : p.q₂ ≠ 0 := by
    have hn : (p.q₂:ℝ) ≠ 0 := abs_pos.mp (lt_of_lt_of_le hQ h.q₂_support.1)
    exact_mod_cast hn
  have hq₁one : (1:ℝ) ≤ |(p.q₁:ℝ)| := by exact_mod_cast Int.one_le_abs hq₁n
  have hq₂one : (1:ℝ) ≤ |(p.q₂:ℝ)| := by exact_mod_cast Int.one_le_abs hq₂n
  refine ⟨h.r_ne_zero,h.r_bound,?_,?_,h.h₁_support,h.h₂_support,
    h.same_sign,h.d_ne_zero,h.linear,?_⟩
  · exact ⟨max_le hq₁one h.q₁_support.1,
      h.q₁_support.2.trans (mul_le_mul_of_nonneg_left (le_max_right 1 Q) (by norm_num))⟩
  · exact ⟨max_le hq₂one h.q₂_support.1,
      h.q₂_support.2.trans (mul_le_mul_of_nonneg_left (le_max_right 1 Q) (by norm_num))⟩
  · exact h.near.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hQ.le (le_max_right 1 Q) 2) (mul_nonneg hδ hH))

theorem RobertSargosReducedSystem.normalized_primitive {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p)
    (hH : 0 ≤ H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    {j k : ℕ} (hj : j = robertSargosCoefficientGcd p)
    (hk : k = robertSargosFrequencyGcd p) :
    RobertSargosPrimitiveSystem (R/j) (H/j) (max 1 (Q/k)) δ
      (robertSargosNormalize j k p) := by
  have hkp : (0:ℝ) < k := by exact_mod_cast (hk ▸ h.frequency_gcd_pos : 0 < k)
  have hn := (h.normalized hj hk).frequency_at_least_one
    (div_nonneg hH (Nat.cast_nonneg j)) (div_pos hQ hkp) hδ
  have hg := robertSargos_normalized_gcds p h.r_ne_zero h.d_ne_zero hj hk
  exact hn.to_primitive hg.2 hg.1

theorem robertSargos_normalized_scale_conditions {R H Q : ℝ} {j : ℕ} (k : ℕ)
    (hj : 0 < j) (hjR : (j:ℝ) ≤ R) (hRH : R ≤ H/2) :
    1 ≤ R/j ∧ 1 ≤ H/j ∧ 1 ≤ max 1 (Q/k) ∧ R/j ≤ (H/j)/2 := by
  have hjp : (0:ℝ) < j := by exact_mod_cast hj
  have hRp : 0 < R := lt_of_lt_of_le hjp hjR
  have hjH : (j:ℝ) ≤ H := by linarith
  refine ⟨(le_div_iff₀ hjp).mpr (by simpa using hjR),
    (le_div_iff₀ hjp).mpr (by simpa using hjH),le_max_left _ _,?_⟩
  have hm := div_le_div_of_nonneg_right hRH hjp.le
  calc
    R/j ≤ (H/2)/j := hm
    _ = _ := by ring

end TaoTrudgianYang2025

