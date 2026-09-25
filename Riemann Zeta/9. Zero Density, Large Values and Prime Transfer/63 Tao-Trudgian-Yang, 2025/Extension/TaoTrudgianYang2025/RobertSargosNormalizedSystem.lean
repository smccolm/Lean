import TaoTrudgianYang2025.RobertSargosNormalizationGeometry

/-! Transport of the complete actual reduced source system under both exact gcd divisions. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem RobertSargosReducedSystem.normalized {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p)
    {j k : ℕ} (hj : j = robertSargosCoefficientGcd p)
    (hk : k = robertSargosFrequencyGcd p) :
    RobertSargosReducedSystem (R/j) (H/j) (Q/k) δ (robertSargosNormalize j k p) := by
  have hjp : 0 < j := hj ▸ h.coefficient_gcd_pos
  have hkp : 0 < k := hk ▸ h.frequency_gcd_pos
  have hjR : (0:ℝ) < j := by exact_mod_cast hjp
  have hkR : (0:ℝ) < k := by exact_mod_cast hkp
  have hdj : (j:ℤ) ∣ p.r ∧ (j:ℤ) ∣ p.h₁ ∧ (j:ℤ) ∣ p.h₂ := by
    rw [hj]
    exact integerTripleGcd_dvd _ _ _
  have hdk : (k:ℤ) ∣ p.d ∧ (k:ℤ) ∣ p.q₁ ∧ (k:ℤ) ∣ p.q₂ := by
    rw [hk]
    exact integerTripleGcd_dvd _ _ _
  have hcast (a : ℤ) (g : ℕ) (ha : (g:ℤ) ∣ a) :
      ((a/(g:ℤ):ℤ):ℝ) = (a:ℝ)/(g:ℝ) := by
    rw [Int.cast_div_charZero ha,Int.cast_natCast]
  constructor
  · exact fun he => h.r_ne_zero (Int.eq_zero_of_ediv_eq_zero hdj.1 he)
  · change |((p.r/(j:ℤ):ℤ):ℝ)| ≤ R/j
    rw [hcast p.r j hdj.1,abs_div,abs_of_pos hjR]
    exact div_le_div_of_nonneg_right h.r_bound hjR.le
  · simpa only [robertSargosNormalize,mul_div_assoc] using
      integer_ediv_abs_support hkp hdk.2.1 h.q₁_support
  · simpa only [robertSargosNormalize,mul_div_assoc] using
      integer_ediv_abs_support hkp hdk.2.2 h.q₂_support
  · simpa only [robertSargosNormalize,mul_div_assoc] using
      integer_ediv_interval_support hjp hdj.2.1 h.h₁_support
  · simpa only [robertSargosNormalize,mul_div_assoc] using
      integer_ediv_interval_support hjp hdj.2.2 h.h₂_support
  · have hs : (0:ℝ) < (p.q₁:ℝ)*p.q₂ := by exact_mod_cast h.same_sign
    have ht : (0:ℝ) < ((p.q₁/(k:ℤ):ℤ):ℝ)*((p.q₂/(k:ℤ):ℤ):ℝ) := by
      rw [hcast p.q₁ k hdk.2.1,hcast p.q₂ k hdk.2.2,div_mul_div_comm]
      exact div_pos hs (mul_pos hkR hkR)
    exact_mod_cast ht
  · exact fun he => h.d_ne_zero (Int.eq_zero_of_ediv_eq_zero hdk.1 he)
  · have hl : ((p.r/(j:ℤ):ℤ):ℝ)*((p.d/(k:ℤ):ℤ):ℝ)+
        ((p.h₁/(j:ℤ):ℤ):ℝ)*((p.q₁/(k:ℤ):ℤ):ℝ)-
        ((p.h₂/(j:ℤ):ℤ):ℝ)*((p.q₂/(k:ℤ):ℤ):ℝ) = 0 := by
      rw [hcast p.r j hdj.1,hcast p.d k hdk.1,
        hcast p.h₁ j hdj.2.1,hcast p.q₁ k hdk.2.1,
        hcast p.h₂ j hdj.2.2,hcast p.q₂ k hdk.2.2,
        robertSargos_linear_div _ _ _ _ _ _ _ _ hjR.ne' hkR.ne',
        h.linear_real,zero_div]
    exact_mod_cast hl
  · change |robertSargosReduced
        ((p.r/(j:ℤ):ℤ):ℝ) ((p.q₁/(k:ℤ):ℤ):ℝ) ((p.q₂/(k:ℤ):ℤ):ℝ)
        ((p.h₁/(j:ℤ):ℤ):ℝ) ((p.h₂/(j:ℤ):ℤ):ℝ) ((p.d/(k:ℤ):ℤ):ℝ)| ≤
        δ*(H/j)*(Q/k)^2
    rw [hcast p.r j hdj.1,hcast p.d k hdk.1,
      hcast p.h₁ j hdj.2.1,hcast p.q₁ k hdk.2.1,
      hcast p.h₂ j hdj.2.2,hcast p.q₂ k hdk.2.2,
      robertSargos_reduced_div _ _ _ _ _ _ _ _ hjR.ne' hkR.ne',
      abs_div,abs_of_pos (mul_pos hjR (sq_pos_of_pos hkR))]
    calc
      _ ≤ (δ*H*Q^2)/((j:ℝ)*(k:ℝ)^2) :=
        div_le_div_of_nonneg_right h.near (by positivity)
      _ = _ := by field_simp

end TaoTrudgianYang2025

