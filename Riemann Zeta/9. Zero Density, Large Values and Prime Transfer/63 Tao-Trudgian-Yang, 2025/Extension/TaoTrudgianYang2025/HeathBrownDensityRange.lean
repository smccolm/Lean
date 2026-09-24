import TaoTrudgianYang2025.HeathBrownLargeValues
import TaoTrudgianYang2025.ZeroDensityTransferCorollaries
import TaoTrudgianYang2025.ZetaPairNonexistence

/-! The exact Heath--Brown large-value theorem at the density cutoff. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem heathBrown_montgomery_range {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) (hupper : τ ≤ 11*σ-8) :
    IsLargeValueBound σ τ (2-2*σ) := by
  have hh := heathBrown_largeValueBound hσ hσ1 hτ
  simpa only [max_eq_left (show 10+τ-13*σ ≤ 2-2*σ by linarith)] using hh

theorem heathBrown_density_of_zeta_range {σ : ℝ}
    (hσ : 7/10 < σ) (hσ1 : σ < 1)
    (hzeta : ∀ τ ∈ Set.Ico (2 : ℝ) (4*(10*σ-7)/3),
      zetaLargeValueExponent σ τ = ⊥) :
    zeroDensityExponent σ ≤ ((3/(10*σ-7) : ℝ) : EReal) := by
  apply zeroDensityExponent_le_three_div_of_montgomery_range σ (10*σ-7)
    (by linarith) hσ1 (by linarith)
  · intro τ ht
    rw [hzeta τ ht]
    exact bot_le
  · intro τ ht
    exact largeValueExponent_le_of_bound (heathBrown_montgomery_range
      (by linarith) hσ1.le ht.1 (by linarith [ht.2]))

theorem heathBrown_density_classical_pair_range {σ : ℝ}
    (hσ : 7/10 < σ) (hσUpper : σ ≤ 19/22) :
    zeroDensityExponent σ ≤ ((3/(10*σ-7) : ℝ) : EReal) := by
  apply heathBrown_density_of_zeta_range hσ (by linarith)
  intro τ ht
  exact zetaLargeValueExponent_eq_bot_of_classical_pair
    (by linarith) (by linarith [ht.1]) (by linarith [ht.2])

theorem heathBrown_density_at_one :
    zeroDensityExponent 1 ≤ ((1 : ℝ) : EReal) := by
  have hi := ingham_isZeroDensityBound (σ := 1) (by norm_num) le_rfl
  have hb : IsZeroDensityBound 1 1 := by
    simpa only [IsZeroDensityBound,sub_self,mul_zero] using hi
  exact zeroDensityExponent_le_of_bound hb

theorem ExponentPair.heathBrown_density_of_old_pair
    (hpair : ExponentPair (3/40) (31/40)) {σ : ℝ}
    (hσ : 7/10 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((3/(10*σ-7) : ℝ) : EReal) := by
  by_cases heq : σ = 1
  · subst σ
    convert heathBrown_density_at_one using 1
    norm_num
  apply heathBrown_density_of_zeta_range hσ (lt_of_le_of_ne hσ1 heq)
  intro τ ht
  exact hpair.zetaLargeValueExponent_eq_bot_of_one_le_tau
    (by linarith) (by linarith [ht.1]) (by linarith [ht.2])

end TaoTrudgianYang2025

