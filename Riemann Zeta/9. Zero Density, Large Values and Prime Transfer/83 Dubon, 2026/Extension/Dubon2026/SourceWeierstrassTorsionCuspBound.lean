import Dubon2026.SourceWeierstrassNormalizedTorsion

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 character realization -> Picard/H1 and diamond comparison ->
differential realization -> rational Fourier structure -> cyclotomic
Fricke expansions. The actual torsion expansion is regrouped by its
finite exponent fibers and identified with the native q-expansion.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
No external theorem module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

lemma norm_wpNormSeries_le {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) :
    ∃ M : ℝ, ∀ τ : ℂ, 1 ≤ τ.im → ‖wpNormSeries N a₁ a₂ τ‖ ≤ M := by
  have hN : 0 < N := by omega
  set ρ : ℝ := Real.exp (-(2 * π * 1 / N)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff, neg_lt_zero]
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  obtain ⟨T, hT⟩ := summable_wpTail_majorant hρ0 hρ1
  set K : ℂ := zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 with hK
  refine ⟨‖K‖ + 1 / (1 - ρ) ^ 2 + ‖(1 / 12 : ℂ)‖ + T, fun τ hτ ↦ ?_⟩
  have hq : ‖qN N τ‖ ≤ ρ := norm_qN_le_of_le_im N hτ
  have hqa : ‖zetaN N ^ a₂ * qN N τ ^ a₁‖ ≤ ρ ^ a₁ := by
    rw [norm_mul, norm_pow, norm_zetaN, one_pow, one_mul, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hq a₁
  have hhead : ‖zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2‖ ≤
      ‖K‖ + 1 / (1 - ρ) ^ 2 := by
    have hKn : 0 ≤ ‖K‖ := norm_nonneg _
    have hρn : (0 : ℝ) ≤ 1 / (1 - ρ) ^ 2 := by positivity
    rcases Nat.eq_zero_or_pos a₁ with ha | ha
    · subst ha
      simp only [pow_zero, mul_one, ← hK]
      linarith
    · set r := zetaN N ^ a₂ * qN N τ ^ a₁ with hr
      have hr1 : ‖r‖ ≤ ρ := hqa.trans (pow_le_of_le_one hρ0 hρ1.le ha.ne')
      have h1r : 1 - ρ ≤ ‖1 - r‖ := by
        have := norm_sub_norm_le (1 : ℂ) r
        rw [norm_one] at this
        linarith
      have hpos : 0 < 1 - ρ := by linarith
      have : ‖r / (1 - r) ^ 2‖ ≤ 1 / (1 - ρ) ^ 2 := by
        rw [norm_div, norm_pow]
        have hr' : ‖r‖ ≤ 1 := hr1.trans hρ1.le
        have hden : (1 - ρ) ^ 2 ≤ ‖1 - r‖ ^ 2 := pow_le_pow_left₀ hpos.le h1r 2
        have hden0 : 0 < ‖1 - r‖ ^ 2 := lt_of_lt_of_le (by positivity) hden
        rw [div_le_div_iff₀ hden0 (by positivity), one_mul]
        nlinarith [norm_nonneg r]
      linarith
  have htail : ‖∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ‖ ≤ T :=
    tsum_of_norm_bounded hT fun p ↦ (norm_wpTail_le ha₁ a₂ p (by linarith)).trans (by gcongr)
  unfold wpNormSeries
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  linarith

theorem isBoundedAtImInfty_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : IsBoundedAtImInfty (wpNorm N a₁ a₂) := by
  obtain ⟨M, hM⟩ := norm_wpNormSeries_le ha₁ a₂
  rw [isBoundedAtImInfty_iff]
  exact ⟨M, 1, fun τ hτ ↦ by rw [wpNorm_eq ha₁ ha₂ h0]; exact hM τ hτ⟩


end
end Dubon2026.SourceFricke
