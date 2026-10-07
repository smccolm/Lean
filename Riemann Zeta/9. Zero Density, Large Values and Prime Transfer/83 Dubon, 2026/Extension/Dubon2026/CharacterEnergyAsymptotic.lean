import Dubon2026.CoprimePowerAsymptotic
import Dubon2026.CoprimeHarmonic
import Mathlib.Analysis.PSeries

/-! # All three regimes of the source's sharp Dirichlet-character energy lemma -/

namespace Dubon2026

open Filter
open scoped Topology

theorem coefficientEnergy_le_rpow_tsum {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 / 2 < σ) (N : ℕ) :
    coefficientEnergy a N σ ≤ ∑' n : ℕ, (n : ℝ) ^ (-2 * σ) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply le_trans ?_ (Summable.sum_le_tsum (Finset.Icc 1 N)
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-2 * σ)) hs)
  apply Finset.sum_le_sum
  intro n _
  have hb : ‖a n‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (a n), ha n]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-2 * σ))

theorem character_energy_left_asymptotic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : σ < 1 / 2) :
    Tendsto (fun N : ℕ => (coefficientEnergy (characterCoefficients χ) N σ -
      ((q.totient : ℝ) / q) * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
        (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0) := by
  have he : -2 * σ + 1 = 1 - 2 * σ := by ring
  simpa only [character_coefficientEnergy_eq, he] using
    tendsto_coprime_power_sum_error (NeZero.ne q) (r := -2 * σ) (by linarith)

theorem character_energy_center_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |coefficientEnergy (characterCoefficients χ) N (1 / 2) -
        ((q.totient : ℝ) / q) * Real.log N| ≤ C := by
  simpa only [character_coefficientEnergy_eq, show -2 * (1 / 2 : ℝ) = -1 by norm_num,
    Real.rpow_neg_one] using eventually_coprime_harmonic_error_bounded (NeZero.ne q)

theorem character_energy_right_bounded {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      0 ≤ coefficientEnergy (characterCoefficients χ) N σ ∧
        coefficientEnergy (characterCoefficients χ) N σ ≤ C := by
  refine ⟨∑' n : ℕ, (n : ℝ) ^ (-2 * σ), tsum_nonneg (fun n =>
    Real.rpow_nonneg (Nat.cast_nonneg n) _), ?_⟩
  intro N
  exact ⟨coefficientEnergy_nonneg _ _ _,
    coefficientEnergy_le_rpow_tsum (norm_characterCoefficients_le_one χ) hσ N⟩

end Dubon2026
