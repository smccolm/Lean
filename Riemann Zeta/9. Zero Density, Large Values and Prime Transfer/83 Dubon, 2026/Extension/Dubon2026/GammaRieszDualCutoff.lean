import Dubon2026.GammaRieszAllCutoffs
import Dubon2026.GammaRieszDualSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Dominated convergence for the actual coefficient-weighted Gamma cutoff series -/

namespace Dubon2026

open Complex Filter
open scoped Topology

noncomputable section

/-- The literal coefficient-weighted order-two Gamma series term at a finite symmetric cutoff. -/
def gammaRieszDualCutoffTerm (a : ℕ → ℝ) (k A x T : ℝ) (n : ℕ) : ℂ :=
  ((a n / (n : ℝ) : ℝ) : ℂ) *
    ((x : ℂ) ^ 2 * gammaRieszVerticalCutoff k 2 (A * n * x) (gammaRieszLine 2) T)

/-- The actual dual term has the precise summable coefficient power, uniformly in the positive parameter. -/
theorem exists_gammaRieszDualCutoffTerm_bound {k A : ℝ} (hk : 2 ≤ k) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℝ) (x T : ℝ) (n : ℕ), 0 ≤ a n → 0 < x → 0 ≤ T → 1 ≤ n →
      ‖gammaRieszDualCutoffTerm a k A x T n‖ ≤ C * x ^ (15 / 8 : ℝ) * (a n * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
  let C : ℝ := (gammaRieszCompactMass k 2 + 24 * gammaRieszConstant k 2) / Real.pi
  have hC : 0 < C := div_pos (by linarith [gammaRieszCompactMass_nonneg k 2, gammaRieszConstant_pos k 2]) Real.pi_pos
  have hb (y T : ℝ) (hy : 0 < y) (hT : 0 ≤ T) :
      ‖gammaRieszVerticalCutoff k 2 y (gammaRieszLine 2) T‖ ≤ C * y ^ (-(1 / 8 : ℝ)) := by
    simpa only [gammaRieszLine, show (3 / 8 : ℝ) - 2 / 4 = -(1 / 8 : ℝ) by norm_num] using
      norm_gammaRiesz_all_vertical_cutoffs_le hk (by norm_num : (0 : ℝ) ≤ 2) le_rfl hy hT
  refine ⟨C * A ^ (-(1 / 8 : ℝ)), by positivity, ?_⟩
  intro a x T n ha hx hT hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : x ^ 2 * x ^ (-(1 / 8 : ℝ)) = x ^ (15 / 8 : ℝ) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]
    norm_num
  rw [gammaRieszDualCutoffTerm, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hn0.le), abs_of_pos hx]
  calc
    _ ≤ (a n / n) * (x ^ 2 * (C * (A * n * x) ^ (-(1 / 8 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb _ T (mul_pos (mul_pos hA hn0) hx) hT)
        (sq_nonneg x)) (div_nonneg ha hn0.le)
    _ = C * x ^ 2 * (a n / n * (A * n * x) ^ (-(1 / 8 : ℝ))) := by ring
    _ = _ := by
      rw [weighted_mellin_power_factor _ _ hA hn0 hx]
      norm_num only [show -(1 / 8 : ℝ) - 1 = -(9 / 8 : ℝ) by norm_num]
      calc
        _ = C * A ^ (-(1 / 8 : ℝ)) * (x ^ 2 * x ^ (-(1 / 8 : ℝ))) *
          (a n * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by ring
        _ = _ := by rw [hp]

/-- The actual coefficient-weighted finite-contour series converges to the already constructed dual series, with a proved uniform summable majorant. -/
theorem tendsto_gammaRieszDualCutoffSeries {a : ℕ → ℝ} {k A B x : ℝ}
    (hk : 2 ≤ k) (hA : 0 < A) (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, a n) ≤ B * N) (hx : 0 < x) :
    Tendsto (fun T : ℝ => ∑' n : ℕ, gammaRieszDualCutoffTerm a k A x T n) atTop
      (𝓝 (gammaRieszDualSeries a k A x)) := by
  obtain ⟨C, hC, hCb⟩ := exists_gammaRieszDualCutoffTerm_bound hk hA
  have htail := (linearPowerTail_summable_bound ha hB hb
    (by norm_num : (1 : ℝ) < 9 / 8) (le_refl (1 : ℕ))).1
  have hpower : Summable (fun n : ℕ => a n * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
    apply htail.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)),
      if_pos (by omega : 1 < n)]
  change Tendsto _ atTop (𝓝 (∑' n : ℕ, gammaRieszDualTerm a k A x n))
  apply tendsto_tsum_of_dominated_convergence (hpower.mul_left (C * x ^ (15 / 8 : ℝ)))
  · intro n
    by_cases hn : n = 0
    · simp only [hn, gammaRieszDualCutoffTerm, gammaRieszDualTerm, Nat.cast_zero, div_zero,
        ofReal_zero, zero_mul]
      exact tendsto_const_nhds
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      exact ((tendsto_gammaRieszKernel hk (by norm_num : (0 : ℝ) ≤ 2) le_rfl
        (mul_pos (mul_pos hA hn0) hx)).const_mul ((x : ℂ) ^ 2)).const_mul ((a n / (n : ℝ) : ℝ) : ℂ)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT n
    by_cases hn : n = 0
    · simp only [hn, gammaRieszDualCutoffTerm, Nat.cast_zero, div_zero, ofReal_zero, zero_mul, norm_zero]
      have ha0 := ha 0
      positivity
    · exact hCb a x T n (ha n) hx hT (Nat.one_le_iff_ne_zero.mpr hn)

end
end Dubon2026
