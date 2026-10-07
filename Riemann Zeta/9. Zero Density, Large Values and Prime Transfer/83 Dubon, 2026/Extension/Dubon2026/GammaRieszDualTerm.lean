import Dubon2026.GammaRieszDifferenceBounds
import Dubon2026.LinearMeanPowerTail

/-! # Actual terms of the dual Riesz Gamma series and their coefficient powers -/

namespace Dubon2026

open Complex

noncomputable section

/-- The genuine coefficient-weighted term of the dual order-two Riesz series. -/
def gammaRieszDualTerm (a : ℕ → ℝ) (k A x : ℝ) (n : ℕ) : ℂ :=
  ((a n / (n : ℝ) : ℝ) : ℂ) * ((x : ℂ) ^ 2 * gammaRieszKernel k 2 (A * n * x))

/-- At index zero the genuine reciprocal coefficient forces the dual term to vanish. -/
theorem gammaRieszDualTerm_zero (a : ℕ → ℝ) (k A x : ℝ) : gammaRieszDualTerm a k A x 0 = 0 := by
  simp [gammaRieszDualTerm]

/-- Exact separation of the conductor, parameter and coefficient powers in the actual Mellin term. -/
theorem weighted_mellin_power_factor (a q : ℝ) {A n x : ℝ} (hA : 0 < A) (hn : 0 < n) (hx : 0 < x) :
    a / n * (A * n * x) ^ q = A ^ q * x ^ q * (a * n ^ (q - 1)) := by
  rw [Real.mul_rpow (mul_pos hA hn).le hx.le, Real.mul_rpow hA.le hn.le,
    Real.rpow_sub_one hn.ne']
  ring

/-- The actual dual term has the precise summable coefficient power, uniformly in the positive parameter. -/
theorem exists_gammaRieszDualTerm_bound {k A : ℝ} (hk : 2 ≤ k) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℝ) (x : ℝ) (n : ℕ), 0 ≤ a n → 0 < x → 1 ≤ n →
      ‖gammaRieszDualTerm a k A x n‖ ≤ C * x ^ (15 / 8 : ℝ) * (a n * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := exists_gammaRieszKernel_bound hk (by norm_num : (0 : ℝ) ≤ 2) (le_refl (2 : ℝ))
  norm_num at hb
  refine ⟨C * A ^ (-(1 / 8 : ℝ)), by positivity, ?_⟩
  intro a x n ha hx hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : x ^ 2 * x ^ (-(1 / 8 : ℝ)) = x ^ (15 / 8 : ℝ) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]
    norm_num
  rw [gammaRieszDualTerm, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hn0.le), abs_of_pos hx]
  calc
    _ ≤ (a n / n) * (x ^ 2 * (C * (A * n * x) ^ (-(1 / 8 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb _ (mul_pos (mul_pos hA hn0) hx))
        (sq_nonneg x)) (div_nonneg ha hn0.le)
    _ = C * x ^ 2 * (a n / n * (A * n * x) ^ (-(1 / 8 : ℝ))) := by ring
    _ = _ := by
      rw [weighted_mellin_power_factor _ _ hA hn0 hx]
      norm_num only [show -(1 / 8 : ℝ) - 1 = -(9 / 8 : ℝ) by norm_num]
      calc
        _ = C * A ^ (-(1 / 8 : ℝ)) * (x ^ 2 * x ^ (-(1 / 8 : ℝ))) *
          (a n * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by ring
        _ = _ := by rw [hp]

/-- The actual three-point difference of a dual term is its reciprocal coefficient times the genuine kernel difference. -/
theorem gammaRieszDualTerm_difference (a : ℕ → ℝ) (k A x h : ℝ) (n : ℕ) :
    gammaRieszDualTerm a k A (x + 2 * h) n - 2 * gammaRieszDualTerm a k A (x + h) n +
      gammaRieszDualTerm a k A x n =
        ((a n / (n : ℝ) : ℝ) : ℂ) * gammaRieszSecondDifference k (A * n) x h := by
  unfold gammaRieszDualTerm gammaRieszSecondDifference
  ring

end
end Dubon2026
