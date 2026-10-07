import Dubon2026.SymmetricEulerPolynomial
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Exact higher-order remainder of a genuine spectral Euler factor -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The exact part beyond the first degree in a local logarithmic Euler derivative. -/
def spectralEulerTail (w z : ℂ) : ℂ := (w * z) ^ 2 / (1 - w * z)

/-- A bounded spectral root gives a nonzero local denominator strictly inside the unit disc. -/
theorem spectralEulerDenominator_ne_zero {w z : ℂ} (hw : ‖w‖ ≤ 1) (hz : ‖z‖ < 1) :
    1 - w * z ≠ 0 := by
  have hm : ‖w * z‖ < 1 := calc
    ‖w * z‖ = ‖w‖ * ‖z‖ := norm_mul _ _
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg z)
    _ < 1 := by simpa using hz
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_one] at hn
  linarith

/-- The actual local logarithmic derivative is exactly its first coefficient plus the higher-order remainder. -/
theorem spectralEulerTail_identity {w z : ℂ} (hne : 1 - w * z ≠ 0) :
    w * z / (1 - w * z) = w * z + spectralEulerTail w z := by
  unfold spectralEulerTail
  field_simp [hne]
  ring

/-- A uniform smaller disc gives a quadratic bound for the complete higher-order remainder. -/
theorem norm_spectralEulerTail_le {w z : ℂ} {ρ : ℝ}
    (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ ρ) (hρ : ρ < 1) :
    ‖spectralEulerTail w z‖ ≤ ‖z‖ ^ 2 / (1 - ρ) := by
  have hm : ‖w * z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg z)
  have hd : 1 - ρ ≤ ‖1 - w * z‖ := by
    have he := norm_sub_norm_le (1 : ℂ) (w * z)
    simp only [norm_one] at he
    linarith
  have hs : ‖w * z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [norm_nonneg (w * z), norm_nonneg z]
  simp only [spectralEulerTail, norm_div, norm_pow]
  exact (div_le_div_of_nonneg_right hs (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr hρ) hd)

/-- Each actual prime Dirichlet coordinate is entire in the spectral variable. -/
theorem primeDirichletCoordinate_differentiable (p : Nat.Primes) :
    Differentiable ℂ (fun s : ℂ => ((p : ℕ) : ℂ) ^ (-s)) :=
  differentiable_id.neg.const_cpow (.inl (by exact_mod_cast p.property.ne_zero))

/-- On a positive right half-plane, every actual prime coordinate stays in one common smaller unit disc. -/
theorem norm_primeDirichletCoordinate_le (p : Nat.Primes) {a : ℝ} (ha : 0 < a)
    {s : ℂ} (hs : a ≤ s.re) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-a) ∧ (2 : ℝ) ^ (-a) < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
  refine ⟨?_, Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le)
    (neg_le_neg hs)).trans (Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast p.property.two_le) (by linarith))

/-- Every bounded local spectral tail is holomorphic on Re(s)>0 before summing over primes. -/
theorem spectralEulerTail_prime_differentiableAt (p : Nat.Primes) {w s : ℂ}
    (hw : ‖w‖ ≤ 1) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun t : ℂ => spectralEulerTail w (((p : ℕ) : ℂ) ^ (-t))) s := by
  have ht := primeDirichletCoordinate_differentiable p
  have hz := norm_primeDirichletCoordinate_le p hs le_rfl
  exact ((ht.differentiableAt.const_mul w).pow 2).div
    ((ht.differentiableAt.const_mul w).const_sub 1)
    (spectralEulerDenominator_ne_zero hw (hz.1.trans_lt hz.2))

end
end Dubon2026
