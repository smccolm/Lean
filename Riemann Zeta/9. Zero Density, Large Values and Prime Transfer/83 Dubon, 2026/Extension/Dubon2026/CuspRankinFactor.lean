import Dubon2026.CuspRankinSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! # The exact Gamma factor of the actual normalized Rankin square series -/

namespace Dubon2026

noncomputable section

/-- The actual Mellin factor for automorphically normalized weight-k coefficients. -/
def cuspRankinFactor (k : ℤ) (s : ℂ) : ℂ :=
  ((4 * Real.pi : ℂ) ^ (-(s + (k : ℂ) - 1))) * Complex.Gamma (s + (k : ℂ) - 1)

/-- The Rankin Mellin factor is nonzero when the shifted Gamma argument has positive real part. -/
theorem cuspRankinFactor_ne_zero (k : ℤ) {s : ℂ} (hs : 0 < s.re + (k : ℝ) - 1) :
    cuspRankinFactor k s ≠ 0 := by
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by
      exact_mod_cast (mul_ne_zero (show (4 : ℝ) ≠ 0 by norm_num) Real.pi_ne_zero)))
  · apply Complex.Gamma_ne_zero_of_re_pos
    simpa using hs

/-- The exact Rankin Mellin factor is holomorphic in the positive shifted half-plane. -/
theorem differentiableAt_cuspRankinFactor (k : ℤ) {s : ℂ} (hs : 0 < s.re + (k : ℝ) - 1) :
    DifferentiableAt ℂ (cuspRankinFactor k) s := by
  have ha : DifferentiableAt ℂ (fun t : ℂ => t + (k : ℂ) - 1) s :=
    (differentiableAt_id.add_const _).sub_const _
  have hG : DifferentiableAt ℂ Complex.Gamma (s + (k : ℂ) - 1) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      have h := congrArg Complex.re hn
      simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re,
        Complex.neg_re, Complex.natCast_re] at h
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  exact (ha.neg.const_cpow (Or.inl (by
    exact_mod_cast (mul_ne_zero (show (4 : ℝ) ≠ 0 by norm_num) Real.pi_ne_zero)))).mul
    (hG.comp s ha)

/-- At real parameters the exact complex factor is the coercion of its real Gamma expression. -/
theorem cuspRankinFactor_real (k : ℤ) (σ : ℝ) :
    cuspRankinFactor k (σ : ℂ) =
      (((4 * Real.pi) ^ (-(σ + (k : ℝ) - 1)) * Real.Gamma (σ + (k : ℝ) - 1) : ℝ) : ℂ) := by
  unfold cuspRankinFactor
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), ← Complex.Gamma_ofReal]
  push_cast
  rfl

/-- At s=1 the weight-k factor is the positive real value (4*pi)^(-k)*Gamma(k). -/
theorem cuspRankinFactor_one (k : ℤ) :
    cuspRankinFactor k 1 = (((4 * Real.pi) ^ (-(k : ℝ)) * Real.Gamma (k : ℝ) : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_one, add_sub_cancel_left] using cuspRankinFactor_real k 1

/-- The real Rankin factor at the pole is strictly positive for positive weight. -/
theorem cuspRankinFactor_one_re_pos {k : ℤ} (hk : 0 < k) :
    0 < (cuspRankinFactor k 1).re := by
  rw [cuspRankinFactor_one, Complex.ofReal_re]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos (by exact_mod_cast hk))

end
end Dubon2026
