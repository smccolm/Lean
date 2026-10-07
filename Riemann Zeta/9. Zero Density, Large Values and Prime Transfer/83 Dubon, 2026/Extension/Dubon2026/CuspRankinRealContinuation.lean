import Dubon2026.Gamma0CuspContinuation
import Dubon2026.CuspRankinFactor
import Dubon2026.CuspRankinUnfolding

/-! # The actual real-axis bridge between cusp continuation and the normalized square series -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The true diagonal Petersson density is the coercion of its nonnegative norm. -/
theorem petersson_self_eq_ofReal_norm (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    petersson k f f z = (‖petersson k f f z‖ : ℂ) := by
  rw [norm_petersson_self]
  simp only [petersson, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.ofReal_mul, Complex.ofReal_zpow]

/-- At real parameters the actual normalized Rankin series is the coercion of its real positive sum. -/
theorem cuspRankinSeries_real {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (σ : ℝ) :
    cuspRankinSeries f (σ : ℂ) =
      ((∑' n : ℕ, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [cuspRankinSeries_eq_tsum, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

/-- The true continued Eisenstein cusp integral agrees with the exact Gamma factor times the actual Rankin series on the real convergence axis. -/
theorem gamma0CuspEisensteinContinuation_real {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {σ : ℝ} (hσ : 1 < σ) :
    gamma0CuspEisensteinContinuation f (σ : ℂ) =
      cuspRankinFactor k (σ : ℂ) * cuspRankinSeries f (σ : ℂ) := by
  rw [gamma0CuspEisensteinContinuation_eq_integral f hσ]
  have hE (z : ℍ) : ((gamma0Eisenstein Q (σ : ℂ) z).re : ℂ) = gamma0Eisenstein Q (σ : ℂ) z := by
    rw [gamma0Eisenstein_real_value, Complex.ofReal_re]
  have he : (fun z : ℍ => gamma0Eisenstein Q (σ : ℂ) z * petersson k f f z) =
      (fun z : ℍ => (((gamma0Eisenstein Q (σ : ℂ) z).re * ‖petersson k f f z‖ : ℝ) : ℂ)) := by
    funext z
    calc
      _ = gamma0Eisenstein Q (σ : ℂ) z * (‖petersson k f f z‖ : ℂ) :=
        congrArg (gamma0Eisenstein Q (σ : ℂ) z * ·) (petersson_self_eq_ofReal_norm k f z)
      _ = _ := by
        rw [Complex.ofReal_mul, hE]
  rw [he, integral_complex_ofReal, cusp_rankin_unfolding_integral f hk hσ,
    cuspRankinFactor_real, cuspRankinSeries_real, Complex.ofReal_mul]

end
end Dubon2026
