import Dubon2026.Gamma0CuspEntire
import Dubon2026.CuspRankinResidue

/-! # A genuine analytic numerator cancelling the actual Rankin pole -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter Set
open scoped Topology

noncomputable section

/-- The actual entire lattice completion divided by the analytic nonzero factors other than s−1. -/
def cuspRankinPoleNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  gamma0CuspEntire f s / (s * gamma0CompletionFactor Q s * cuspRankinFactor k s)

/-- The genuine pole numerator is holomorphic throughout Re(s)>1/2, including at 1. -/
theorem differentiableAt_cuspRankinPoleNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (cuspRankinPoleNumerator f) s := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  have hshift : 0 < s.re + (k : ℝ) - 1 := by linarith
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  exact (differentiable_gamma0CuspEntire f s).div
    ((differentiableAt_id.mul (differentiableAt_gamma0CompletionFactor Q hs)).mul
      (differentiableAt_cuspRankinFactor k hshift))
    (mul_ne_zero (mul_ne_zero hs0 (gamma0CompletionFactor_ne_zero Q hs))
      (cuspRankinFactor_ne_zero k hshift))

/-- Away from its pole the analytic numerator is exactly (s−1) times the true Rankin continuation. -/
theorem cuspRankinPoleNumerator_eq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    cuspRankinPoleNumerator f s = (s - 1) * cuspRankinContinuation f s := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  have hshift : 0 < s.re + (k : ℝ) - 1 := by linarith
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  rw [cuspRankinPoleNumerator, gamma0CuspEntire_eq f hs0 hs1, cuspRankinContinuation,
    gamma0CuspEisensteinContinuation_eq_div]
  field_simp [hs0, gamma0CompletionFactor_ne_zero Q hs, cuspRankinFactor_ne_zero k hshift]

/-- The value of the genuine analytic numerator at the pole is the exact real Petersson residue. -/
theorem cuspRankinPoleNumerator_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    cuspRankinPoleNumerator f 1 = (cuspRankinResidue f : ℂ) := by
  have ht : Tendsto (cuspRankinPoleNumerator f) (𝓝[≠] (1 : ℂ)) (𝓝 (cuspRankinPoleNumerator f 1)) :=
    (differentiableAt_cuspRankinPoleNumerator f hk (s := 1) (by norm_num)).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds
  have hre : ∀ᶠ s : ℂ in 𝓝[≠] 1, 1 / 2 < s.re :=
    ((Complex.continuous_re.tendsto (1 : ℂ)).eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num))).filter_mono nhdsWithin_le_nhds
  have he : (fun s : ℂ => (s - 1) * cuspRankinContinuation f s) =ᶠ[𝓝[≠] 1]
      cuspRankinPoleNumerator f := by
    filter_upwards [hre, self_mem_nhdsWithin] with s hs hs1
    exact (cuspRankinPoleNumerator_eq f hk hs hs1).symm
  exact tendsto_nhds_unique ht ((cuspRankinContinuation_residue_real f hk).congr' he)

end
end Dubon2026
