import Dubon2026.CuspRankinComplexContinuation

/-! # The genuine normalized Rankin series continuation from the actual cusp integral -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The actual normalized Rankin continuation obtained by removing the precise Mellin factor. -/
def cuspRankinContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  gamma0CuspEisensteinContinuation f s / cuspRankinFactor k s

/-- The constructed Rankin continuation agrees with the literal normalized square Dirichlet series throughout Re(s)>1. -/
theorem cuspRankinContinuation_eq_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    cuspRankinContinuation f s = cuspRankinSeries f s := by
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
  rw [cuspRankinContinuation, gamma0CuspEisensteinContinuation_eq_rankin f hk hs]
  exact mul_div_cancel_left₀ _ (cuspRankinFactor_ne_zero k (by linarith))

/-- For positive integral weight the actual Rankin continuation is holomorphic in Re(s)>1/2 away from 1. -/
theorem differentiableAt_cuspRankinContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (cuspRankinContinuation f) s := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  have hshift : 0 < s.re + (k : ℝ) - 1 := by linarith
  exact (differentiableAt_gamma0CuspEisensteinContinuation f hs hs1).div
    (differentiableAt_cuspRankinFactor k hshift) (cuspRankinFactor_ne_zero k hshift)

/-- The actual normalized square Rankin continuation has the precise Eisenstein-Petersson pole coefficient. -/
theorem cuspRankinContinuation_residue_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun s : ℂ => (s - 1) * cuspRankinContinuation f s) (𝓝[≠] 1)
      (𝓝 (((gamma0EisensteinResidue Q : ℂ) * cuspPetersson f f) / cuspRankinFactor k 1)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hshift : 0 < (1 : ℂ).re + (k : ℝ) - 1 := by
    simp only [Complex.one_re]
    linarith
  have hd : Tendsto (cuspRankinFactor k) (𝓝[≠] (1 : ℂ)) (𝓝 (cuspRankinFactor k 1)) :=
    (differentiableAt_cuspRankinFactor k hshift).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds
  have h := (gamma0CuspEisensteinContinuation_residue_one f).div hd (cuspRankinFactor_ne_zero k hshift)
  change Tendsto (fun s : ℂ => ((s - 1) * gamma0CuspEisensteinContinuation f s) / cuspRankinFactor k s)
    (𝓝[≠] 1) (𝓝 (((gamma0EisensteinResidue Q : ℂ) * cuspPetersson f f) / cuspRankinFactor k 1)) at h
  simpa only [cuspRankinContinuation, mul_div_assoc] using h

end
end Dubon2026
