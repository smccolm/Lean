import Dubon2026.CuspRankinPoleNumerator
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # The actual continuous pole-subtracted Rankin function on the convergence boundary -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter Set
open scoped Topology

noncomputable section

/-- The genuine regular part of the actual Rankin continuation, including the derivative value at its removed pole. -/
def cuspRankinRegular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : ℂ → ℂ :=
  dslope (cuspRankinPoleNumerator f) 1

/-- The actual Rankin regular part is holomorphic throughout Re(s)>1/2 after removing its true residue. -/
theorem differentiableOn_cuspRankinRegular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    DifferentiableOn ℂ (cuspRankinRegular f) {s : ℂ | 1 / 2 < s.re} := by
  apply (Complex.differentiableOn_dslope
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} by norm_num))).mpr
  exact fun s hs => (differentiableAt_cuspRankinPoleNumerator f hk hs).differentiableWithinAt

/-- The actual removed-pole Rankin function is continuous on the complete closed convergence boundary. -/
theorem continuousOn_cuspRankinRegular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    ContinuousOn (cuspRankinRegular f) {s : ℂ | 1 ≤ s.re} := by
  apply (differentiableOn_cuspRankinRegular f hk).continuousOn.mono
  intro s hs
  change 1 ≤ s.re at hs
  change 1 / 2 < s.re
  linarith

/-- In Re(s)>1 this actual continuous boundary extension is precisely the literal Rankin series minus its proved pole. -/
theorem cuspRankinRegular_eq_series_sub_pole {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    cuspRankinRegular f s = cuspRankinSeries f s - (cuspRankinResidue f : ℂ) / (s - 1) := by
  have hs1 : s ≠ 1 := by intro h; simp only [h, Complex.one_re] at hs; linarith
  rw [cuspRankinRegular, dslope_of_ne _ hs1, slope, smul_eq_mul, vsub_eq_sub,
    cuspRankinPoleNumerator_one f hk, cuspRankinPoleNumerator_eq f hk (by linarith) hs1,
    cuspRankinContinuation_eq_series f hk.le hs]
  field_simp [sub_ne_zero.mpr hs1]

end
end Dubon2026
