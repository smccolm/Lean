import Dubon2026.RankinConvolutionGlobal
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-! # Identification of the global Rankin continuation with its proved positive residue -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Filter Set
open scoped Topology

noncomputable section

/-- Analytic uniqueness identifies the actual entire numerator with the previously proved half-plane numerator. -/
theorem rankinConvolutionEntireNumerator_eq_poleNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : 1 / 2 < s.re) :
    rankinConvolutionEntireNumerator f s = rankinConvolutionPoleNumerator f s := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE : AnalyticOnNhd ℂ (rankinConvolutionEntireNumerator f) {s : ℂ | 1 / 2 < s.re} := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z _
    exact (differentiable_rankinConvolutionEntireNumerator f z).differentiableWithinAt
  have hP : AnalyticOnNhd ℂ (rankinConvolutionPoleNumerator f) {s : ℂ | 1 / 2 < s.re} := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    exact (differentiableAt_rankinConvolutionPoleNumerator f hk hz).differentiableWithinAt
  have hz : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he : ∀ᶠ z : ℂ in 𝓝[≠] (2 : ℂ),
      rankinConvolutionEntireNumerator f z = rankinConvolutionPoleNumerator f z := by
    filter_upwards [hz.filter_mono nhdsWithin_le_nhds] with z hz'
    rw [rankinConvolutionEntireNumerator_eq_series f hk.le hz', rankinConvolutionPoleNumerator_eq f hk hz']
  exact hE.eqOn_of_preconnected_of_frequently_eq hP (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | 1 / 2 < z.re} by norm_num) he.frequently hs

/-- At one the genuine entire numerator is exactly the previously constructed Rankin residue. -/
theorem rankinConvolutionEntireNumerator_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    rankinConvolutionEntireNumerator f 1 = (rankinConvolutionResidue f : ℂ) := by
  rw [rankinConvolutionEntireNumerator_eq_poleNumerator f hk (by norm_num), rankinConvolutionPoleNumerator_one f hk]

/-- The true global continuation has the actual positive Petersson Rankin residue at its only possible pole. -/
theorem rankinConvolutionGlobalContinuation_residue_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun s : ℂ => (s - 1) * rankinConvolutionGlobalContinuation f s) (𝓝[≠] 1)
      (𝓝 (rankinConvolutionResidue f : ℂ)) := by
  have ht : Tendsto (rankinConvolutionEntireNumerator f) (𝓝[≠] 1)
      (𝓝 (rankinConvolutionEntireNumerator f 1)) :=
    (differentiable_rankinConvolutionEntireNumerator f 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [rankinConvolutionEntireNumerator_one f hk] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ (1 : ℂ) := hs
  dsimp only [rankinConvolutionGlobalContinuation]
  field_simp [sub_ne_zero.mpr hs1]

end
end Dubon2026
