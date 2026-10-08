import Dubon2026.RankinEulerPositivity

/-! # Genuine Rankin and symmetric-square nonvanishing on the boundary -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- Equality in the open right half-plane extends to any common continuous boundary point by a genuine horizontal limit. -/
theorem eq_at_closed_halfPlane_of_continuousAt {F G : ℂ → ℂ} {s : ℂ}
    (hs : 1 ≤ s.re) (hF : ContinuousAt F s) (hG : ContinuousAt G s)
    (he : Set.EqOn F G {z | 1 < z.re}) : F s = G s := by
  have ht : Tendsto (fun x : ℝ => s + (x : ℂ)) (𝓝[>] 0) (𝓝 s) := by
    have hh : ContinuousAt (fun x : ℝ => s + (x : ℂ)) 0 := by fun_prop
    simpa only [Complex.ofReal_zero, add_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hh : (fun x : ℝ => F (s + x)) =ᶠ[𝓝[>] 0] (fun x : ℝ => G (s + x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    apply he
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
    change 0 < x at hx
    linarith
  exact tendsto_nhds_unique (hF.tendsto.comp ht) ((hG.tendsto.comp ht).congr' hh.symm)

/-- The original Rankin convolution is nonzero at every nonreal point of Re(s)=1, by its proved actual Euler inequality. -/
theorem primitive_rankin_ne_zero_on_boundary {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1) :
    rankinConvolutionGlobalContinuation f.toCuspForm s ≠ 0 := by
  have hy : s.im ≠ 0 := by
    intro hi
    apply hs1
    exact Complex.ext (by simpa using hs) (by simpa using hi)
  have hs' : s = 1 + Complex.I * s.im := by
    apply Complex.ext <;> simp [hs]
  have h1 : 1 + Complex.I * (s.im : ℂ) ≠ 1 := by
    simpa only [← hs'] using hs1
  have h2 : 1 + Complex.I * ((2 * s.im : ℝ) : ℂ) ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at hi
    exact hy (by linarith)
  rw [hs']
  apply boundary_ne_zero_of_three_four_one (rankinConvolutionGlobal_isBigO_near_one f.toCuspForm)
    (differentiableAt_rankinConvolutionGlobalContinuation f.toCuspForm h1)
  · simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      differentiableAt_rankinConvolutionGlobalContinuation f.toCuspForm h2
  · intro x hx
    exact primitive_rankin_global_three_four_one f hk hx s.im

/-- The global entire Rankin numerator agrees with the original pole numerator on the full closed half-plane. -/
theorem rankinConvolutionEntireNumerator_eq_pole_on_closed {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) {s : ℂ} (hs : 1 ≤ s.re) :
    rankinConvolutionEntireNumerator f.toCuspForm s = rankinConvolutionPoleNumerator f.toCuspForm s := by
  apply eq_at_closed_halfPlane_of_continuousAt hs
    ((differentiable_rankinConvolutionEntireNumerator f.toCuspForm s).continuousAt)
    ((differentiableAt_rankinConvolutionPoleNumerator f.toCuspForm hk (by linarith)).continuousAt)
  intro z hz
  rw [rankinConvolutionEntireNumerator_eq_series f.toCuspForm hk.le hz,
    rankinConvolutionPoleNumerator_eq f.toCuspForm hk hz]

/-- The actual symmetric-square continuation is nonzero at every point of Re(s)=1. -/
theorem primitiveSecondContinuation_boundary_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : s.re = 1) :
    primitiveSecondContinuation f s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    exact primitiveSecondContinuation_one_ne_zero f hk
  have hn := primitive_rankin_ne_zero_on_boundary f hk hs hs1
  have hnum : rankinConvolutionEntireNumerator f.toCuspForm s ≠ 0 := by
    intro he
    apply hn
    rw [rankinConvolutionGlobalContinuation, he, zero_div]
  rw [rankinConvolutionEntireNumerator_eq_pole_on_closed f (by omega) hs.ge,
    rankinConvolutionPoleNumerator] at hnum
  rw [primitiveSecondContinuation]
  apply div_ne_zero
  · have hc := primitiveRankinBadCorrection_ne_zero f hk (s := s) (by rw [hs]; norm_num)
    have hh := mul_ne_zero hnum hc
    convert hh using 1
    ring
  · exact principal_pole_numerator_ne_zero Q hs.ge

/-- The genuine second symmetric Euler product now has a proved holomorphic nonvanishing continuation on the full closed half-plane, without Deligne. -/
theorem primitive_second_symmetric_nonvanishing_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (primitiveSymmetricLFunction f 2) {s | 1 < s.re} := by
  refine ⟨primitiveSecondContinuation f, primitiveSecondContinuation_analyticOnNhd f (by omega), ?_,
    fun _ hs => primitiveSecondContinuation_eq_symmetric f (by omega) hs⟩
  intro s hs
  rcases hs.eq_or_lt with he | hlt
  · exact primitiveSecondContinuation_boundary_ne_zero f hk he.symm
  · rw [primitiveSecondContinuation_eq_symmetric f (by omega) hlt]
    exact primitive_second_symmetric_ne_zero f (by omega) hlt

end
end Dubon2026
