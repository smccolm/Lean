import Dubon2026.PrimitivePurityFromContinuation
import Dubon2026.PrimitiveFirstNonvanishing

/-! # Actual purity and Sato–Tate from higher symmetric continuation alone -/

namespace Dubon2026

noncomputable section
open Filter
open scoped Topology

/-- Higher symmetric holomorphy alone implies the actual good-prime coefficient bound.
The zeroth and second cases are provided by the proved actual continuations. -/
theorem primitive_prime_bound_of_higher_symmetric_holomorphy {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hcontinuation : ∀ r : ℕ, 3 ≤ r → ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s | 1 < s.re} ∧
      Set.EqOn F (primitiveSymmetricLFunction f r) {s | (r : ℝ) + 1 < s.re})
    {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) :
    ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 := by
  classical
  have hex (t : ℕ) : ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | 1 < s.re} ∧
      Set.EqOn F (primitiveSymmetricLFunction f (2 * t)) {s | (2 * t : ℕ) + 1 < s.re} := by
    rcases (by omega : t = 0 ∨ t = 1 ∨ 2 ≤ t) with h0 | h1 | h2
    · subst t
      refine ⟨primitiveSymmetricLFunction f 0, ?_, ?_⟩
      · simpa using primitive_higher_symmetric_differentiableOn_far f hk 0
      · intro s _
        rfl
    · subst t
      obtain ⟨F, hF, _, hm⟩ := primitive_second_symmetric_nonvanishing_continuation f hk
      refine ⟨F, hF.differentiableOn.mono (fun s hs => (show 1 < s.re from hs).le), ?_⟩
      intro s hs
      exact hm (by change 1 < s.re; norm_num at hs; linarith)
    · exact hcontinuation (2 * t) (by omega)
  choose H hH hm using hex
  exact primitive_prime_bound_of_even_continuation f hk H hH hm hp hpQ

/-- Once actual purity is established, analytic uniqueness extends the genuine far-half-plane
Euler matching to the whole open Euler half-plane. -/
theorem primitive_symmetric_continuation_eqOn_of_far {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F {s | 1 ≤ s.re})
    (hmatch : Set.EqOn F (primitiveSymmetricLFunction f r) {s | (r : ℝ) + 1 < s.re}) :
    Set.EqOn F (primitiveSymmetricLFunction f r) {s | 1 < s.re} := by
  have hF' : AnalyticOnNhd ℂ F {s | 1 < s.re} := hF.mono (fun s hs => (show 1 < s.re from hs).le)
  let z : ℂ := ((r : ℝ) + 2 : ℝ)
  have hz : z ∈ {s : ℂ | 1 < s.re} := by dsimp [z]; linarith [Nat.cast_nonneg (α := ℝ) r]
  have he : ∀ᶠ s : ℂ in 𝓝[≠] z, F s = primitiveSymmetricLFunction f r s := by
    have hh : ∀ᶠ s : ℂ in 𝓝 z, (r : ℝ) + 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [z]; linarith)
    filter_upwards [hh.filter_mono nhdsWithin_le_nhds] with s hs
    exact hmatch hs
  exact hF'.eqOn_of_preconnected_of_frequently_eq
    (primitiveSymmetricLFunction_analyticOnNhd f hbound r)
    (convex_halfSpace_re_gt 1).isPreconnected hz he.frequently

/-- The genuine Sato–Tate law follows from higher symmetric holomorphic nonvanishing
continuations matched only in their proved far convergence half-planes. Actual local purity,
the first two continuation cases, and the entire analytic deduction are proved internally. -/
theorem primitive_satoTate_of_higher_continuation_alone {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hcontinuation : ∀ r : ℕ, 3 ≤ r → ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (primitiveSymmetricLFunction f r) {s | (r : ℝ) + 1 < s.re}) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) := by
  have hb : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 := by
    intro p hp hpQ
    apply primitive_prime_bound_of_higher_symmetric_holomorphy f hk _ hp hpQ
    intro r hr
    obtain ⟨F, hF, _, hm⟩ := hcontinuation r hr
    exact ⟨F, hF.differentiableOn.mono (fun s hs => (show 1 < s.re from hs).le), hm⟩
  apply primitive_satoTate_of_higher_symmetric_L_continuation f hk hb
  intro r hr
  obtain ⟨F, hF, hne, hm⟩ := hcontinuation r hr
  exact ⟨F, hF, hne, primitive_symmetric_continuation_eqOn_of_far f hb r hF hm⟩

end
end Dubon2026
