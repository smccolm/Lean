import Dubon2026.HigherBoundaryNonvanishing
import Dubon2026.HigherNonvanishingAtOne

/-! # Genuine local purity, nonvanishing and Sato–Tate from entire symmetric continuation -/

namespace Dubon2026

noncomputable section
open Filter
open scoped Topology

/-- Genuine entire positive-order symmetric continuations are automatically nonzero on
Re(s)>=1. Local purity, the actual mixed boundary inequality and the nonnegative augmented
Dirichlet series prove all three parts of the nonvanishing conclusion. -/
theorem primitive_symmetric_nonvanishing_of_entire_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ n, 0 < n → Differentiable ℂ (H n))
    (hmatch : ∀ n, 0 < n → Set.EqOn (H n) (primitiveSymmetricLFunction f n)
      {s | (n : ℝ) + 1 < s.re}) {r : ℕ} (hr : 0 < r) {s : ℂ} (hs : 1 ≤ s.re) :
    H r s ≠ 0 := by
  have hA (n : ℕ) (hn : 0 < n) : AnalyticOnNhd ℂ (H n) {s | 1 ≤ s.re} :=
    fun z _ => (hH n hn).analyticAt z
  by_cases hs1 : s = 1
  · subst s
    exact primitive_symmetric_one_ne_zero_of_entire_continuation f hk H hH hmatch hr
  rcases hs.eq_or_lt with he | hlt
  · have hy : s.im ≠ 0 := by
      intro hz
      apply hs1
      exact Complex.ext (by simpa using he.symm) (by simpa using hz)
    have hform : s = 1 + Complex.I * s.im := by apply Complex.ext <;> simp [he.symm]
    rw [hform]
    exact primitive_symmetric_nonreal_boundary_of_continuation f hk H hA hmatch hr hy
  · have hb : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 := by
      intro p hp hpQ
      apply primitive_prime_bound_of_higher_symmetric_holomorphy f hk _ hp hpQ
      intro n hn
      exact ⟨H n, (hH n (by omega)).differentiableOn, hmatch n (by omega)⟩
    rw [primitive_symmetric_continuation_eqOn_of_far f hb r (hA r hr) (hmatch r hr) hlt]
    exact primitiveSymmetricLFunction_ne_zero f hb r hlt

/-- Entire continuation of the actual positive symmetric Euler functions alone implies the
genuine weak Sato–Tate law. Purity and all closed-half-plane nonvanishing are consequences;
constructing the entire family for the original non-CM form remains an arithmetic obligation. -/
theorem primitive_satoTate_of_entire_symmetric_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ n, 0 < n → Differentiable ℂ (H n))
    (hmatch : ∀ n, 0 < n → Set.EqOn (H n) (primitiveSymmetricLFunction f n)
      {s | (n : ℝ) + 1 < s.re}) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) := by
  apply primitive_satoTate_of_higher_continuation_alone f hk
  intro r hr
  refine ⟨H r, fun s _ => (hH r (by omega)).analyticAt s, ?_, hmatch r (by omega)⟩
  intro s hs
  exact primitive_symmetric_nonvanishing_of_entire_continuation f hk H hH hmatch (by omega) hs

end
end Dubon2026
