import Dubon2026.PrimitiveAugmentedEuler
import Dubon2026.FirstRankinPoleCancellation
import Dubon2026.PrimitiveFirstBoundary
import Mathlib.NumberTheory.LSeries.Positivity

/-! # Nonvanishing of the genuine first symmetric continuation at one and throughout Re(s)≥1 -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder Topology

/-- The actual first symmetric continuation cannot vanish at one: its hypothetical zero would
make a genuine nonnegative-coefficient mixed L-series entire with a real zero, contradicting
Mathlib's proved Dirichlet-series positivity theorem. -/
theorem primitiveFirstContinuation_one_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) : primitiveFirstContinuation f 1 ≠ 0 := by
  intro hz
  have hpos : 0 < firstRankinPoleCancellation f (((1 - (k : ℝ)) / 2 : ℝ) : ℂ) :=
    LSeries.positive_of_differentiable_of_eqOn
      (primitiveAugmentedCoefficient_nonneg f)
      (by rw [primitiveAugmentedCoefficient_one]; exact zero_lt_one)
      (firstRankinPoleCancellation_differentiable f (by omega))
      (primitiveAugmentedCoefficient_abscissa_le f hk)
      (fun s hs => (firstRankinPoleCancellation_eq_product f (by omega) hz (by exact lt_trans (by norm_num) hs)).trans
        (primitiveAugmentedCoefficient_LSeries f hk hs).symm)
      ((1 - (k : ℝ)) / 2)
  exact (ne_of_gt hpos) (firstRankinPoleCancellation_trivial_zero_of_zero_at_one f hk hz)

/-- The actual entire first symmetric continuation is nonzero on the full closed Euler half-plane. -/
theorem primitiveFirstContinuation_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : 1 ≤ s.re) :
    primitiveFirstContinuation f s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    exact primitiveFirstContinuation_one_ne_zero f hk
  exact primitiveFirstContinuation_ne_zero_of_ne_one f hk hs hs1

/-- The literal first symmetric Euler function has a proved entire continuation nonzero on
Re(s)≥1, without Deligne or an additional arithmetic hypothesis. -/
theorem primitive_first_symmetric_nonvanishing_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (primitiveSymmetricLFunction f 1) {s | 1 < s.re} := by
  refine ⟨primitiveFirstContinuation f, ?_, fun _ hs => primitiveFirstContinuation_ne_zero f hk hs,
    fun _ hs => primitiveFirstContinuation_eq_symmetric f (by omega) hs⟩
  exact fun s _ => (primitiveFirstContinuation_differentiable f (by omega)).analyticAt s

/-- The genuine Sato–Tate reduction now needs only orders at least three; the first two
continuation/nonvanishing cases are proved here. The good-prime bound and the remaining
higher continuation hypotheses stay explicit. -/
theorem primitive_satoTate_of_higher_symmetric_L_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hcontinuation : ∀ r : ℕ, 3 ≤ r → ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (primitiveSymmetricLFunction f r) {s | 1 < s.re}) :
    Filter.Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      Filter.atTop (𝓝 satoTateProbability) := by
  apply primitive_satoTate_of_symmetric_L_continuation f hbound
  intro r hr
  rcases (by omega : r = 1 ∨ r = 2 ∨ 3 ≤ r) with h1 | h2 | h3
  · subst r
    exact primitive_first_symmetric_nonvanishing_continuation f hk
  · subst r
    exact primitive_second_symmetric_nonvanishing_continuation f hk
  · exact hcontinuation r h3

end
end Dubon2026
