import Dubon2026.PrimitiveFirstNonvanishing
import Mathlib.NumberTheory.LSeries.Linearity

/-! # Literal finite prefixes and positive Dirichlet tails -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- The actual finite prefix of a Dirichlet coefficient sequence. -/
def dirichletCoefficientHead (a : ℕ → ℂ) (N n : ℕ) : ℂ := if n < N then a n else 0

/-- The finite coefficient prefix has precisely its original finite Dirichlet sum at every point. -/
theorem dirichletCoefficientHead_hasSum (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    HasSum (LSeries.term (dirichletCoefficientHead a N) s)
      (∑ n ∈ Finset.range N, LSeries.term a s n) := by
  have hh : HasSum (LSeries.term (dirichletCoefficientHead a N) s)
      (∑ n ∈ Finset.range N, LSeries.term (dirichletCoefficientHead a N) s n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    have hn' : ¬n < N := by simpa only [Finset.mem_range] using hn
    simp [LSeries.term, dirichletCoefficientHead, hn']
  convert hh using 1
  apply Finset.sum_congr rfl
  intro n hn
  simp [LSeries.term, dirichletCoefficientHead, Finset.mem_range.mp hn]

/-- The L-series of a genuine finite coefficient prefix equals the original finite sum. -/
theorem dirichletCoefficientHead_LSeries (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeries (dirichletCoefficientHead a N) s = ∑ n ∈ Finset.range N, LSeries.term a s n :=
  (dirichletCoefficientHead_hasSum a N s).tsum_eq

/-- The genuine finite Dirichlet sum is entire, including the explicitly excluded index zero. -/
theorem dirichletCoefficientHead_differentiable (a : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (LSeries (dirichletCoefficientHead a N)) := by
  have he : LSeries (dirichletCoefficientHead a N) = fun s => ∑ n ∈ Finset.range N, LSeries.term a s n :=
    funext (dirichletCoefficientHead_LSeries a N)
  rw [he]
  intro s
  exact DifferentiableAt.fun_sum (fun n _ => (LSeries.hasDerivAt_term a n s).differentiableAt)

/-- Removing a finite actual prefix preserves coefficient nonnegativity. -/
theorem dirichletCoefficientTail_nonneg {a : ℕ → ℂ} (ha : 0 ≤ a) (N : ℕ) :
    0 ≤ a - dirichletCoefficientHead a N := by
  intro n
  by_cases hn : n < N
  · simp [dirichletCoefficientHead, hn]
  · simpa [dirichletCoefficientHead, hn] using ha n

/-- Removing a finite actual prefix preserves the exact abscissa of absolute convergence. -/
theorem dirichletCoefficientTail_abscissa (a : ℕ → ℂ) (N : ℕ) :
    LSeries.abscissaOfAbsConv (a - dirichletCoefficientHead a N) = LSeries.abscissaOfAbsConv a := by
  apply LSeries.abscissaOfAbsConv_congr'
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  simp [dirichletCoefficientHead, not_lt.mpr hn]

/-- Alternating nonnegative Taylor derivatives propagate positivity to the left along a real
segment within the actual complex disk of holomorphy. -/
theorem nonneg_of_iteratedDeriv_alternating_on_ball {F : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hF : DifferentiableOn ℂ F (Metric.ball c r))
    (hder : ∀ n : ℕ, 0 ≤ (-1) ^ n * iteratedDeriv n F c)
    (hzc : z ≤ c) (hz : z ∈ Metric.ball c r) : 0 ≤ F z := by
  have he : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n F c * (z - c) ^ n = F z :=
    Complex.taylorSeries_eq_on_ball' hz hF
  rw [← he]
  apply tsum_nonneg
  intro n
  have hcz : 0 ≤ c - z := sub_nonneg.mpr hzc
  have hid : (n.factorial : ℂ)⁻¹ * iteratedDeriv n F c * (z - c) ^ n =
      (n.factorial : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n F c) * (c - z) ^ n := by
    rw [show z - c = (-1 : ℂ) * (c - z) by ring, mul_pow]
    ring
  rw [hid]
  exact mul_nonneg (mul_nonneg (by positivity) (hder n)) (pow_nonneg hcz n)

end
end Dubon2026
