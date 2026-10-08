import Dubon2026.BoundedL2Smoothness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Exact original L2 representatives of every bounded pointwise jet -/

namespace Dubon2026

noncomputable section
open MeasureTheory

/-- Actual bounded pointwise jets are exactly the iterated derivatives of the original L2 curve. -/
theorem iteratedDeriv_toLp_of_bounded_jet_family {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (J : ℕ → ℝ → X → ℂ)
    (hJ : ∀ n t, MemLp (J n t) 2 μ)
    (hd : ∀ n t x, HasDerivAt (fun u : ℝ => J n u x) (J (n + 1) t x) t)
    (hB : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖J n t x‖ ≤ C) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => (hJ 0 t).toLp (J 0 t)) =
      fun t : ℝ => (hJ n t).toLp (J n t) := by
  induction n with
  | zero => exact iteratedDeriv_zero
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    obtain ⟨C, hC0, hC⟩ := hB (n + 1)
    exact (hasDerivAt_toLp_of_uniform_derivative_bound (J n) (J (n + 1))
      (hJ n) (hJ (n + 1)) (hd n) hC0 hC t).deriv

/-- Every actual L2 jet has precisely its original pointwise jet as its almost-everywhere representative. -/
theorem iteratedDeriv_toLp_ae_of_bounded_jet_family {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (J : ℕ → ℝ → X → ℂ)
    (hJ : ∀ n t, MemLp (J n t) 2 μ)
    (hd : ∀ n t x, HasDerivAt (fun u : ℝ => J n u x) (J (n + 1) t x) t)
    (hB : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖J n t x‖ ≤ C) (n : ℕ) (t : ℝ) :
    ⇑(iteratedDeriv n (fun u : ℝ => (hJ 0 u).toLp (J 0 u)) t) =ᵐ[μ] J n t := by
  rw [iteratedDeriv_toLp_of_bounded_jet_family J hJ hd hB n]
  exact (hJ n t).coeFn_toLp

end
end Dubon2026
