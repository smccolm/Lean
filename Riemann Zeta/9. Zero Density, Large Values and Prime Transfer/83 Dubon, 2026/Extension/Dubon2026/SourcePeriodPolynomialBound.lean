import Dubon2026.SourceEichlerTransformation
import Mathlib.Algebra.Polynomial.Roots

/-! Polynomial corrections in the original period-cohomology injectivity argument.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> modular Galois association -> original analytic H1 injectivity.
A coboundary changes the already constructed scalar Eichler integral by a
polynomial. At each cusp, periodicity makes that correction constant. This
supplies the boundedness step without a second construction of Eichler primitives.
SourcePeriodCohomologyInjective consumes this bound. Geometric comparison remains open.
-/

namespace Dubon2026
noncomputable section
open Complex Polynomial UpperHalfPlane

/-- A polynomial periodic on the upper half-plane with nonzero real period is constant. -/
theorem sourcePolynomial_eq_const_of_upperHalfPlane_periodic (p : ℂ[X]) {h : ℝ}
    (hh : h ≠ 0)
    (hper : ∀ τ : UpperHalfPlane, p.eval ((h : ℂ) + (τ : ℂ)) = p.eval (τ : ℂ)) :
    p = C (p.eval Complex.I) := by
  let τ : ℕ → UpperHalfPlane := fun n =>
    ⟨Complex.I + (n : ℂ) * (h : ℂ), by simp⟩
  have hi : Function.Injective (fun n : ℕ => (τ n : ℂ)) := by
    intro a b hab
    have hm : (a : ℂ) * (h : ℂ) = (b : ℂ) * (h : ℂ) := add_left_cancel hab
    exact_mod_cast (mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hh) hm)
  have he (n : ℕ) : p.eval (τ n : ℂ) = p.eval Complex.I := by
    induction n with
    | zero => simp [τ]
    | succ n ih =>
      have ht : (τ (n + 1) : ℂ) = (h : ℂ) + (τ n : ℂ) := by
        dsimp [τ]
        push_cast
        ring
      rw [ht, hper, ih]
  apply Polynomial.eq_of_infinite_eval_eq
  exact (Set.infinite_range_of_injective hi).mono (by
    rintro z ⟨n, rfl⟩
    simpa only [Polynomial.eval_C] using he n)

end
end Dubon2026
