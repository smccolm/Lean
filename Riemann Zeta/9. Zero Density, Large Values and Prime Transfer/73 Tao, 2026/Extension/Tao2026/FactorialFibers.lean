import Tao2026.FactorialIntervals

/-!
# Fibers of factorial squarefree components

This file isolates the exact arithmetic bridge through which the
Erdős--Selfridge theorem enters Tao's proof of Theorem 1.10.  Equality of two
factorial squarefree components is equivalent to the intervening product of
consecutive integers being a square.  The adjacent case is therefore exactly
the case in which the new endpoint itself is a square.
-/

namespace Tao2026

/-- For `a ≤ b`, two factorials have the same squarefree component exactly
when `(a+1)⋯b` is a square. -/
theorem squarefreeComponent_factorial_eq_iff_consecutiveProduct_square
    {a b : ℕ} (hab : a ≤ b) :
    squarefreeComponent a.factorial = squarefreeComponent b.factorial ↔
      ∃ r : ℕ, consecutiveProduct a (b - a) = r ^ 2 := by
  have hfactorial :
      a.factorial * consecutiveProduct a (b - a) = b.factorial := by
    simpa only [Nat.add_sub_of_le hab] using
      factorial_mul_consecutiveProduct a (b - a)
  constructor
  · intro hcomponents
    obtain ⟨m, hm⟩ :=
      (squarefreeComponent_eq_iff_mul_eq_sq
        (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)).mp hcomponents
    have htotal : a.factorial ^ 2 * consecutiveProduct a (b - a) = m ^ 2 := by
      calc
        a.factorial ^ 2 * consecutiveProduct a (b - a) =
            a.factorial *
              (a.factorial * consecutiveProduct a (b - a)) := by ring
        _ = a.factorial * b.factorial := by rw [hfactorial]
        _ = m ^ 2 := hm
    exact exists_eq_sq_of_sq_mul_eq_sq (Nat.factorial_ne_zero a)
      (consecutiveProduct_ne_zero a (b - a)) htotal
  · rintro ⟨r, hr⟩
    apply (squarefreeComponent_eq_iff_mul_eq_sq
      (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)).mpr
    refine ⟨a.factorial * r, ?_⟩
    calc
      a.factorial * b.factorial =
          a.factorial *
            (a.factorial * consecutiveProduct a (b - a)) := by rw [hfactorial]
      _ = a.factorial ^ 2 * consecutiveProduct a (b - a) := by ring
      _ = a.factorial ^ 2 * r ^ 2 := by rw [hr]
      _ = (a.factorial * r) ^ 2 := by ring

/-- Adjacent factorial squarefree components repeat exactly when the larger
index is a square. -/
theorem squarefreeComponent_factorial_succ_eq_iff_square (a : ℕ) :
    squarefreeComponent a.factorial =
        squarefreeComponent (a + 1).factorial ↔
      ∃ r : ℕ, a + 1 = r ^ 2 := by
  simpa only [Nat.add_sub_cancel_left, consecutiveProduct_one] using
    (squarefreeComponent_factorial_eq_iff_consecutiveProduct_square
      (Nat.le_add_right a 1))

end Tao2026
