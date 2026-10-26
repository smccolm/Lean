import Mathlib

namespace RamanujanPetersson

/--
Lemma 5.1 from the source note:
if a complex number is written as a sum of two terms, each with norm at most `R`,
then its norm is at most `2 * R`.
-/
theorem rankTwoTraceBound {a α β : ℂ} {R : ℝ}
    (ha : a = α + β) (hα : ‖α‖ ≤ R) (hβ : ‖β‖ ≤ R) :
    ‖a‖ ≤ 2 * R := by
  rw [ha]
  calc
    ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le _ _
    _ ≤ R + R := add_le_add hα hβ
    _ = 2 * R := by ring

/--
Lean-friendly corollary of `rankTwoTraceBound` matching the witness–squeeze step in
the proof of the Ramanujan–Petersson bound: equality of the two spectral norms is
more than enough for the required inequality.
-/
theorem witnessSqueeze {a α β : ℂ} {R : ℝ}
    (ha : a = α + β) (hα : ‖α‖ = R) (hβ : ‖β‖ = R) :
    ‖a‖ ≤ 2 * R := by
  apply rankTwoTraceBound ha
  · simp [hα]
  · simp [hβ]

end RamanujanPetersson
