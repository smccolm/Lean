import Mathlib
import RamanujanPetersson.Autoformalized
import RamanujanPetersson.Theorem41

namespace RamanujanPetersson

/--
A Lean-generated witness-squeeze form of Theorem 2.1 from the source note.

This theorem isolates exactly the final deduction used in the paper's proof:
once one has complex numbers `αₚ, βₚ` summing to `aₚ` and both having norm
`p^((k - 1) / 2)`, the desired Ramanujan–Petersson bound follows.

The arithmetic/modular-form input producing such `αₚ, βₚ` is not encoded here;
it is tracked in the project blueprint and paper patch notes.
-/
theorem theorem21_witnessForm
    {aₚ αₚ βₚ : ℂ} {p k N : ℕ}
    (hp : Nat.Prime p) (hpnmidN : ¬ p ∣ N)
    (ha : aₚ = αₚ + βₚ)
    (hα : ‖αₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2))
    (hβ : ‖βₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2)) :
    ‖aₚ‖ ≤ 2 * (p : ℝ) ^ ((k - 1 : ℝ) / 2) := by
  rcases theorem41_purity_witnessForm hp hpnmidN hα hβ with ⟨hα', hβ'⟩
  simpa using witnessSqueeze ha hα' hβ'

end RamanujanPetersson
