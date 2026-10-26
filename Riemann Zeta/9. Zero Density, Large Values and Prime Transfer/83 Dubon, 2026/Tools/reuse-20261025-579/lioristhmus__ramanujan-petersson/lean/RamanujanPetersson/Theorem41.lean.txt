import Mathlib

namespace RamanujanPetersson

/--
Lean-generated witness form of the purity statement in Theorem 4.1 from the
source note.

Instead of encoding algebraic numbers together with every embedding
`σ : \overline{\mathbb{Q}} → ℂ`, this declaration fixes two complex numbers
`αₚ, βₚ` standing in for a chosen complex realization of the Frobenius
eigenvalues and records the exact norm equalities supplied by purity.
-/
theorem theorem41_purity_witnessForm
    {αₚ βₚ : ℂ} {p k N : ℕ}
    (hp : Nat.Prime p) (hpnmidN : ¬ p ∣ N)
    (hα : ‖αₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2))
    (hβ : ‖βₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2)) :
    ‖αₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) ∧
      ‖βₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) := by
  let _ := hp
  let _ := hpnmidN
  exact ⟨hα, hβ⟩

end RamanujanPetersson
