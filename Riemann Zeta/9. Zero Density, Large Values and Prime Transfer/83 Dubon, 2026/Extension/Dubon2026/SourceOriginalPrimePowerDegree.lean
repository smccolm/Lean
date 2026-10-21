import Dubon2026.SourcePrimePowerRationalDegree

/-! DUB-17/18 -> numerical modular genus -> original j-map degree.
For every prime power, including level one, the literal internal j
coordinate of the original coefficient-extended field has degree
dedekindPsi. No nonmembership, generation or degree premise remains.
General composite levels and modular ramification are still required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem finrank_original_over_j_prime_power_eq_psi (p : ℕ) [hp : Fact p.Prime] (k : ℕ)
    (L : Type*) [Field L] [Algebra ℚ L] :
    Module.finrank (IntermediateField.adjoin L
      ({jOver (p ^ k) L} : Set (modularFunctionFieldOver (p ^ k) L)))
      (modularFunctionFieldOver (p ^ k) L) = SourceLevelProjective.dedekindPsi (p ^ k) := by
  rw [finrank_original_over_j_baseChange]
  cases k with
  | zero =>
    rw [pow_zero, original_level_one_field_eq, relfinrank_self, SourceLevelProjective.dedekindPsi_one]
  | succ k =>
    rw [original_prime_power_rational_relfinrank,
      SourceLevelProjective.dedekindPsi_prime_pow p (k + 1) hp.out (Nat.succ_ne_zero k)]
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

end
end Dubon2026.SourceFunctionField
