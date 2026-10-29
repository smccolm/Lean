import Dubon2026.SourceCyclicOrbitClassification

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers. An invariant
surjection from the actual finite sign classes descends to the finite
cyclic orbit quotient. The already proved finite-period orbit criterion
supplies this cardinal bound, without a new orbit classification. -/
namespace Dubon2026.SourceFunctionField.MarkedTorsion
noncomputable section
open SourceManin SourceEllipticExceptional
variable {X Y : Type*} [Finite X]

theorem card_le_periodic_orbits_of_surjective
    (τ : Equiv.Perm X) (n : ℕ) (hn : 0 < n) (hτ : τ ^ n = 1)
    (f : X → Y) (hf : Function.Surjective f) (hinv : ∀ x, f (τ x) = f x) :
    Nat.card Y ≤ Nat.card (Orb τ) := by
  have hp (i : ℕ) (x : X) : f ((τ ^ i) x) = f x := by
    induction i with
    | zero => rfl
    | succ i hi =>
      rw [pow_succ', Equiv.Perm.mul_apply, hinv, hi]
  let g : Orb τ → Y := Quotient.lift f (by
    intro x y hxy
    obtain ⟨i, _, hi⟩ := (orbQ_eq_iff_pow_lt τ n hn hτ x y).mp (Quotient.sound hxy)
    rw [hi, hp])
  apply Nat.card_le_card_of_surjective g
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨orbQ τ x, rfl⟩

end
end Dubon2026.SourceFunctionField.MarkedTorsion
