import Mathlib.Tactic

/-! DUB-17/18 -> reverse original genus -> exact wild fiber orders.
If the fiber cardinal bound and total degree exhaust the same upper
bound on each local order, every local order attains that bound. This
finite equality case is used for the original j fibers in characteristics
two and three, with constants twelve and six. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section

theorem eq_const_of_finsum_and_card_bound {X : Type*} [Finite X]
    (f : X → ℤ) (n d : ℕ) (hcard : n * Nat.card X ≤ d)
    (hsum : (∑ᶠ x, f x) = (d : ℤ)) (hle : ∀ x, f x ≤ (n : ℤ)) :
    ∀ x, f x = (n : ℤ) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  rw [finsum_eq_sum_of_fintype] at hsum
  have hsumle := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hle x)
  have hbound : (n : ℤ) * Fintype.card X ≤ (d : ℤ) := by
    rw [Nat.card_eq_fintype_card] at hcard
    exact_mod_cast hcard
  have heq : (∑ x : X, f x) = ∑ _x : X, (n : ℤ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumle ⊢
    nlinarith
  intro x
  exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).mp heq x (Finset.mem_univ x)

end
end Dubon2026.SourceFunctionField.MarkedChart
