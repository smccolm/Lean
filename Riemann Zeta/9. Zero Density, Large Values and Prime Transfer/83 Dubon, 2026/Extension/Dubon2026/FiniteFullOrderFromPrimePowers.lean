import Mathlib.GroupTheory.Exponent
import Mathlib.Data.Nat.Factorization.Basic

/-! # Full order from constructed primary orders

Mathlib's finite abelian exponent theorem combines the constructed primary
orders. This closes the finite-group assembly step for DUB-17's mixed-degree
original class, without introducing an auxiliary field of mixed degree.
-/
namespace Dubon2026

/-- A finite abelian group of order dividing `n` has an element of order `n`
if each prime-power divisor of `n` occurs as an element order. -/
theorem finiteAddCommGroup_exists_full_order_of_prime_powers
    (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ)
    (hcard : Nat.card A ∣ n)
    (hprimary : ∀ q t : ℕ, q.Prime → q ^ t ∣ n → ∃ x : A, addOrderOf x = q ^ t) :
    ∃ x : A, addOrderOf x = n := by
  have he : n ∣ AddMonoid.exponent A := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro q t hq hd
    obtain ⟨x, hx⟩ := hprimary q t hq hd
    exact hx ▸ AddMonoid.addOrder_dvd_exponent x
  obtain ⟨x, hx⟩ := AddMonoid.exists_addOrderOf_eq_exponent
    (AddMonoid.ExponentExists.of_finite (G := A))
  exact ⟨x, hx.trans (Nat.dvd_antisymm (AddGroup.exponent_dvd_nat_card.trans hcard) he)⟩

end Dubon2026
