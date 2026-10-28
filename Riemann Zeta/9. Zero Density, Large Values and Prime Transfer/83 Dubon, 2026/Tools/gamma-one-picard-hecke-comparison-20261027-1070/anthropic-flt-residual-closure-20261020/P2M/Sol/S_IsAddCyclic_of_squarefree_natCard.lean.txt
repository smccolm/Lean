import Mathlib
import P2M.Util
namespace P2MW.S_IsAddCyclic_of_squarefree_natCard

set_option autoImplicit false

theorem solution
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A := by
  haveI : Finite A := Nat.finite_of_card_ne_zero hA.ne_zero
  rw [← isCyclic_multiplicative_iff]
  have hM : Squarefree (Nat.card (Multiplicative A)) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  haveI : IsZGroup (Multiplicative A) := IsZGroup.of_squarefree hM
  exact IsCyclic.of_exponent_eq_card (IsZGroup.exponent_eq_card (Multiplicative A))
