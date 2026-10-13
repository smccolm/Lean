import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index

/-! # Containment of the actual subgroups of a finite cyclic group

Degree divisibility must give containment of the original unramified stages
inside their cyclic compositum. This subgroup calculation is the precise
Galois-correspondence input for constructing the characteristic-degree tower
used by DUB-17's unramified H2 and local-invariant support argument.
-/

namespace Dubon2026
noncomputable section

variable {G : Type} [Group G] [Finite G] [IsCyclic G]

/-- In the original finite cyclic group, a subgroup contains every element
whose power by that subgroup's actual order is one. -/
theorem finiteCyclicSubgroup_mem_of_pow_card (S : Subgroup G) (x : G)
    (hx : x ^ Nat.card S = 1) : x ∈ S := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let T := {y : G // y ^ Nat.card S = 1}
  let f : S → T := fun y => ⟨y.val, congrArg Subtype.val (pow_card_eq_one' (x := y))⟩
  have hf : Function.Injective f := by
    intro y z h
    have he : (y : G) = (z : G) := congrArg (fun t : T => t.val) h
    exact Subtype.ext he
  have hc : Nat.card T ≤ Nat.card S := by
    simpa only [T, Nat.card_eq_fintype_card, Fintype.card_subtype] using
      (IsCyclic.card_pow_eq_one_le (α := G) (n := Nat.card S) Nat.card_pos)
  obtain ⟨y, hy⟩ := (hf.bijective_of_nat_card_le hc).2 (⟨x, hx⟩ : T)
  have hy' : (y : G) = x := congrArg (fun t : T => t.val) hy
  exact hy' ▸ y.property

/-- Divisibility of the actual subgroup orders gives containment in the
same original cyclic group. No abstract replacement subgroup is chosen. -/
theorem finiteCyclicSubgroup_le_of_card_dvd (S T : Subgroup G)
    (h : Nat.card S ∣ Nat.card T) : S ≤ T := by
  intro x hx
  apply finiteCyclicSubgroup_mem_of_pow_card T x
  obtain ⟨d, hd⟩ := h
  rw [hd, pow_mul]
  have he : x ^ Nat.card S = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : S)))
  rw [he, one_pow]

/-- Reversed index divisibility gives original subgroup containment,
in the form required for the actual finite Galois correspondence. -/
theorem finiteCyclicSubgroup_le_of_index_dvd (S T : Subgroup G)
    (h : T.index ∣ S.index) : S ≤ T := by
  apply finiteCyclicSubgroup_le_of_card_dvd S T
  obtain ⟨d, hd⟩ := h
  refine ⟨d, ?_⟩
  have he : T.index * Nat.card T = T.index * (Nat.card S * d) := by
    calc
      T.index * Nat.card T = Nat.card G := T.index_mul_card
      _ = S.index * Nat.card S := S.index_mul_card.symm
      _ = T.index * (Nat.card S * d) := by rw [hd]; ac_rfl
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := T))) he

end
end Dubon2026
