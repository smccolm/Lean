import Dubon2026.SourceDihedralThreeOrbits

/-! DUB-17/18 -> reverse original genus -> characteristic-three fiber.
The already proved six-element orbit classification gives a lower bound
of six in every invariant fiber when the involution and cubic generator
have no fixed points. Only this finite counting consequence is needed. -/
namespace Dubon2026.SourceFunctionField.MarkedTorsion
noncomputable section
open SourceDihedralThree

theorem six_mul_card_fiber_le_of_free_dihedral
    {X Y : Type*} [Finite X] (a b : X → X)
    (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x)
    (hab : ∀ x, a (b x) = b (b (a x)))
    (hafree : ∀ x, a x ≠ x) (hbfree : ∀ x, b x ≠ x)
    (f : X → Y) (hf : Function.Surjective f)
    (hfa : ∀ x, f (a x) = f x) (hfb : ∀ x, f (b x) = f x) :
    6 * Nat.card Y ≤ Nat.card X := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Finite Y := Finite.of_surjective f hf
  letI : Fintype Y := Fintype.ofFinite Y
  have hcard (x : X) : (six a b x).card = 6 := by
    have hsmall : ¬ ((six a b x).card = 1 ∨ (six a b x).card = 2) :=
      fun h => hbfree x ((small_iff a b ha hb hab x).mp h)
    have hodd : ¬ ((six a b x).card = 1 ∨ (six a b x).card = 3) := by
      intro h
      rcases (mem_T b).mp ((odd_iff a b ha hb hab x).mp h) with h | h | h
      · exact hafree x h
      · apply hafree (b (b x))
        rw [abb a b hb hab x, h]
      · apply hafree (b x)
        rw [hab x, h, hb]
    rcases card_six_mem a b ha hb hab x with h | h | h | h <;> omega
  have hbound := Finset.mul_card_image_le_card_of_maps_to
    (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) 6 (fun y _ => ?_)
  · simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hbound
  obtain ⟨x, rfl⟩ := hf y
  rw [← hcard x]
  apply Finset.card_le_card
  intro z hz
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases (mem_six a b hb hab).mp hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [hfa, hfb]

end
end Dubon2026.SourceFunctionField.MarkedTorsion
