import Mathlib.GroupTheory.PGroup

/-! # A genuine central cyclic subgroup reduces the order of a finite p-group -/

namespace Dubon2026
noncomputable section

/-- Every nontrivial finite p-group has an actual nontrivial central cyclic
normal subgroup. Its actual quotient has strictly smaller order. -/
theorem pGroup_exists_central_cyclic_reduction
    {G : Type} [Group G] [Finite G] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    ∃ S : Subgroup G, S.Normal ∧ IsCyclic S ∧
      1 < Nat.card S ∧ S.index < Nat.card G := by
  haveI : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  obtain ⟨g, hg⟩ := exists_ne (1 : Subgroup.center G)
  let S : Subgroup G := Subgroup.zpowers g.val
  have hle : S ≤ Subgroup.center G := Subgroup.zpowers_le.mpr g.property
  have hnormal : S.Normal := ⟨fun x hx y => by
    have hc := Subgroup.mem_center_iff.mp (hle hx) y
    simpa only [hc, mul_inv_cancel_right] using hx⟩
  have hne : S ≠ ⊥ := by
    intro heq
    have hgmem : g.val ∈ S := Subgroup.mem_zpowers g.val
    rw [heq, Subgroup.mem_bot] at hgmem
    exact hg (Subtype.ext hgmem)
  have hcard : 1 < Nat.card S := S.one_lt_card_iff_ne_bot.mpr hne
  refine ⟨S, hnormal, inferInstance, hcard, ?_⟩
  rw [← S.card_mul_index]
  simpa only [one_mul] using
    Nat.mul_lt_mul_of_pos_right hcard (Nat.pos_of_ne_zero S.index_ne_zero_of_finite)

end
end Dubon2026
