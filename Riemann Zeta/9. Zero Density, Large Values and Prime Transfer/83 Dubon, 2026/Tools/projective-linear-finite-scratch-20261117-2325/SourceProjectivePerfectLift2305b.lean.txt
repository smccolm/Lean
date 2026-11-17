import Dubon2026.FieldSL2Perfect
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! DUB-17/18 -> actual residual large image -> lifting projective containment.
Perfection of the existing SL₂ image removes the central scalar ambiguity in
projectivization. This does not assert an arithmetic large-image hypothesis. -/
namespace Dubon2026.SourceDickson
open scoped commutatorElement

private theorem commutator_central_mul {G : Type*} [Group G]
    (a b z w : G) (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hzcomm (c : G) : Commute z c := (Subgroup.mem_center_iff.mp hz c).symm
  have hwcomm (c : G) : Commute w c := (Subgroup.mem_center_iff.mp hw c).symm
  rw [commutatorElement_mul_left_eq_conj_mul,
    (hzcomm (w * b)).commutator_eq, mul_one,
    (hzcomm ⁅a, w * b⁆).eq, mul_assoc, mul_inv_cancel, mul_one,
    commutatorElement_mul_right_eq_mul_conj, (hwcomm a).symm.commutator_eq,
    one_mul, (hwcomm ⁅a, b⁆).eq, mul_assoc, mul_inv_cancel, mul_one]

/-- A perfect subgroup contained in a projective image is already contained in its linear lift. -/
theorem perfect_subgroup_le_of_center_quotient_map_le {G : Type*} [Group G]
    (S H : Subgroup G) [Group.IsPerfect S]
    (h : S.map (QuotientGroup.mk' (Subgroup.center G)) ≤
      H.map (QuotientGroup.mk' (Subgroup.center G))) : S ≤ H := by
  rw [← Subgroup.commutator_eq_self (H := S)]
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  obtain ⟨x, hx, heqx⟩ := h (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
  obtain ⟨y, hy, heqy⟩ := h (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
  have hz : a / x ∈ Subgroup.center G := QuotientGroup.eq_iff_div_mem.mp heqx.symm
  have hw : b / y ∈ Subgroup.center G := QuotientGroup.eq_iff_div_mem.mp heqy.symm
  have heq := commutator_central_mul x y (a / x) (b / y) hz hw
  rw [div_mul_cancel, div_mul_cancel] at heq
  rw [heq]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

end Dubon2026.SourceDickson
