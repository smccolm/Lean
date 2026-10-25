import Dubon2026.SourceEllipticCharTwoFixedCounts
import Dubon2026.SourceEllipticCharTwoSignAction

/-! DUB-17/18 -> characteristic-two weighted exceptional census -> apply
the exact order-twelve orbit marks to the actual sign quotient. The proved
stabilizer coordinates imply that every quotient element squares or cubes
to one. No abstract exponent hypothesis is assumed for the actual group. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [CharP K 2]
attribute [local instance] charTwoSignSubgroup_normal

theorem mem_sign_of_u_one_s_zero
    (g : MulAction.stabilizer (VariableChange K) (ofJ0 K))
    (hu : (g.val.u : K) = 1) (hs : g.val.s = 0) : g ∈ charTwoSignSubgroup := by
  obtain ⟨_, hr, _, ht⟩ := (stabilizer_coordinates_iff g.val).mp
    (MulAction.mem_stabilizer_iff.mp g.property)
  simp only [hs, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 6 ≠ 0)] at hr ht
  have hm : g.val.t * (g.val.t + 1) = 0 := by linear_combination ht
  rw [mem_charTwoSignSubgroup_iff]
  rcases mul_eq_zero.mp hm with h0 | h1
  · left
    apply Subtype.ext
    exact VariableChange.ext (Units.ext hu) hr hs h0
  · right
    have ht1 : g.val.t = 1 := by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h1
    apply Subtype.ext
    rw [← epsilonChange_eq_negation]
    exact VariableChange.ext (Units.ext hu) hr hs ht1

theorem stabilizer_square_or_cube_mem_sign
    (g : MulAction.stabilizer (VariableChange K) (ofJ0 K)) :
    g ^ 2 ∈ charTwoSignSubgroup ∨ g ^ 3 ∈ charTwoSignSubgroup := by
  have hu3 := ((stabilizer_coordinates_iff g.val).mp
    (MulAction.mem_stabilizer_iff.mp g.property)).1
  by_cases hu : (g.val.u : K) = 1
  · left
    apply mem_sign_of_u_one_s_zero
    · rw [pow_two]
      change ((g.val * g.val).u : K) = 1
      simp [VariableChange.mul_def, hu]
    · rw [pow_two]
      change (g.val * g.val).s = 0
      simp [VariableChange.mul_def, hu, CharTwo.add_self_eq_zero]
  · right
    have hpoly : (g.val.u : K) ^ 2 + (g.val.u : K) + 1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hu)
      calc ((g.val.u : K) - 1) * ((g.val.u : K) ^ 2 + (g.val.u : K) + 1) =
          (g.val.u : K) ^ 3 - 1 := by ring
        _ = 0 := by rw [hu3, sub_self]
    apply mem_sign_of_u_one_s_zero
    · rw [pow_succ, pow_two]
      change (((g.val * g.val) * g.val).u : K) = 1
      simpa only [VariableChange.mul_def, Units.val_mul, pow_succ, pow_zero, one_mul] using hu3
    · rw [pow_succ, pow_two]
      change ((g.val * g.val) * g.val).s = 0
      simp only [VariableChange.mul_def]
      linear_combination g.val.s * hpoly

theorem charTwoSignQuotient_square_or_cube
    (g : (MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) :
    g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    rcases stabilizer_square_or_cube_mem_sign g with h | h
    · left
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr h
    · right
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr h

end
end Dubon2026.SourceEllipticCharTwo
