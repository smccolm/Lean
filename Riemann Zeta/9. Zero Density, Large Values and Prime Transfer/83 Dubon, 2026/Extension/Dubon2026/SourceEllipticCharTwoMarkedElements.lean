import Dubon2026.SourceEllipticCharTwoSignExponent

/-! DUB-17/18 -> weighted characteristic-two exceptional census. The two
actual automorphisms used in the fixed-subgroup counts descend to nontrivial
elements of orders two and three in the actual sign quotient. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [CharP K 2]
attribute [local instance] charTwoSignSubgroup_normal
variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)

theorem signProjection_quartic_ne_one :
    charTwoSignProjection (quarticStabilizer ω hω) ≠ 1 := by
  intro h
  have hm := (QuotientGroup.eq_one_iff _).mp h
  rcases (mem_charTwoSignSubgroup_iff _).mp hm with h | h
  · have hr := congrArg (fun g : MulAction.stabilizer (VariableChange K) (ofJ0 K) => g.val.r) h
    exact one_ne_zero hr
  · have hr := congrArg (fun g : MulAction.stabilizer (VariableChange K) (ofJ0 K) => g.val.r) h
    dsimp only at hr
    rw [← epsilonChange_eq_negation] at hr
    exact one_ne_zero hr

theorem signProjection_quartic_square :
    charTwoSignProjection (quarticStabilizer ω hω) ^ 2 = 1 := by
  rw [← map_pow, pow_two, quarticStabilizer_square]
  exact (QuotientGroup.eq_one_iff _).mpr ((mem_charTwoSignSubgroup_iff _).mpr (Or.inr rfl))

theorem signProjection_cubic_ne_one :
    charTwoSignProjection (cubicStabilizer ω hω) ≠ 1 := by
  intro h
  have hm := (QuotientGroup.eq_one_iff _).mp h
  rcases (mem_charTwoSignSubgroup_iff _).mp hm with h | h
  · have hu := congrArg (fun g : MulAction.stabilizer (VariableChange K) (ofJ0 K) => (g.val.u : K)) h
    exact omega_ne_one ω hω hu
  · have hu := congrArg (fun g : MulAction.stabilizer (VariableChange K) (ofJ0 K) => (g.val.u : K)) h
    dsimp only at hu
    rw [← epsilonChange_eq_negation] at hu
    exact omega_ne_one ω hω hu

theorem cubicStabilizer_cube : cubicStabilizer ω hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_two]
  change (cubicChange ω hω * cubicChange ω hω) * cubicChange ω hω = 1
  ext
  · simpa only [VariableChange.mul_def, cubicChange, Units.val_mul, coe_omegaUnit,
      VariableChange.one_def, Units.val_one, pow_succ, pow_zero, one_mul] using omega_pow_three ω hω
  · simp [VariableChange.mul_def, cubicChange, VariableChange.one_def]
  · simp [VariableChange.mul_def, cubicChange, VariableChange.one_def]
  · simp [VariableChange.mul_def, cubicChange, VariableChange.one_def]

theorem signProjection_cubic_cube :
    charTwoSignProjection (cubicStabilizer ω hω) ^ 3 = 1 := by
  rw [← map_pow, cubicStabilizer_cube, map_one]

end
end Dubon2026.SourceEllipticCharTwo
