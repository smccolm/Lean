import Dubon2026.SourceEllipticCharTwoStabilizerCard
import Dubon2026.SourceEllipticNegationVariableChange
import Dubon2026.SourceEllipticStabilizerPointAction

/-! Actual elliptic negation inside the characteristic-two exceptional
stabilizer. The existing all-characteristic point-negation theorem is
reused. Order two and centrality supply the DUB-17/18 order-twelve quotient. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [CharP K 2]

/-- The actual elliptic negation as an element of the exceptional stabilizer. -/
def charTwoNegation : MulAction.stabilizer (VariableChange K) (ofJ0 K) :=
  ⟨negationChange (ofJ0 K), MulAction.mem_stabilizer_iff.mpr (negationChange_smul _)⟩

omit [CharP K 2] in
theorem charTwoNegation_ne_one : charTwoNegation (K := K) ≠ 1 := by
  intro h
  have ht := congrArg (fun g : MulAction.stabilizer (VariableChange K) (ofJ0 K) => g.val.t) h
  have he : (-1 : K) = 0 := ht
  exact neg_ne_zero.mpr one_ne_zero he

omit [CharP K 2] in
theorem charTwoNegation_square : charTwoNegation (K := K) ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change negationChange (ofJ0 K) * negationChange (ofJ0 K) = 1
  ext <;> simp [negationChange, ofJ0, VariableChange.mul_def, VariableChange.one_def]
  ring

omit [CharP K 2] in
theorem charTwoNegation_order : orderOf (charTwoNegation (K := K)) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime charTwoNegation_square charTwoNegation_ne_one

theorem charTwoNegation_central : charTwoNegation (K := K) ∈
    Subgroup.center (MulAction.stabilizer (VariableChange K) (ofJ0 K)) := by
  rw [Subgroup.mem_center_iff]
  intro γ
  apply Subtype.ext
  have hu := ((stabilizer_coordinates_iff γ.val).mp
    (MulAction.mem_stabilizer_iff.mp γ.property)).1
  have hn : (-1 : K) = 1 := by linear_combination -(two_eq_zero K)
  change γ.val * negationChange (ofJ0 K) = negationChange (ofJ0 K) * γ.val
  ext <;> simp [negationChange, ofJ0, VariableChange.mul_def, hn, hu, add_comm]

omit [CharP K 2] in
theorem charTwoNegation_point [DecidableEq K] (P : (ofJ0 K).toAffine.Point) :
    stabilizerPointEquiv (ofJ0 K) (charTwoNegation (K := K)).val
      (MulAction.mem_stabilizer_iff.mp charTwoNegation.property) P = -P := by
  apply (stabilizerPointEquiv_eq_iff_heq _ _ _ _ _).mpr
  exact vcInvFun_negationChange_heq _ P

end
end Dubon2026.SourceEllipticCharTwo
