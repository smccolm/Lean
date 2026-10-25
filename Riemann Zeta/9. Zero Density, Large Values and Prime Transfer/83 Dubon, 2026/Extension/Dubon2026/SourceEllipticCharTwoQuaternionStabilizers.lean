import Dubon2026.SourceEllipticCharTwoQuarticChanges
import Dubon2026.SourceEllipticStabilizerPointHom

/-! DUB-17/18 -> characteristic-two fixed cyclic-subgroup count nuTwo.
The explicit source changes belong to the actual elliptic stabilizer and
satisfy the exact quaternion relations consumed by the nonscalar theorem. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [CharP K 2]

theorem epsilonChange_eq_negation :
    (epsilonChange : VariableChange K) = (charTwoNegation (K := K)).val := by
  change (⟨1, 0, 0, 1⟩ : VariableChange K) = negationChange (ofJ0 K)
  ext <;> simp [negationChange, ofJ0, CharTwo.neg_eq]

/-- The actual exceptional quartic stabilizer element. -/
def quarticStabilizer (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    MulAction.stabilizer (VariableChange K) (ofJ0 K) :=
  ⟨quarticChange ω, MulAction.mem_stabilizer_iff.mpr (quarticChange_smul ω hω)⟩

/-- The actual exceptional cubic stabilizer element. -/
def cubicStabilizer (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    MulAction.stabilizer (VariableChange K) (ofJ0 K) :=
  ⟨cubicChange ω hω, MulAction.mem_stabilizer_iff.mpr (cubicChange_smul ω hω)⟩

/-- The actual quaternion product in the exceptional stabilizer. -/
def quaternionStabilizer (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    MulAction.stabilizer (VariableChange K) (ofJ0 K) :=
  ⟨quaternionChange ω, MulAction.mem_stabilizer_iff.mpr (quaternionChange_smul ω hω)⟩

theorem quarticStabilizer_square (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    quarticStabilizer ω hω * quarticStabilizer ω hω = charTwoNegation :=
  Subtype.ext ((quarticChange_mul_quarticChange ω).trans epsilonChange_eq_negation)

theorem quaternionStabilizer_square (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    quaternionStabilizer ω hω * quaternionStabilizer ω hω = charTwoNegation :=
  Subtype.ext ((quaternionChange_mul_quaternionChange ω hω).trans epsilonChange_eq_negation)

theorem quaternionStabilizer_eq (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    quaternionStabilizer ω hω = quarticStabilizer ω hω *
      (cubicStabilizer ω hω * quarticStabilizer ω hω * (cubicStabilizer ω hω)⁻¹) :=
  Subtype.ext (quaternionChange_eq ω hω)

end
end Dubon2026.SourceEllipticCharTwo
