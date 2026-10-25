import Dubon2026.SourceEllipticCharTwoQuaternionStabilizers

/-! DUB-17/18 -> characteristic-two fixed cyclic-subgroup count nuThree.
The actual cubic commutator squares to elliptic negation. The already proved
quaternion product and central negation give this by group arithmetic,
avoiding another coordinate expansion from the source. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [CharP K 2]

/-- The actual stabilizer commutator used to rule out scalar cubic action. -/
def cubicCommutator (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    MulAction.stabilizer (VariableChange K) (ofJ0 K) :=
  (cubicStabilizer ω hω)⁻¹ * quarticStabilizer ω hω *
    cubicStabilizer ω hω * (quarticStabilizer ω hω)⁻¹

theorem cubicCommutator_square (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    cubicCommutator ω hω * cubicCommutator ω hω = charTwoNegation := by
  let α := quarticStabilizer ω hω
  let β := cubicStabilizer ω hω
  let δ := quaternionStabilizer ω hω
  let ε := charTwoNegation (K := K)
  let x := β⁻¹ * δ * β
  have hα : α * α = ε := quarticStabilizer_square ω hω
  have hδ : δ * δ = ε := quaternionStabilizer_square ω hω
  have hε : ε * ε = 1 := by simpa only [pow_two] using charTwoNegation_square (K := K)
  have hg : δ = α * (β * α * β⁻¹) := quaternionStabilizer_eq ω hω
  have hαinv : α⁻¹ = α * ε := by
    apply mul_left_cancel (a := α)
    rw [mul_inv_cancel, ← mul_assoc, hα, hε]
  have hc (g : MulAction.stabilizer (VariableChange K) (ofJ0 K)) : g * ε = ε * g :=
    Subgroup.mem_center_iff.mp charTwoNegation_central g
  have hx : x * x = ε := by
    calc x * x = β⁻¹ * (δ * δ) * β := by dsimp [x]; group
      _ = β⁻¹ * ε * β := by rw [hδ]
      _ = β⁻¹ * (ε * β) := by group
      _ = β⁻¹ * (β * ε) := by rw [← hc β]
      _ = ε := by group
  have heq : cubicCommutator ω hω = x * ε := by
    change β⁻¹ * α * β * α⁻¹ = x * ε
    calc β⁻¹ * α * β * α⁻¹ = (β⁻¹ * (α * (β * α * β⁻¹)) * β) * ε := by
          rw [hαinv]; group
      _ = x * ε := by rw [← hg]
  rw [heq]
  have hc' : Commute x ε := hc x
  calc (x * ε) * (x * ε) = (x * ε) ^ 2 := (pow_two _).symm
    _ = x ^ 2 * ε ^ 2 := hc'.mul_pow 2
    _ = ε := by rw [pow_two, pow_two, hx, hε, mul_one]

end
end Dubon2026.SourceEllipticCharTwo
