import Dubon2026.SourceUnitaryCharacterTorsion

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier logarithms. Adapted from the Apache-2.0 scope-795b primary at
revision 6e837e75355538c7f80bab5b956861e86c4eacc2. The actual
parabolic quotient has no cyclic torsion factors because each coordinate
character has the proved integer parabolic lift. The resulting logarithm
is additive and vanishes on the same actual elliptic/parabolic elements.
No torsion-freeness, character lift, or logarithm premise is assumed. -/
namespace Dubon2026.SourceUnitaryCharacterLift
noncomputable section
open scoped MatrixGroups
variable (Γ : Subgroup SL(2, ℤ))

/-- The actual unit-circle character associated with a unit-modulus multiplier. -/
def unitChar (χ : Γ → ℂ) (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ)
    (hunit : ∀ γ, ‖χ γ‖ = 1) : Γ →* Circle where
  toFun γ := ⟨χ γ, mem_sphere_zero_iff_norm.2 (hunit γ)⟩
  map_one' := Circle.ext (by
    have h1 : χ 1 ≠ 0 := fun h => by simpa [h] using hunit 1
    have h2 : χ 1 * χ 1 = χ 1 * 1 := by rw [mul_one, ← hmul, one_mul]
    rw [Circle.coe_one]
    exact (mul_right_inj' h1).mp h2)
  map_mul' γ δ := Circle.ext (by rw [Circle.coe_mul]; exact hmul γ δ)

theorem unitChar_apply (χ : Γ → ℂ) (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ)
    (hunit : ∀ γ, ‖χ γ‖ = 1) (γ : Γ) : (unitChar Γ χ hmul hunit γ : ℂ) = χ γ := rfl


end
end Dubon2026.SourceUnitaryCharacterLift
