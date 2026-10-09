import Dubon2026.FiniteGroupProjection

/-! # Actual spherical matrix coefficients are constant on genuine central integral double cosets -/

namespace Dubon2026

noncomputable section
variable {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The original matrix coefficient of fixed vectors removes genuine trivial scalars and actual integral left and right factors. -/
theorem unitary_scalar_double_coset_coefficient (ρ : Representation ℂ G V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (c l d r : G) (hc : ∀ z, ρ c z = z) (x y : V)
    (hx : ρ l⁻¹ x = x) (hy : ρ r y = y) :
    inner ℂ x (ρ (c * l * d * r) y) = inner ℂ x (ρ d y) := by
  simp only [map_mul, Module.End.mul_apply, hc, hy]
  have he := representation_inner_inverse ρ hρ l⁻¹ x (ρ d y)
  simpa only [inv_inv, hx] using he.symm

end
end Dubon2026
