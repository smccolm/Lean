import Dubon2026.FiniteGroupProjection

/-! # Exact original unitary Hecke-trace pairings on actual fixed vectors -/

namespace Dubon2026

noncomputable section

variable {G V ι : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]

/-- The genuine finite coset sum in the first slot has the exact original diagonal matrix coefficient when the other vector is fixed by the original representatives. -/
theorem unitary_coset_trace_inner_left (ρ : Representation ℂ G V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (r : ι → G) (d : G) (x y : V) (hy : ∀ i, ρ (r i) y = y) :
    inner ℂ (∑ i, ρ ((r i)⁻¹ * d⁻¹) x) y =
      (Fintype.card ι : ℂ) * inner ℂ x (ρ d y) := by
  rw [sum_inner]
  simp only [representation_inner_inverse ρ hρ, inv_inv, map_mul,
    Module.End.mul_apply, hy]
  simp

/-- The genuine finite coset sum in the second slot has the original inverse-diagonal matrix coefficient on original representative-fixed vectors. -/
theorem unitary_coset_trace_inner_right (ρ : Representation ℂ G V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (r : ι → G) (d : G) (x y : V) (hx : ∀ i, ρ (r i) x = x) :
    inner ℂ x (∑ i, ρ ((r i)⁻¹ * d⁻¹) y) =
      (Fintype.card ι : ℂ) * inner ℂ x (ρ d⁻¹ y) := by
  rw [inner_sum]
  simp only [map_mul, Module.End.mul_apply]
  have he (i : ι) : inner ℂ x (ρ (r i)⁻¹ (ρ d⁻¹ y)) = inner ℂ x (ρ d⁻¹ y) := by
    rw [← representation_inner_inverse ρ hρ, hx]
  simp only [he]
  simp

/-- A genuine compact conjugation identity for the original inverse diagonal gives symmetry of the actual finite coset sum on original fixed vectors. -/
theorem unitary_coset_trace_symmetric (ρ : Representation ℂ G V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (r : ι → G) (d j : G)
    (hd : ∀ z, ρ d⁻¹ z = ρ j (ρ d (ρ j⁻¹ z)))
    (x y : V) (hx : ∀ i, ρ (r i) x = x) (hy : ∀ i, ρ (r i) y = y)
    (hxj : ρ j⁻¹ x = x) (hyj : ρ j⁻¹ y = y) :
    inner ℂ (∑ i, ρ ((r i)⁻¹ * d⁻¹) x) y = inner ℂ x (∑ i, ρ ((r i)⁻¹ * d⁻¹) y) := by
  rw [unitary_coset_trace_inner_left ρ hρ r d x y hy,
    unitary_coset_trace_inner_right ρ hρ r d x y hx, hd y, hyj]
  have he := representation_inner_inverse ρ hρ j⁻¹ x (ρ d y)
  rw [inv_inv, hxj] at he
  rw [← he]

end
end Dubon2026
