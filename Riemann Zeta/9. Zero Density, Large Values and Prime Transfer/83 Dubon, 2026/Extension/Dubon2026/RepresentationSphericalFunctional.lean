import Dubon2026.SmoothInducedFrobenius

/-! # Actual spherical matrix coefficients from genuine compact-invariant linear functionals -/

namespace Dubon2026

noncomputable section

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ k : K, ∀ x : V, ℓ (ρ k.val x) = ℓ x)
    (y : V) (hy : ∀ k : K, ρ k.val y = y)

include hℓ hy in
/-- An original invariant functional and fixed vector give a genuinely bi-invariant coefficient on each original compact double coset. -/
theorem sphericalFunctional_double_coset (a : G) (l r : K) :
    ℓ (ρ (l.val * a * r.val) y) = ℓ (ρ a y) := by
  rw [map_mul, Module.End.mul_apply, hy, map_mul, Module.End.mul_apply, hℓ]

include hℓ hy in
/-- A genuine trivial scalar action leaves the actual double-coset coefficient unchanged as well. -/
theorem sphericalFunctional_scalar_double_coset (c a : G)
    (hc : ∀ x : V, ρ c x = x) (l r : K) :
    ℓ (ρ (c * l.val * a * r.val) y) = ℓ (ρ a y) := by
  have he : c * l.val * a * r.val = c * (l.val * a * r.val) := by group
  rw [he, map_mul, Module.End.mul_apply, hc]
  exact sphericalFunctional_double_coset ρ K ℓ hℓ y hy a l r

end
end Dubon2026
