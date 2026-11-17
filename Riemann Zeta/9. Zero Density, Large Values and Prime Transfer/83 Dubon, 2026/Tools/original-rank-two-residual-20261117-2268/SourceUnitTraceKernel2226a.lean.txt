import Mathlib.Tactic

/-! DUB-17/18 -> original unramified rank-two association -> finite trace invariance.
The genuine trace expression is unchanged by an element killed by both
the original operator action and determinant. The actual norm-inertia
lemmas supply these two hypotheses in the source application. -/
namespace Dubon2026

/-- The actual dimension-two trace expression is invariant under a common
kernel element of its original action and determinant. -/
theorem sourceUnitTrace_kernel_translate
    {G R : Type*} [Group G] [Ring R] (ρ D : G →* R)
    (n : G) (hρ : ρ n = 1) (hD : D n = 1) (g : G) :
    ρ (n * g) + ρ (n * g)⁻¹ * D (n * g) = ρ g + ρ g⁻¹ * D g := by
  have hi : ρ n⁻¹ = 1 := by
    have h := map_mul ρ n⁻¹ n
    simpa only [inv_mul_cancel, map_one, hρ, mul_one] using h.symm
  rw [map_mul ρ, hρ, one_mul, mul_inv_rev, map_mul ρ, hi, mul_one,
    map_mul D, hD, one_mul]

end Dubon2026
