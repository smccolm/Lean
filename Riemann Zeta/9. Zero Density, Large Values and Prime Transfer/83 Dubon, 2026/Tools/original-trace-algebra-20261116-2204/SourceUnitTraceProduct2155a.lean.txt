import Mathlib.Tactic

/-! DUB-17/18 -> original all-weight association -> rank-two trace identities.
The exact operator trace satisfies the two-dimensional product identity
once the required centrality is proved. This does not assert that an
arbitrary quadratic relation constructs a rank-two representation. -/
namespace Dubon2026

/-- The two-dimensional trace product identity in an operator ring, with
all commutations named explicitly for discharge by the original Hecke image. -/
theorem sourceUnitTrace_product {G R : Type} [Group G] [Ring R]
    (ρ D : G →* R) (g h : G)
    (hc : Commute (ρ g⁻¹ * D g) (ρ h + ρ h⁻¹ * D h))
    (hDρ : Commute (D h) (ρ g⁻¹)) (hDD : Commute (D h) (D g)) :
    (ρ g + ρ g⁻¹ * D g) * (ρ h + ρ h⁻¹ * D h) =
      (ρ (g * h) + ρ (g * h)⁻¹ * D (g * h)) +
        (ρ (g * h⁻¹) + ρ (g * h⁻¹)⁻¹ * D (g * h⁻¹)) * D h := by
  have hinv : D h⁻¹ * D h = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc
    (ρ g + ρ g⁻¹ * D g) * (ρ h + ρ h⁻¹ * D h) =
        ρ g * (ρ h + ρ h⁻¹ * D h) + (ρ h + ρ h⁻¹ * D h) * (ρ g⁻¹ * D g) := by
      rw [add_mul, hc.eq]
    _ = ρ g * ρ h + ρ h⁻¹ * (ρ g⁻¹ * (D g * D h)) +
        (ρ g * ρ h⁻¹ * D h + ρ h * ρ g⁻¹ * D g) := by
      noncomm_ring [hDρ.left_comm, hDD.eq]
    _ = (ρ (g * h) + ρ (g * h)⁻¹ * D (g * h)) +
        (ρ (g * h⁻¹) + ρ (g * h⁻¹)⁻¹ * D (g * h⁻¹)) * D h := by
      simp only [map_mul, mul_inv_rev, inv_inv]
      noncomm_ring [hinv]

end Dubon2026
