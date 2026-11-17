import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic

/-! DUB-17/18 -> original all-weight association -> trace membership.
Transport a known central trace value by actual group conjugation. The
application supplies determinant invariance from the genuine cyclotomic
character and commutation from the original Galois/Hecke intertwining. -/
namespace Dubon2026

/-- A trace expression with an invariant determinant retains its known value
under conjugation when that value and determinant commute with the conjugator. -/
theorem sourceUnitTrace_conjugate_eq {G R : Type} [Group G] [Ring R]
    (ρ : G →* R) (D : G → R) (g τ : G) (H : R)
    (hD : D (τ * g * τ⁻¹) = D g)
    (hcomm : Commute (ρ τ⁻¹) (D g))
    (hH : Commute (ρ τ) H)
    (htrace : ρ g + ρ g⁻¹ * D g = H) :
    ρ (τ * g * τ⁻¹) + ρ (τ * g * τ⁻¹)⁻¹ * D (τ * g * τ⁻¹) = H := by
  have hi : (τ * g * τ⁻¹)⁻¹ = τ * g⁻¹ * τ⁻¹ := by group
  rw [hi, hD, map_mul, map_mul, map_mul, map_mul]
  calc
    ρ τ * ρ g * ρ τ⁻¹ + ρ τ * ρ g⁻¹ * ρ τ⁻¹ * D g =
        ρ τ * (ρ g + ρ g⁻¹ * D g) * ρ τ⁻¹ := by
      rw [mul_assoc (ρ τ * ρ g⁻¹), hcomm.eq]
      noncomm_ring
    _ = ρ τ * H * ρ τ⁻¹ := by rw [htrace]
    _ = H := by
      rw [hH.eq, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

end Dubon2026
