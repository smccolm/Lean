import Dubon2026.PolarizationCongruence
import Dubon2026.PolarizedScalarStabilizer
import Dubon2026.LocalPrincipalUnitSquareRoot

/-! The residue-one scalar correction in DUB-17 polarized descent.
Scalar congruence multiplies a form by a square; the existing complete-ring
root lift makes this correction without altering the CM matrices. -/

namespace Dubon2026
open Matrix IsLocalRing
noncomputable section

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Successive actual changes of basis act by the product congruence. -/
theorem polarizationCongruence_mul (B U V : GeneralLinearGroup ι R) :
    polarizationCongruence B (U * V) = polarizationCongruence (polarizationCongruence B V) U := by
  unfold polarizationCongruence
  rw [map_mul]
  group

/-- A scalar change of basis multiplies the original polarization by its square. -/
theorem polarizationCongruence_scalar (B : GeneralLinearGroup ι R) (u : Rˣ) :
    polarizationCongruence B (GeneralLinearGroup.scalar ι u) =
      GeneralLinearGroup.scalar ι (u ^ 2) * B := by
  unfold polarizationCongruence
  rw [polarizedContragredient_scalar, map_inv, inv_inv, map_pow, pow_two]
  rw [mul_assoc, ← (polarizedScalar_commute u B).eq, ← mul_assoc]

/-- A residue-one scalar discrepancy between polarization matrices can be
removed by a residue-one scalar basis change in the original complete ring. -/
theorem polarization_scalar_strict_adjustment [Nonempty ι] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (h2 : (2 : ResidueField R) ≠ 0)
    (B₀ B₁ : GeneralLinearGroup ι R) (u : Rˣ)
    (hu : B₁ = GeneralLinearGroup.scalar ι u * B₀)
    (hred : GeneralLinearGroup.map (residue R) B₁ = GeneralLinearGroup.map (residue R) B₀) :
    ∃ v : Rˣ, Units.map (residue R).toMonoidHom v = 1 ∧
      polarizationCongruence B₁ (GeneralLinearGroup.scalar ι v) = B₀ := by
  have hu0 : Units.map (residue R).toMonoidHom u = 1 := by
    apply polarizedScalar_reduction_eq_one (ι := ι) (residue R) u
    rw [hu, map_mul] at hred
    exact mul_right_cancel (hred.trans (one_mul _).symm)
  obtain ⟨v, hv, hvsq⟩ := localPrincipalUnit_squareRoot h2 u hu0
  refine ⟨v⁻¹, ?_, ?_⟩
  · rw [map_inv, hv, inv_one]
  · rw [polarizationCongruence_scalar, inv_pow, hvsq, hu, ← mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, one_mul]

end
end Dubon2026
