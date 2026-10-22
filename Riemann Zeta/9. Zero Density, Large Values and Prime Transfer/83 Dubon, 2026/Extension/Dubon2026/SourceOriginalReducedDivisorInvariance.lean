import Dubon2026.SourceOriginalPrincipalDivisorIdentities
import Dubon2026.SourceOriginalReducedRiemannRochSpace

/-! DUB-17/18 -> arithmetic torsion surjectivity -> invariant reduced divisors.
If an original divisor is carried to a linearly equivalent divisor by an
actual coefficient automorphism, its one-dimensional reduced representative
is fixed. The principal correction is constructed from the unique spanning
function and exact original principal-divisor identities.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]
local notation "FC" => modularFunctionFieldOver N ℂ

theorem original_reduced_divisor_fixed (τ : ℂ ≃ₐ[ℚ] ℂ)
    {D : Divisor ℂ FC} {f : FC} (hf0 : f ≠ 0) (hf : f ∈ LSpace D)
    (huniq : ∀ h ∈ LSpace D, ∃ a : ℂ, a • f = h)
    (hD : Divisor.IsPrincipal (originalArithmeticDivisorEquiv N τ D - D)) :
    originalArithmeticDivisorEquiv N τ (D + originalPrincipalDivisor N ℂ f) =
      D + originalPrincipalDivisor N ℂ f := by
  obtain ⟨u, hu0, hu⟩ := hD
  have hdiff : originalArithmeticDivisorEquiv N τ D - D = originalPrincipalDivisor N ℂ u :=
    Finsupp.ext hu
  have he : originalArithmeticDivisorEquiv N τ D = D + originalPrincipalDivisor N ℂ u := by
    rw [← hdiff]
    abel
  have hmem := (mem_original_lSpace_arithmetic_iff N τ).mpr hf
  rw [he, mem_original_lSpace_add_principal_iff N hu0] at hmem
  obtain ⟨a, ha⟩ := huniq _ hmem
  have htf : originalArithmeticRingAut N τ f ≠ 0 := (map_ne_zero _).mpr hf0
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at ha
    exact mul_ne_zero htf hu0 ha.symm
  rw [map_add, he, original_principal_arithmetic, add_assoc,
    add_comm (originalPrincipalDivisor N ℂ u), ← original_principal_mul N htf hu0,
    ← ha, original_principal_smul N ha0]

end
end Dubon2026.SourceFunctionField.OriginalConstantField
