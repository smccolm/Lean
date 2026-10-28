import Dubon2026.SourceGammaOnePrincipalDivisorIdentities
import Dubon2026.SourceGammaOneReducedRiemannRochSpace

/-! DUB-17/18 -> arithmetic torsion surjectivity -> invariant reduced divisors.
If an original divisor is carried to a linearly equivalent divisor by an
actual coefficient automorphism, its one-dimensional reduced representative
is fixed. The principal correction is constructed from the unique spanning
function and exact original principal-divisor identities.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "FC" => functionFieldOver (Gamma1 N) ℂ

theorem reduced_divisor_fixed (τ : ℂ ≃ₐ[ℚ] ℂ)
    {D : Divisor ℂ FC} {f : FC} (hf0 : f ≠ 0) (hf : f ∈ LSpace D)
    (huniq : ∀ h ∈ LSpace D, ∃ a : ℂ, a • f = h)
    (hD : Divisor.IsPrincipal (arithmeticDivisorEquiv (Gamma1 N) τ D - D)) :
    arithmeticDivisorEquiv (Gamma1 N) τ (D + principalDivisor N ℂ f) =
      D + principalDivisor N ℂ f := by
  obtain ⟨u, hu0, hu⟩ := hD
  have hdiff : arithmeticDivisorEquiv (Gamma1 N) τ D - D = principalDivisor N ℂ u :=
    Finsupp.ext hu
  have he : arithmeticDivisorEquiv (Gamma1 N) τ D = D + principalDivisor N ℂ u := by
    rw [← hdiff]
    abel
  have hmem := (mem_lSpace_arithmetic_iff N τ).mpr hf
  rw [he, mem_lSpace_add_principal_iff N hu0] at hmem
  obtain ⟨a, ha⟩ := huniq _ hmem
  have htf : arithmeticRingAut (Gamma1 N) τ f ≠ 0 := (map_ne_zero _).mpr hf0
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at ha
    exact mul_ne_zero htf hu0 ha.symm
  rw [map_add, he, principal_arithmetic, add_assoc,
    add_comm (principalDivisor N ℂ u), ← principal_mul N htf hu0,
    ← ha, principal_smul N ha0]

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
