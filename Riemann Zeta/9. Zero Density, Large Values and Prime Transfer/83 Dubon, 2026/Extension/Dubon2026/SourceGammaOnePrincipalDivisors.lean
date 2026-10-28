import Dubon2026.SourceGammaOneCurveInputs
import Dubon2026.SourceCurveSeparatingFunctionSupport

/-! DUB17/18 -> actual Gamma1 arithmetic torsion descent -> invariant reduced
divisors. The divisor here is the literal finite normalized-order divisor.
Existing finite-coordinate support and the actual curve inputs supply
finiteness and degree zero; no principal-divisor premise is introduced. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
local notation "F" => functionFieldOver (Gamma1 N) L

theorem finite_principal_support (f : F) :
    {v : Place L F | v.ord f ≠ 0}.Finite := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  letI := finiteDimensional_jCoordinateOver (Γ := Gamma1 N)
    (by simp [Gamma1_mem, ModularGroup.T]) L
  exact finite_function_support_of_separating_coordinate
    (jCoordinateOver (Gamma1 N) L) (transcendental_jCoordinateOver (Gamma1 N) L) f

/-- The actual normalized-order divisor of a Gamma1 function. -/
def principalDivisor (f : F) : Divisor L F :=
  Finsupp.ofSupportFinite (fun v => v.ord f) (finite_principal_support N L f)

theorem principalDivisor_apply (f : F) (v : Place L F) :
    principalDivisor N L f v = v.ord f := rfl

theorem degree_principalDivisor [IsAlgClosed L] (f : F) :
    Divisor.degree (principalDivisor N L f) = 0 := by
  letI := gamma1_isCurveOver N L
  rcases eq_or_ne f 0 with rfl | hf
  · have he : principalDivisor N L 0 = 0 := by
      ext v
      exact v.ord_zero
    rw [he, map_zero]
  · obtain ⟨D, hD, hD0⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf
    have he : principalDivisor N L f = D := Finsupp.ext fun v => (hD v).symm
    rw [he, hD0]

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
