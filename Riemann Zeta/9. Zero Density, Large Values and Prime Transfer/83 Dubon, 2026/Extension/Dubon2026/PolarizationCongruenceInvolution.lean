import Dubon2026.PolarizationCongruence
import Dubon2026.PolarizedInvolution

/-! Matrix congruence is the literal full polarized conjugation at the
real-place involution. This links the scalar correction to DUB-17's full
arithmetic strict equivalence. -/

namespace Dubon2026
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- On the identity component, the actual linear basis change conjugates
the original matrix and leaves the original multiplier unchanged. -/
theorem polarizedLinear_conjugate_identity (U A : GeneralLinearGroup ι R) (u : Rˣ) :
    polarizedLinearInclusion U * polarizedIdentityComponent (A, u) *
      (polarizedLinearInclusion U)⁻¹ = polarizedIdentityComponent (U * A * U⁻¹, u) := by
  change polarizedIdentityComponent (U, 1) * polarizedIdentityComponent (A, u) *
    (polarizedIdentityComponent (U, 1))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext rfl (by simp)

/-- At the actual odd real-place point, polarized conjugation is exactly
the original congruence of polarization matrices. -/
theorem polarizedLinear_conjugate_involution (U B : GeneralLinearGroup ι R) :
    polarizedLinearInclusion U * polarizedInvolution B * (polarizedLinearInclusion U)⁻¹ =
      polarizedInvolution (polarizationCongruence B U) := by
  rw [← map_inv]
  apply SemidirectProduct.ext
  · change ((U, (1 : Rˣ)) * (B, 1)) *
        polarizedSwitchAction (Multiplicative.ofAdd (1 : ZMod 2)) (U⁻¹, 1) =
      (polarizationCongruence B U, 1)
    rw [polarizedSwitchAction_generator]
    apply Prod.ext
    · change U * B * (GeneralLinearGroup.scalar ι 1 * polarizedContragredient U⁻¹) = _
      rw [map_one, one_mul, map_inv]
      rfl
    · change (1 : Rˣ) * 1 * 1 = 1
      simp
  · change (1 * Multiplicative.ofAdd (1 : ZMod 2)) * 1 = Multiplicative.ofAdd (1 : ZMod 2)
    simp

end Dubon2026
