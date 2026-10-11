import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Original local algebra automorphisms stabilize the actual maximal ideal -/

namespace Dubon2026
noncomputable section

open IsLocalRing
open scoped Pointwise

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]

/-- Every original algebra automorphism of a local ring preserves its
actual maximal ideal under the original pointwise ideal action. -/
theorem localAlgebraAut_maximalIdeal_fixed (g : S ≃ₐ[R] S) :
    g • maximalIdeal S = maximalIdeal S := by
  rw [Ideal.pointwise_smul_def]
  exact map_ringEquiv_maximalIdeal g.toRingEquiv

/-- The actual stabilizer of the original maximal ideal contains all
original local algebra automorphisms, with their unchanged action. -/
def localAlgebraAutMaximalStabilizerEquiv :
    (S ≃ₐ[R] S) ≃* MulAction.stabilizer (S ≃ₐ[R] S) (maximalIdeal S) where
  toFun g := ⟨g, localAlgebraAut_maximalIdeal_fixed g⟩
  invFun g := g.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end
end Dubon2026
