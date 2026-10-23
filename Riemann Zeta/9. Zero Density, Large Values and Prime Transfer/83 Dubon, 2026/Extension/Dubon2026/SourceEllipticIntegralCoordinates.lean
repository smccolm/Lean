import Dubon2026.SourceEllipticFunctionGeneric
import Dubon2026.SourceEllipticRationalIntegral

/-! Integrality of the actual generic y-coordinate from that of x.
The native monic Weierstrass relation and integral closure perform the descent.
This specializes the integral-image argument also present in the archived
TauCeti Isogeny/FunctionField.lean (Apache-2.0, bfcff79b60964ba7bdb78b952828313686c327ba).
It serves the explicit odd quotient coordinate ring on the DUB-17/18 chain. -/

open Polynomial WeierstrassCurve

namespace Dubon2026.SourceEllipticFunctionField

/-- Integrality descends when the coefficient homomorphism has integral image. -/
theorem isIntegral_of_integral_image {R B K : Type*} [CommRing R] [CommRing B] [CommRing K]
    [Algebra R K] [Algebra B K] (hf : ∀ b : B, IsIntegral R (algebraMap B K b)) {x : K}
    (hx : IsIntegral B x) : IsIntegral R x := by
  exact isIntegral_trans x
    (hx.map_of_comp_eq ((algebraMap B K).codRestrict (integralClosure R K) hf)
      (RingHom.id K) rfl)

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The Weierstrass relation makes y integral over every subalgebra over which x is integral. -/
theorem isIntegral_genericY_of_genericX (A : Subalgebra F W.FunctionField)
    (hx : IsIntegral A (genericX W)) : IsIntegral A (genericY W) := by
  have hi (p : F[X]) : algebraMap F[X] W.FunctionField p ∈ integralClosure A W.FunctionField := by
    change IsIntegral A (algebraMap F[X] W.FunctionField p)
    rw [algebraMap_eq_aeval_genericX]
    exact isIntegral_aeval_over_subalgebra A hx p
  exact isIntegral_of_integral_image hi (isIntegral_genericY W F[X])

end Dubon2026.SourceEllipticFunctionField
