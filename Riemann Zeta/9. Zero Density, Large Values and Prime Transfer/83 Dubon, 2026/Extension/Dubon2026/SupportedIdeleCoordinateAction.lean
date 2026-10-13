import Dubon2026.SupportedIdeleCoordinates
import Dubon2026.NumberFieldSupportedIdeleGaloisAction

/-! # Original local transport in supported-idele coordinates

The coordinate equivalence evaluates the original action by the same
completed field transports already proved from the global automorphisms.
These identities connect the supported coefficient representation to the
local stabilizer factors required by DUB-17's global norm index.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual finite supported coordinate transforms by the original completed transport. -/
theorem numberFieldSupportedIdeleCoordinate_finite_galois
    (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S)
    (v w : HeightOneSpectrum (𝓞 L)) (h : numberFieldGaloisPlaceEquiv K L σ v = w) :
    (numberFieldSupportedIdeleCoordinateEquiv L S
      (numberFieldSupportedIdeleGaloisMap K L S hS σ a)).2.val w =
      Units.map (numberFieldGaloisLocalTransport K L σ v w h).toMonoidHom
        ((numberFieldSupportedIdeleCoordinateEquiv L S a).2.val v) := by
  apply Units.ext
  exact numberFieldFiniteAdeleGaloisMap_apply K L σ a.val.val.2 v w h

/-- The actual infinite supported coordinate transforms by the original completed transport. -/
theorem numberFieldSupportedIdeleCoordinate_infinite_galois
    (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S)
    (v w : InfinitePlace L) (h : σ • v = w) :
    (numberFieldSupportedIdeleCoordinateEquiv L S
      (numberFieldSupportedIdeleGaloisMap K L S hS σ a)).1 w =
      Units.map (numberFieldGaloisArchimedeanTransport K L σ v w h).toMonoidHom
        ((numberFieldSupportedIdeleCoordinateEquiv L S a).1 v) := by
  apply Units.ext
  exact numberFieldInfiniteAdeleGaloisMap_apply K L σ a.val.val.1 v w h

end
end Dubon2026
