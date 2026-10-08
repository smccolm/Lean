import Dubon2026.HomogeneousTwistDerivative
import Dubon2026.HomogeneousCentralCharacter
import Dubon2026.TracelessEnvelopingProjection
import Dubon2026.EnvelopingLiftComposition

/-! # The full enveloping action of the genuine normalized algebraic GL₂ representation -/

namespace Dubon2026

noncomputable section

/-- The actual complex Lie action of the original degree-2m determinant twist. -/
def homogeneousNormalizedGL2Action (m : ℕ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆
    Module.End ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :=
  (homogeneousSl2Action (2 * m)).comp complexTracelessProjection

/-- This original matrix Lie action is precisely the proved genuine norm derivative of the actual determinant-twisted group action. -/
theorem homogeneousNormalizedGL2Action_hasDerivAt (m : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    HasDerivAt (fun t : ℂ => homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) (complexIdentityGLCurve a t) p)
      (homogeneousNormalizedGL2Action m a p) 0 :=
  homogeneousNormalizedTwist_hasDerivAt m a p

/-- Lift the genuine original derivative to the entire full matrix enveloping algebra. -/
def homogeneousGL2EnvelopingAction (m : ℕ) :
    UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) →ₐ[ℂ]
      Module.End ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :=
  UniversalEnvelopingAlgebra.lift ℂ (homogeneousNormalizedGL2Action m)

/-- Every original matrix generator acts by the actual norm-derived twisted algebraic infinitesimal. -/
theorem homogeneousGL2EnvelopingAction_generator (m : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ) :
    homogeneousGL2EnvelopingAction m (UniversalEnvelopingAlgebra.ι ℂ a) =
      homogeneousNormalizedGL2Action m a :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ a

/-- The entire genuine twisted algebraic enveloping action factors through the original trace projection. -/
theorem homogeneousGL2EnvelopingAction_factor (m : ℕ) :
    homogeneousGL2EnvelopingAction m = (homogeneousEnvelopingAction (2 * m)).comp tracelessEnvelopingProjection :=
  universalEnvelopingLift_comp (homogeneousSl2Action (2 * m)) complexTracelessProjection

end
end Dubon2026
