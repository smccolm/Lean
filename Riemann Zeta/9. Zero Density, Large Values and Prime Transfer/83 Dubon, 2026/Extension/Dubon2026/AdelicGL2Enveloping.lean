import Dubon2026.AdelicFullGL2Derivative
import Dubon2026.AdelicInfinitesimalCharacter
import Dubon2026.TracelessEnvelopingProjection
import Dubon2026.EnvelopingLiftComposition

/-! # The full GL₂ enveloping action and original cusp infinitesimal character -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The full genuine matrix enveloping algebra acts by lifting the original GL₂ norm derivatives. -/
def adelicGL2EnvelopingAction :
    UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) →ₐ[ℂ]
      Module.End ℂ (adelicRealSmoothSubmodule f) :=
  UniversalEnvelopingAlgebra.lift ℂ (adelicComplexGL2Action f)

/-- Every original matrix generator retains its actual norm-derived infinitesimal action. -/
theorem adelicGL2EnvelopingAction_generator (a : Matrix (Fin 2) (Fin 2) ℂ) :
    adelicGL2EnvelopingAction f (UniversalEnvelopingAlgebra.ι ℂ a) = adelicComplexGL2Action f a :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ a

/-- The entire original GL₂ enveloping action factors through the genuine trace projection, not just the Casimir. -/
theorem adelicGL2EnvelopingAction_factor :
    adelicGL2EnvelopingAction f = (adelicEnvelopingAction f).comp tracelessEnvelopingProjection :=
  universalEnvelopingLift_comp (adelicComplexSl2Action f) complexTracelessProjection

/-- The actual full GL₂ infinitesimal character is the original cusp character on the proved image of its entire enveloping center. -/
def adelicGL2InfinitesimalCharacter (hf : f ≠ 0) :
    Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)) →ₐ[ℂ] ℂ :=
  (adelicInfinitesimalCharacter f hf).comp tracelessEnvelopingCenterProjection

/-- Every genuine full GL₂ central element acts by the original full character on every vector of the original cyclic Lie module. -/
theorem adelicGL2InfinitesimalCharacter_span (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (v : adelicRealSmoothSubmodule f) (hv : v ∈ adelicRaisingSpan f) :
    adelicGL2EnvelopingAction f z.val v = adelicGL2InfinitesimalCharacter f hf z • v := by
  have he := congrArg (fun T : UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) →ₐ[ℂ]
    Module.End ℂ (adelicRealSmoothSubmodule f) => T z.val v) (adelicGL2EnvelopingAction_factor f)
  exact he.trans (adelicInfinitesimalCharacter_span f hf (tracelessEnvelopingCenterProjection z) v hv)

/-- The full character in particular is the actual action on the original nonzero smooth cusp generator. -/
theorem adelicGL2InfinitesimalCharacter_generator (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ))) :
    adelicGL2EnvelopingAction f z.val (adelicSmoothGenerator f) =
      adelicGL2InfinitesimalCharacter f hf z • adelicSmoothGenerator f :=
  adelicGL2InfinitesimalCharacter_span f hf z _ (adelicSmoothGenerator_mem_raisingSpan f)

end
end Dubon2026
