import Dubon2026.AdelicGL2Enveloping
import Dubon2026.HomogeneousGL2Enveloping
import Dubon2026.AdelicHomogeneousScalar

/-! # Full original GL₂ infinitesimal-character comparison with the genuine algebraic determinant twist -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- Every element of the full actual GL₂ enveloping center acts on every vector of the genuine degree-(k-2) determinant twist by the original cusp representation's full infinitesimal character. -/
theorem adelicGL2InfinitesimalCharacter_algebraic {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (m : ℕ)
    (hk : k = (2 * m : ℕ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    homogeneousGL2EnvelopingAction m z.val p = adelicGL2InfinitesimalCharacter f hf z • p := by
  rw [homogeneousGL2EnvelopingAction_factor]
  exact adelicInfinitesimalCharacter_homogeneous_scalar f hf (2 * m) hk
    (tracelessEnvelopingCenterProjection z) p

end
end Dubon2026
