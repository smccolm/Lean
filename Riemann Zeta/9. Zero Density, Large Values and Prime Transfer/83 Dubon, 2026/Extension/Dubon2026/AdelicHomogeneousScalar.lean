import Dubon2026.AdelicHomogeneousCharacter
import Dubon2026.HomogeneousScalarAction

/-! # Original cusp infinitesimal character on the entire genuine algebraic representation -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- Every genuine central element acts on every vector of the entire original degree-(k-2) homogeneous representation by the actual cusp infinitesimal character. -/
theorem adelicInfinitesimalCharacter_homogeneous_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (n : ℕ) (hk : k = (n : ℤ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2))
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n) :
    homogeneousEnvelopingAction n z.val p = adelicInfinitesimalCharacter f hf z • p := by
  rw [homogeneousEnvelopingAction_center_apply, adelicInfinitesimalCharacter_eq_reflected_verma f hf]
  have he : (k : ℂ) - 2 = n := by rw [hk]; push_cast; ring
  rw [he]

end
end Dubon2026
