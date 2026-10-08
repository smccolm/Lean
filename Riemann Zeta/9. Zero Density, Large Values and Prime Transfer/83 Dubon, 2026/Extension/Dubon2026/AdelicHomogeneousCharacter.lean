import Dubon2026.AdelicVermaCharacter
import Dubon2026.HomogeneousCentralCharacter

/-! # Exact original cusp-character action on the genuine algebraic lowest vector -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The full actual cusp infinitesimal character acts on the original degree-(k-2) algebraic generator for every central element. -/
theorem adelicInfinitesimalCharacter_homogeneous_generator {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (n : ℕ) (hk : k = (n : ℤ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    homogeneousEnvelopingAction n z.val (homogeneousCompactGenerator n) =
      adelicInfinitesimalCharacter f hf z • homogeneousCompactGenerator n := by
  rw [homogeneousEnvelopingAction_center_generator, adelicInfinitesimalCharacter_eq_reflected_verma f hf]
  have he : (k : ℂ) - 2 = n := by rw [hk]; push_cast; ring
  rw [he]

end
end Dubon2026
