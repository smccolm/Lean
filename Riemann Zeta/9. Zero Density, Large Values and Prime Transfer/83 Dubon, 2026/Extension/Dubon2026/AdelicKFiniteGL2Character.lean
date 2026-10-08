import Dubon2026.AdelicKFiniteIdentification
import Dubon2026.AdelicGL2AlgebraicCharacter

/-! # The full original GL₂ character on every genuine K-finite vector -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The entire genuine GL₂ enveloping center acts by the original infinitesimal character on every actual K-finite smooth vector of the original real component. -/
theorem adelicRealKFinite_gl2_character (hf : f ≠ 0) (hk : 0 < k)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (v : adelicRealSmoothSubmodule f) (hv : v.val ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v.val)] :
    adelicGL2EnvelopingAction f z.val v = adelicGL2InfinitesimalCharacter f hf z • v :=
  adelicGL2InfinitesimalCharacter_span f hf z v
    (@adelicSmoothKFinite_mem_raisingSpan N inferInstance k f hf hk v hv inferInstance)

/-- The actual full central action agrees simultaneously on each genuine real K-finite cusp vector and every vector of its original algebraic determinant twist. -/
theorem adelicRealKFinite_algebraic_character (hf : f ≠ 0) (m : ℕ) (hk : k = (2 * m : ℕ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (v : adelicRealSmoothSubmodule f) (hv : v.val ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v.val)]
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    adelicGL2EnvelopingAction f z.val v = adelicGL2InfinitesimalCharacter f hf z • v ∧
      homogeneousGL2EnvelopingAction m z.val p = adelicGL2InfinitesimalCharacter f hf z • p :=
  ⟨adelicRealKFinite_gl2_character f hf (by omega) z v hv,
    adelicGL2InfinitesimalCharacter_algebraic f hf m hk z p⟩

end
end Dubon2026
