import Dubon2026.FiniteAdelicLocalUnits
import Dubon2026.AdelicLocalRepresentation
import Dubon2026.AdelicScalarCoordinates

/-! # Exact trivial central character of every genuine original local action -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The actual local scalar insertion is precisely the scalar of its genuine full adelic unit with real coordinate one. -/
theorem adelicLocal_scalar_pair (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ) :
    rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v (GeneralLinearGroup.scalar (Fin 2) u)) =
      GeneralLinearGroup.scalar (Fin 2) (rationalAdeleUnitPair 1 (finiteAdeleLocalUnit v u)) := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  rw [rationalAdelicFiniteGL2Embedding_coordinates, rationalAdeleUnitPair_scalar_coordinates,
    finiteAdelicLocalGL2_scalar, map_one]

/-- Every actual local scalar acts trivially on the original full cusp Hilbert space, with no separately assumed local character. -/
theorem adelicCyclicLocal_scalar_action {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : HeightOneSpectrum ℤ)
    (u : (v.adicCompletion ℚ)ˣ) (x : AdelicCyclicHilbert f) :
    adelicCyclicLocalRepresentation f v (GeneralLinearGroup.scalar (Fin 2) u) x = x := by
  rw [adelicCyclicLocalRepresentation_apply, adelicLocal_scalar_pair]
  exact adelicCyclicHilbert_scalar_action f _ x

end
end Dubon2026
