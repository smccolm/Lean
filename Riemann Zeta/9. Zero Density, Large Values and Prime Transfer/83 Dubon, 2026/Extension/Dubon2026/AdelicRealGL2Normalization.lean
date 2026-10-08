import Dubon2026.AdelicHilbertCentralLevel
import Dubon2026.AdelicRealOrbitCoordinates
import Dubon2026.AdelicScalarCoordinates

/-! # The original real general-linear action and its exact central normalization -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The genuine full real general-linear group embedded with identity finite coordinates. -/
def adelicRealGL2Embedding : GeneralLinearGroup (Fin 2) ℝ →* RationalAdelicGL2 :=
  rationalAdelicGL2RealFiniteEquiv.symm.toMonoidHom.comp
    ((MonoidHom.id _).prod (1 : GeneralLinearGroup (Fin 2) ℝ →*
      GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)))

/-- The original real embedding has exactly its prescribed actual real and finite coordinates. -/
theorem adelicRealGL2Embedding_coordinates (g : GeneralLinearGroup (Fin 2) ℝ) :
    rationalAdelicGL2RealFiniteEquiv (adelicRealGL2Embedding g) = (g, 1) :=
  rationalAdelicGL2RealFiniteEquiv.apply_symm_apply _

/-- The genuine general-linear embedding restricts to the already constructed original special-linear embedding. -/
theorem adelicRealGL2Embedding_toGL (g : SL(2, ℝ)) :
    adelicRealGL2Embedding (toGL g) = adelicRealSL2Embedding g := rfl

/-- Every positive real matrix is its actual positive scalar root times its genuine normalized special-linear matrix. -/
theorem realPositiveNormalize_factor (g : GL(2, ℝ)⁺) :
    GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (realPositiveDetRoot g)
      (realPositiveDetRoot_pos g).ne') * toGL (realPositiveNormalize g) = g.val := by
  apply Units.ext
  change Matrix.scalar (Fin 2) (realPositiveDetRoot g) *
    ((realPositiveDetRoot g)⁻¹ • g.val.val) = g.val.val
  have hs : Matrix.scalar (Fin 2) (realPositiveDetRoot g) = realPositiveDetRoot g • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  rw [hs, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ (realPositiveDetRoot_pos g).ne', one_smul]

/-- On the original completed adelic Hilbert space, positive determinant normalization preserves every vector's actual orbit. -/
theorem adelicCyclicHilbert_positive_normalize {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺)
    (v : AdelicCyclicHilbert f) :
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g.val) v =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realPositiveNormalize g)) v := by
  let u := Units.mk0 (realPositiveDetRoot g) (realPositiveDetRoot_pos g).ne'
  have he : adelicRealGL2Embedding g.val =
      GeneralLinearGroup.scalar (Fin 2) (rationalAdeleUnitPair u 1) *
        adelicRealSL2Embedding (realPositiveNormalize g) := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [adelicRealGL2Embedding_coordinates, map_mul, rationalAdeleUnitPair_scalar_coordinates,
      ← adelicRealGL2Embedding_toGL, adelicRealGL2Embedding_coordinates]
    apply Prod.ext
    · exact (realPositiveNormalize_factor g).symm
    · simp
  rw [he, map_mul, Module.End.mul_apply, adelicCyclicHilbert_scalar_action]

end
end Dubon2026
