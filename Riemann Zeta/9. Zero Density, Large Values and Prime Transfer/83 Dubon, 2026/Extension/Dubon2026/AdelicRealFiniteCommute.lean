import Dubon2026.AdelicRealGL2Normalization

/-! # Genuine commutation of the original real and finite adelic actions -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- Original real and finite embeddings commute because their actual adelic coordinates are disjoint. -/
theorem adelicRealGL2_finite_commute (g : GeneralLinearGroup (Fin 2) ℝ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    Commute (adelicRealGL2Embedding g) (rationalAdelicFiniteGL2Embedding a) := by
  change adelicRealGL2Embedding g * rationalAdelicFiniteGL2Embedding a =
    rationalAdelicFiniteGL2Embedding a * adelicRealGL2Embedding g
  apply rationalAdelicGL2RealFiniteEquiv.injective
  simp only [map_mul, adelicRealGL2Embedding_coordinates,
    rationalAdelicFiniteGL2Embedding_coordinates, Prod.mk_mul_mk, one_mul, mul_one]

/-- The actual completed real and finite operators commute on every original Hilbert vector. -/
theorem adelicCyclicHilbert_real_finite_commute {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : SL(2, ℝ))
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : AdelicCyclicHilbert f) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g)
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) v) =
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
      (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) := by
  have h := (adelicRealGL2_finite_commute (toGL g) a).map (adelicCyclicHilbertRepresentation f)
  exact LinearMap.congr_fun h.eq v

end
end Dubon2026
