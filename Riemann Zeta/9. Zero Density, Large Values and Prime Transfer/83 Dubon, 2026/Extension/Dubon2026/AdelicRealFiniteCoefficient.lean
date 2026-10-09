import Dubon2026.AdelicFullOrbitWeightProjection
import Dubon2026.AdelicFiniteTupleGram

/-! # Actual real and finite adelic matrix coefficients factor in the original cusp representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine projection to the original lowest-weight space yields the exact finite/real coefficient identity. -/
theorem adelicCyclicFinite_real_coefficient_factor (hf : f ≠ 0) (hk : 0 < k)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (g : GeneralLinearGroup (Fin 2) ℝ) :
    inner ℂ (adelicCyclicHilbertGenerator f)
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicHilbertGenerator f))) *
      inner ℂ (adelicCyclicHilbertGenerator f) (adelicCyclicHilbertGenerator f) =
    inner ℂ (adelicCyclicHilbertGenerator f)
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicCyclicHilbertGenerator f)) *
    inner ℂ (adelicCyclicHilbertGenerator f)
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicHilbertGenerator f)) := by
  obtain ⟨c, hc⟩ := adelicRotationWeightProjection_realGLOrbit f hf hk g
  exact @unitary_projection_coefficient_factor
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (fun a x y => adelicCyclicHilbertRepresentation_inner f (rationalAdelicFiniteGL2Embedding a) x y)
    (adelicRotationWeightSpace f) inferInstance (adelicRotationWeightSpace_finite_invariant f)
    _ _ (adelicCyclicHilbertGenerator_mem_rotationWeight f hf) c hc a

/-- The actual normalized cusp coefficient is the product of its genuine full real and finite coefficients. -/
theorem adelicNormalizedCuspCoefficient_real_finite (hf : f ≠ 0) (hk : 0 < k)
    (g : GeneralLinearGroup (Fin 2) ℝ) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicNormalizedCuspCoefficient f (adelicRealGL2Embedding g * rationalAdelicFiniteGL2Embedding a) =
      adelicNormalizedCuspCoefficient f (adelicRealGL2Embedding g) *
        adelicNormalizedCuspCoefficient f (rationalAdelicFiniteGL2Embedding a) := by
  rw [(adelicRealGL2_finite_commute g a).eq, mul_comm]
  exact (@representationNormalizedCoefficient_mul_iff RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (adelicCyclicHilbertGenerator f) (adelicCyclicHilbertGenerator_ne_zero f hf) _ _).mpr
    (adelicCyclicFinite_real_coefficient_factor f hf hk a g)

/-- Actual real/finite coordinates reconstruct the original adelic matrix by their genuine embeddings. -/
theorem adelicRealFiniteCoordinates_factor (b : RationalAdelicGL2) :
    adelicRealGL2Embedding (rationalAdelicGL2RealFiniteEquiv b).1 *
      rationalAdelicFiniteGL2Embedding (rationalAdelicGL2RealFiniteEquiv b).2 = b := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  simp only [map_mul, adelicRealGL2Embedding_coordinates, rationalAdelicFiniteGL2Embedding_coordinates,
    Prod.mk_mul_mk, one_mul, mul_one, Prod.eta]

/-- The genuine original coefficient at arbitrary adelic matrices separates into its actual real and finite coordinates. -/
theorem adelicNormalizedCuspCoefficient_coordinates (hf : f ≠ 0) (hk : 0 < k) (b : RationalAdelicGL2) :
    adelicNormalizedCuspCoefficient f b =
      adelicNormalizedCuspCoefficient f (adelicRealGL2Embedding (rationalAdelicGL2RealFiniteEquiv b).1) *
      adelicNormalizedCuspCoefficient f (rationalAdelicFiniteGL2Embedding (rationalAdelicGL2RealFiniteEquiv b).2) :=
  (congrArg (adelicNormalizedCuspCoefficient f) (adelicRealFiniteCoordinates_factor b).symm).trans
    (adelicNormalizedCuspCoefficient_real_finite f hf hk _ _)

/-- The entire actual normalized mixed Gram matrix factors into its original real and finite Gram entries. -/
theorem adelicCyclicUnitReference_realFinite_gram (hf : f ≠ 0) (hk : 0 < k)
    (a b : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    inner ℂ
      (adelicCyclicHilbertRepresentation f (rationalAdelicGL2RealFiniteEquiv.symm a) (adelicCyclicUnitReference f))
      (adelicCyclicHilbertRepresentation f (rationalAdelicGL2RealFiniteEquiv.symm b) (adelicCyclicUnitReference f)) =
    inner ℂ
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding a.1) (adelicCyclicUnitReference f))
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding b.1) (adelicCyclicUnitReference f)) *
    inner ℂ
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.2) (adelicCyclicUnitReference f))
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b.2) (adelicCyclicUnitReference f)) := by
  have hrel := groupHom_relative rationalAdelicGL2RealFiniteEquiv.symm.toMonoidHom a b
  have hleft := adelicCyclicUnitReference_orbit_inner f
    (rationalAdelicGL2RealFiniteEquiv.symm a) (rationalAdelicGL2RealFiniteEquiv.symm b)
  have he := adelicNormalizedCuspCoefficient_coordinates f hf hk
    (rationalAdelicGL2RealFiniteEquiv.symm (a⁻¹ * b))
  simp only [MulEquiv.apply_symm_apply, Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv] at he
  apply hleft.trans ((congrArg (adelicNormalizedCuspCoefficient f) hrel.symm).trans (he.trans _))
  apply congrArg₂ (· * ·)
  · exact (congrArg (adelicNormalizedCuspCoefficient f) (groupHom_relative adelicRealGL2Embedding a.1 b.1)).trans
      (adelicCyclicUnitReference_orbit_inner f _ _).symm
  · exact (congrArg (adelicNormalizedCuspCoefficient f)
      (groupHom_relative rationalAdelicFiniteGL2Embedding a.2 b.2)).trans
      (adelicCyclicUnitReference_orbit_inner f _ _).symm

end
end Dubon2026
