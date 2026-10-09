import Dubon2026.AdelicRealFiniteTensor
import Dubon2026.ContinuousGramClosure

/-! # Actual finite-adelic Gram factorization on every vector of the original full real Hilbert factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual finite translate of an actual real unit-reference orbit is the original mixed-coordinate orbit. -/
theorem adelicFinite_real_unitOrbit (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (g : GeneralLinearGroup (Fin 2) ℝ) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicUnitReference f)) =
      adelicCyclicHilbertRepresentation f (rationalAdelicGL2RealFiniteEquiv.symm (g, a)) (adelicCyclicUnitReference f) := by
  have he : rationalAdelicFiniteGL2Embedding a * adelicRealGL2Embedding g =
      rationalAdelicGL2RealFiniteEquiv.symm (g, a) := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    simp only [map_mul, rationalAdelicFiniteGL2Embedding_coordinates, adelicRealGL2Embedding_coordinates,
      Prod.mk_mul_mk, one_mul, mul_one, MulEquiv.apply_symm_apply]
  have hm := @representation_hom_mul_apply RationalAdelicGL2 RationalAdelicGL2
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertRepresentation f) (MonoidHom.id _) (rationalAdelicFiniteGL2Embedding a)
    (adelicRealGL2Embedding g) (adelicCyclicUnitReference f)
  exact hm.symm.trans (congrArg (fun b : RationalAdelicGL2 =>
    adelicCyclicHilbertRepresentation f b (adelicCyclicUnitReference f)) he)

/-- The original real/finite Gram identity extends faithfully to the entire original real Hilbert closure. -/
theorem adelicFullRealClosure_finite_gram (hf : f ≠ 0) (hk : 0 < k)
    (a b : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (x y : AdelicCyclicHilbert f)
    (hx : x ∈ (adelicFullRealUnitCore f).topologicalClosure)
    (hy : y ∈ (adelicFullRealUnitCore f).topologicalClosure) :
    inner ℂ (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) x)
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b) y) =
      inner ℂ x y * inner ℂ
        (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicCyclicUnitReference f))
        (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b) (adelicCyclicUnitReference f)) := by
  apply @continuous_gram_factor_closure (AdelicCyclicHilbert f) (AdelicCyclicHilbert f)
    (GeneralLinearGroup (Fin 2) ℝ) inferInstance inferInstance inferInstance inferInstance
    (fun g => adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicUnitReference f))
    (adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a))
    (adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding b)) _ _ x y hx hy
  intro g h
  exact (congrArg₂ (inner ℂ) (adelicFinite_real_unitOrbit f a g) (adelicFinite_real_unitOrbit f b h)).trans
    (adelicCyclicUnitReference_realFinite_gram f hf hk (g, a) (h, b))

end
end Dubon2026
