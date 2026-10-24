import Dubon2026.SourceCurveCoordinateExchange
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! The actual image of a transcendental coordinate still generates the
coefficient field over which its algebraic closure is algebraic. Native
rational-function equivalences and scalar-compatible algebraicity transport
supply this one closure-change input for the all-level cyclic-root theorem. -/

namespace Dubon2026.SourceEllipticCyclicCount
open IntermediateField
open scoped IntermediateField
noncomputable section

/-- An algebraic extension of the original j-field is algebraic over its actual image coordinate field. -/
theorem isAlgebraic_mapped_coordinate_field
    {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K F]
    (j : F) (hj : Transcendental K j)
    [Algebra K Ω] [Algebra K⟮j⟯ Ω] [IsScalarTower K K⟮j⟯ Ω]
    [Algebra.IsAlgebraic K⟮j⟯ Ω] :
    Algebra.IsAlgebraic K⟮algebraMap K⟮j⟯ Ω (AdjoinSimple.gen K j)⟯ Ω := by
  let t := algebraMap K⟮j⟯ Ω (AdjoinSimple.gen K j)
  have hgen : Transcendental K (AdjoinSimple.gen K j) :=
    (transcendental_algebraMap_iff (algebraMap K⟮j⟯ F).injective).mp hj
  have ht : Transcendental K t :=
    (transcendental_algebraMap_iff (algebraMap K⟮j⟯ Ω).injective).mpr hgen
  let e : K⟮j⟯ ≃ₐ[K] K⟮t⟯ :=
    (RatFunc.algEquivOfTranscendental j hj).symm.trans (RatFunc.algEquivOfTranscendental t ht)
  have he : (K⟮t⟯.val : K⟮t⟯ →ₐ[K] Ω).comp e.toAlgHom =
      IsScalarTower.toAlgHom K K⟮j⟯ Ω := by
    apply adjoin_algHom_ext K
    intro x hx
    have hxj : x = j := Set.mem_singleton_iff.mp hx
    subst x
    change (e (AdjoinSimple.gen K j) : Ω) = t
    dsimp only [e, AlgEquiv.trans_apply]
    rw [RatFunc.algEquivOfTranscendental_symm_gen]
    exact RatFunc.algEquivOfTranscendental_X t ht
  have hr : (algebraMap K⟮t⟯ Ω).comp e.toRingEquiv.toRingHom =
      (RingEquiv.refl Ω).toRingHom.comp (algebraMap K⟮j⟯ Ω) :=
    congrArg AlgHom.toRingHom he
  exact (Algebra.isAlgebraic_ringHom_iff_of_comp_eq e.toRingEquiv (RingEquiv.refl Ω) hr).mpr inferInstance

end
end Dubon2026.SourceEllipticCyclicCount
