import Dubon2026.SourceCurveLocalFinite

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy/residual association -> original Frobenius/inertia
-> good reduction -> reverse genus inequality -> local differential orders.
Reuse the existing finite separable rational chart theorem with an explicit
separating coordinate. The two actual j charts supply these hypotheses in
residue characteristic; no general inseparable local-chart result is needed. -/
namespace Dubon2026.SourceCurve
noncomputable section

theorem essFiniteType_place_of_separating_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (v : Place K F) (hv : t ∈ v.toValuationSubring) :
    Algebra.EssFiniteType K v.toValuationSubring := by
  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K {t} :=
    RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F :=
    ((algebraMap (IntermediateField.adjoin K {t}) F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
      (e.symm.toRingEquiv : IntermediateField.adjoin K {t} →+* RatFunc K) =
        RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap (IntermediateField.adjoin K {t}) F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap (IntermediateField.adjoin K {t}) F (e (e.symm a)) =
      algebraMap (IntermediateField.adjoin K {t}) F a
    rw [e.apply_symm_apply]
  letI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap K F a = algebraMap (IntermediateField.adjoin K {t}) F (e (algebraMap K (RatFunc K) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  apply essFiniteType_place_of_mem_X v
  have he : algebraMap (RatFunc K) F RatFunc.X = t := by
    show ((RatFunc.algEquivOfTranscendental t ht RatFunc.X : IntermediateField.adjoin K {t}) : F) = t
    rw [RatFunc.algEquivOfTranscendental_X]
  rwa [he]

end
end Dubon2026.SourceCurve
