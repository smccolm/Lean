import Dubon2026.SourceCurveCoordinateSupport

/-! DUB-17/18 -> regular differential geometry -> principal divisors ->
finite support. The actual transcendental coordinate identifies its rational
subfield with RatFunc. The finite integral-closure chart then bounds the
positive support. No classification of all rational places is needed.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem finite_places_positive_of_finite_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] :
    {v : Place K F | 0 < v.ord t}.Finite := by
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
      (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K) =
        RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  letI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F := inferInstance
  have he : algebraMap (RatFunc K) F RatFunc.X = t := by
    show ((RatFunc.algEquivOfTranscendental t ht RatFunc.X : K⟮t⟯) : F) = t
    rw [RatFunc.algEquivOfTranscendental_X]
  simpa only [he] using (finite_places_positive_X (K := K) (F := F))

end
end Dubon2026.SourceCurve
