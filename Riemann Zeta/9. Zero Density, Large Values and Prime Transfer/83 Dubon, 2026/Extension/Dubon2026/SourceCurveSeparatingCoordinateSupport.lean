import Dubon2026.SourceCurveCoordinateSupport

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> principal
divisor finite support. The existing rational-chart proof needs separability,
not characteristic zero. Explicit transport along the rational-coordinate
equivalence permits its use for the proved separating residue-field j. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem finite_places_positive_of_separating_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F] :
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
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have he : algebraMap (RatFunc K) F RatFunc.X = t := by
    show ((RatFunc.algEquivOfTranscendental t ht RatFunc.X : K⟮t⟯) : F) = t
    rw [RatFunc.algEquivOfTranscendental_X]
  simpa only [he] using (finite_places_positive_X (K := K) (F := F))

end
end Dubon2026.SourceCurve
