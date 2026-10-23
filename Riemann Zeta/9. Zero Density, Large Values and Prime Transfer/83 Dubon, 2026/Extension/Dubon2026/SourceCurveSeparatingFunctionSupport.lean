import Dubon2026.SourceCurveIntegralCoordinateFunctionSupport
import Dubon2026.SourceCurveSeparatingCoordinateSupport
import Dubon2026.SourceCurveTranscendentalDegree

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> principal
divisor finite support in residue characteristic. A single separating
coordinate suffices: its finite set of poles and the integral chart cover
all actual places. Arbitrary functions need not themselves be separating. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem finite_function_support_of_separating_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F]
    (f : F) : {v : Place K F | v.ord f ≠ 0}.Finite := by
  have hti : Transcendental K t⁻¹ := fun hi => ht (IsAlgebraic.inv_iff.mp hi)
  haveI : FiniteDimensional K⟮t⁻¹⟯ F := by rw [adjoin_singleton_inv_eq]; infer_instance
  haveI : Algebra.IsSeparable K⟮t⁻¹⟯ F := by rw [adjoin_singleton_inv_eq]; infer_instance
  have hneg := finite_places_positive_of_separating_coordinate t⁻¹ hti
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
  have hchart := finite_function_support_where_coordinate_integral (K := K) f
  rw [he] at hchart
  refine (hchart.union hneg).subset ?_
  intro v hv
  by_cases htmem : t ∈ v.toValuationSubring
  · exact Or.inl ⟨htmem, hv⟩
  · apply Or.inr
    change 0 < v.ord t⁻¹
    rw [v.ord_inv]
    have hlt : v.ord t < 0 := lt_of_not_ge (fun h => htmem (v.mem_of_ord_nonneg h))
    omega

end
end Dubon2026.SourceCurve
