import Dubon2026.SourceCurveCoordinateDifferentialSupport

/-! DUB-17/18 -> canonical divisors. Transport the finite different-ideal
and pole-locus argument to any actual transcendental coordinate, preserving
the literal differential and normalized local orders.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential

theorem finite_differential_support_of_finite_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (t : F) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ F]
    [∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
    [∀ v : Place K F, Algebra.IsSeparable K v.ResidueField]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hpole : {v : Place K F | v.ord t < 0}.Finite) :
    {v : Place K F | v.ordDifferential (D K F t) ≠ 0}.Finite := by
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
  rw [← he] at hpole ⊢
  exact finite_differential_support_X hpole

end
end Dubon2026.SourceCurve
