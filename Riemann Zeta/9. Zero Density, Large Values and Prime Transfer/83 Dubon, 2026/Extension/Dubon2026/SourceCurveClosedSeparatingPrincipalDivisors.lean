import Dubon2026.SourceCurveClosedPrincipalDescent

/-! DUB-17/18 -> original Frobenius/inertia -> residue-curve principal
divisors. The actual finite separating coordinate identifies its rational
subfield with RatFunc, so the proved Galois descent applies to the original
field with its original constant action. No degree-zero hypothesis remains. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem hasPrincipalDivisors_closed_of_separating_coordinate
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    HasPrincipalDivisors K F := by
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
  exact hasPrincipalDivisors_finite_ratfunc_closed K F

end
end Dubon2026.SourceCurve
