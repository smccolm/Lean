import Dubon2026.SourceCurvePositiveDegree

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> principal
divisor degree zero in residue characteristic. Reuse the proved rational
chart ramification/inertia degree sum with explicit coordinate separability.
This supports the rational-function base of the Galois-closure argument;
arbitrary nonseparating function coordinates are not assumed separable. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem sum_positive_orders_eq_finrank_separating
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ F]
    [Algebra.IsSeparable K⟮t⟯ F] :
    (∑ᶠ v : {v : Place K F // 0 < v.ord t},
      v.1.ord t * (Module.finrank K v.1.ResidueField : ℤ)) =
        (Module.finrank K⟮t⟯ F : ℤ) := by
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
  have hd : Module.finrank K⟮t⟯ F = Module.finrank (RatFunc K) F :=
    Algebra.finrank_eq_of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have h := sum_positive_orders_X_eq_finrank (K := K) (F := F)
  rw [he, ← hd] at h
  exact h

end
end Dubon2026.SourceCurve
