import Dubon2026.SourceCurveLocalChart
import Dubon2026.SourceCurveCoordinateSupport
import Mathlib.RingTheory.Kaehler.Basic

/-! DUB-17/18 -> canonical divisors -> local integral differentials.
An actual finite separable coordinate extension supplies a finite integral
chart. Its localization proves essential finite type of each place containing
the coordinate, which gives a finite local differential module.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial KaehlerDifferential

theorem essFiniteType_place_of_mem_X
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    (v : Place K F) (hX : algebraMap (RatFunc K) F RatFunc.X ∈ v.toValuationSubring) :
    Algebra.EssFiniteType K v.toValuationSubring := by
  letI : Algebra K[X] F := ((algebraMap (RatFunc K) F).comp
    (algebraMap K[X] (RatFunc K))).toAlgebra
  letI : IsScalarTower K[X] (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K F a = algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) (C a))
    rw [← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
      ← IsScalarTower.algebraMap_apply K (RatFunc K) F]
  let R := integralClosure K[X] F
  haveI : IsDedekindDomain R := integralClosure.isDedekindDomain K[X] (RatFunc K) F
  haveI : IsFractionRing R F := integralClosure.isFractionRing_of_finite_extension (RatFunc K) F
  haveI : Module.Finite K[X] R := IsIntegralClosure.finite K[X] (RatFunc K) F R
  haveI : Algebra.EssFiniteType K R := Algebra.EssFiniteType.comp K K[X] R
  apply v.essFiniteType_of_chart (R := R)
  intro c
  apply integralClosure_mem_of_base_mem v _ c
  apply polynomial_mem_of_coordinate_mem v
  change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) ∈ v.toValuationSubring
  rwa [RatFunc.algebraMap_X]

theorem essFiniteType_place_of_finite_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
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
  haveI : Algebra.IsSeparable (RatFunc K) F := inferInstance
  apply essFiniteType_place_of_mem_X v
  have he : algebraMap (RatFunc K) F RatFunc.X = t := by
    show ((RatFunc.algEquivOfTranscendental t ht RatFunc.X : IntermediateField.adjoin K {t}) : F) = t
    rw [RatFunc.algEquivOfTranscendental_X]
  rwa [he]

end
end Dubon2026.SourceCurve
