import Dubon2026.SourceCurveDifferentSupport
import Dubon2026.SourceCurveCoordinateSupport

/-! DUB-17/18 -> canonical divisors. For the actual finite separable
coordinate extension, the different ideal bounds all nonzero differential
orders on its integral chart. The remaining places are coordinate poles;
their finite support is supplied by the proved principal-divisor theorem.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial KaehlerDifferential
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem finite_differential_support_X
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
    [∀ v : Place K F, Algebra.IsSeparable K v.ResidueField]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hpole : {v : Place K F | v.ord (algebraMap (RatFunc K) F RatFunc.X) < 0}.Finite) :
    {v : Place K F | v.ordDifferential (D K F (algebraMap (RatFunc K) F RatFunc.X)) ≠ 0}.Finite := by
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
  haveI : Module.IsTorsionFree K[X] F := .trans_faithfulSMul K[X] (RatFunc K) F
  haveI : Module.IsTorsionFree K[X] R := IsIntegralClosure.isTorsionFree K[X] F
  haveI : Algebra.IsSeparable (FractionRing K[X]) (FractionRing R) := by
    let e₁ : FractionRing K[X] ≃ₐ[K[X]] RatFunc K := FractionRing.algEquiv _ _
    let e₂ : FractionRing R ≃ₐ[R] F := FractionRing.algEquiv _ _
    apply Algebra.IsSeparable.of_equiv_equiv e₁.symm.toRingEquiv e₂.symm.toRingEquiv
    ext r
    exact IsFractionRing.algEquiv_commutes e₁.symm e₂.symm r
  have he : algebraMap R F (algebraMap K[X] R X) = algebraMap (RatFunc K) F RatFunc.X := by
    change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) = _
    rw [RatFunc.algebraMap_X]
  have hbad := Place.finite_differential_support_on_chart (K := K) (F := F) (R := R)
  refine (hpole.union hbad).subset ?_
  intro v hv
  by_cases hnonneg : 0 ≤ v.ord (algebraMap (RatFunc K) F RatFunc.X)
  · right
    refine ⟨?_, ?_⟩
    · intro c
      apply integralClosure_mem_of_base_mem v _ c
      apply polynomial_mem_of_coordinate_mem v
      change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) ∈ v.toValuationSubring
      rw [RatFunc.algebraMap_X]
      exact v.mem_of_ord_nonneg hnonneg
    · rwa [he]
  · left
    exact lt_of_not_ge hnonneg

end
end Dubon2026.SourceCurve
