import Dubon2026.SourceFiniteDivisorEvaluationPushforward
import Dubon2026.SourceOriginalEvaluationRestriction
import Dubon2026.SourceOriginalWeilEvaluation

/-! DUB-17/18 -> original Weil reciprocity and Hecke adjointness ->
evaluation on pushed-forward divisors. Actual residue restriction gives
the function values; disjointness from the function divisor gives the
nonvanishing needed when integer divisor coefficients cancel in a fiber. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M]

theorem originalDivisorEval_geometricPushforwardAlong
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (D : Divisor L (modularFunctionFieldOver M L))
    (f : modularFunctionFieldOver N L) (hf : f ≠ 0)
    (hord : ∀ w ∈ D.support, w.ord (φ f) = 0) :
    originalDivisorEval N L f
      (Divisor.geometricPushforwardAlong φ (original_field_hom_finite L N M φ) D) =
        originalDivisorEval M L (φ f) D := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    original_field_hom_finite L N M φ
  haveI : Algebra.IsSeparable (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    Algebra.IsSeparable.of_integral _ _
  have hn (w : Place L (modularFunctionFieldOver M L)) (hw : w ∈ D.support) :
      originalPlaceEval N L (w.restrictAlong φ (original_field_hom_finite L N M φ)) f ≠ 0 := by
    rw [← originalPlaceEval_map_restrictAlong L N M φ w f]
    exact originalPlaceEval_ne_zero_of_ord_eq_zero M L w ((map_ne_zero φ).mpr hf) (hord w hw)
  change (D.mapDomain (fun w => w.restrictAlong φ (original_field_hom_finite L N M φ))).prod
    (fun v n => originalPlaceEval N L v f ^ n) = _
  rw [finsupp_prod_zpow_mapDomain _ _ _ hn]
  apply Finsupp.prod_congr
  intro w _
  rw [originalPlaceEval_map_restrictAlong L N M φ w f]

end
end Dubon2026.SourceFunctionField
