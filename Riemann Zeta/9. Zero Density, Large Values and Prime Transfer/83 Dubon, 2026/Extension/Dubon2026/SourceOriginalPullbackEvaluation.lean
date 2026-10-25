import Dubon2026.SourceCurvePullbackEvaluationProduct
import Dubon2026.SourceOriginalNormEvaluation
import Dubon2026.SourceOriginalWeilEvaluation

/-! DUB-17/18 -> original Frobenius determinant -> Weil reciprocity and
Hecke adjointness -> evaluation on pulled-back divisors. Apply the proved
original field-norm formula to every actual fiber in the existing divisor
pullback. Finiteness and residue identifications are already discharged;
only regularity on the fibers above the divisor support is required. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M]

theorem originalDivisorEval_finitePullbackAlong
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (D : Divisor L (modularFunctionFieldOver N L)) (f : modularFunctionFieldOver M L)
    (hord : ∀ v ∈ D.support, ∀ w : Place L (modularFunctionFieldOver M L),
      w.restrictAlong φ (original_field_hom_finite L N M φ) = v → 0 ≤ w.ord f) :
    letI := algebraAlong φ
    originalDivisorEval M L f
      (Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D) =
        originalDivisorEval N L (Algebra.norm (modularFunctionFieldOver N L) f) D := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    original_field_hom_finite L N M φ
  haveI : Algebra.IsSeparable (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    Algebra.IsSeparable.of_integral _ _
  change (Divisor.finitePullback (modularFunctionFieldOver M L) D).prod
    (fun w n => originalPlaceEval M L w f ^ n) = _
  rw [Divisor.finitePullback_prod_zpow]
  apply Finset.prod_congr rfl
  intro v hv
  exact congrArg (fun a : L => a ^ D v)
    (originalPlaceEval_normAlong_eq_finprod_fiber L N M φ v f (hord v hv)).symm

end
end Dubon2026.SourceFunctionField
