import Dubon2026.SourceLaurentCoefficientIndependence
import Dubon2026.SourceLaurentEuler
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Module.LinearMap.Rat

/-! DUB-17/18 -> actual Hecke norm -> coefficient extension of Atkin-Lehner.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_GeometricBaseChange.lean. The existing local
coefficient-independence theorem supplies tensor injectivity. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped TensorProduct
open IntermediateField

variable (L : Type*) [Field L]

private theorem algebraMap_mul_eq_smul (c : L) (y : LaurentSeries L) :
    algebraMap L (LaurentSeries L) c * y = c • y := by
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, HahnSeries.single_zero_mul_eq_smul]

variable [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

/-- Evaluate the actual rational tensor product by constant multiplication and Laurent coefficient embedding. -/
def baseChangeRatAlgHom : L ⊗[ℚ] F₀ →ₐ[ℚ] LaurentSeries L :=
  Algebra.TensorProduct.productMap (algebraMap L (LaurentSeries L)).toRatAlgHom
    ((coeffEmb L).comp (F₀.val : F₀ →+* LaurentSeries ℚ)).toRatAlgHom

theorem baseChangeRatAlgHom_tmul (c : L) (f : F₀) :
    baseChangeRatAlgHom L F₀ (c ⊗ₜ f) =
      algebraMap L (LaurentSeries L) c * coeffEmb L (f : LaurentSeries ℚ) :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ c f

/-- The actual tensor evaluation as a homomorphism over the coefficient field. -/
def baseChangeHom : L ⊗[ℚ] F₀ →ₐ[L] LaurentSeries L :=
  { baseChangeRatAlgHom L F₀ with
    commutes' := fun c => by
      change baseChangeRatAlgHom L F₀ (algebraMap L (L ⊗[ℚ] F₀) c) =
        algebraMap L (LaurentSeries L) c
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        baseChangeRatAlgHom_tmul, OneMemClass.coe_one, map_one, mul_one] }

@[simp]
theorem baseChangeHom_tmul (c : L) (f : F₀) :
    baseChangeHom L F₀ (c ⊗ₜ f) =
      algebraMap L (LaurentSeries L) c * coeffEmb L (f : LaurentSeries ℚ) :=
  baseChangeRatAlgHom_tmul L F₀ c f

theorem baseChangeHom_one_tmul (f : F₀) :
    baseChangeHom L F₀ (1 ⊗ₜ f) = coeffEmb L (f : LaurentSeries ℚ) := by
  rw [baseChangeHom_tmul, map_one, one_mul]

private def baseChangeLinear : L ⊗[ℚ] F₀ →ₗ[L] LaurentSeries L where
  toFun := baseChangeHom L F₀
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, ← algebraMap_mul_eq_smul, ← (baseChangeHom L F₀).commutes c,
      ← map_mul, ← Algebra.smul_def]

private theorem baseChangeLinear_apply (x : L ⊗[ℚ] F₀) :
    baseChangeLinear L F₀ x = baseChangeHom L F₀ x := rfl

private def valRatLinear : F₀ →ₗ[ℚ] LaurentSeries ℚ :=
  ((F₀.val : F₀ →+* LaurentSeries ℚ) : F₀ →+ LaurentSeries ℚ).toRatLinearMap

private theorem valRatLinear_apply (f : F₀) : valRatLinear F₀ f = (f : LaurentSeries ℚ) := rfl

private theorem baseChangeLinear_injective : Function.Injective (baseChangeLinear L F₀) := by
  classical
  let bF := Module.Free.chooseBasis ℚ F₀
  let B := Algebra.TensorProduct.basis L bF
  have hli : LinearIndependent L (baseChangeLinear L F₀ ∘ B) := by
    have h : (baseChangeLinear L F₀ ∘ B : _ → LaurentSeries L) =
        fun i => coeffEmb L (valRatLinear F₀ (bF i)) := by
      funext i
      rw [Function.comp_apply, baseChangeLinear_apply, Algebra.TensorProduct.basis_apply,
        baseChangeHom_one_tmul, valRatLinear_apply]
    rw [h]
    refine linearIndependent_coeffEmb L ?_
    refine bF.linearIndependent.map' (valRatLinear F₀) (LinearMap.ker_eq_bot.mpr ?_)
    exact Subtype.val_injective
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hrepr : Finsupp.linearCombination L (baseChangeLinear L F₀ ∘ B) (B.repr x) = 0 := by
    rw [← Finsupp.apply_linearCombination, B.linearCombination_repr]
    exact hx
  have h0 : B.repr x = 0 := linearIndependent_iff.mp hli (B.repr x) hrepr
  rw [← B.linearCombination_repr x, h0, map_zero]

theorem baseChangeHom_injective : Function.Injective (baseChangeHom L F₀) :=
  baseChangeLinear_injective L F₀

theorem baseChangeHom_mem (x : L ⊗[ℚ] F₀) :
    baseChangeHom L F₀ x ∈ laurentBaseChange L F₀ := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c f =>
      rw [baseChangeHom_tmul]
      exact mul_mem ((laurentBaseChange L F₀).algebraMap_mem c)
        (coeffEmb_mem_laurentBaseChange L f.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

end
end Dubon2026.SourceFunctionField
