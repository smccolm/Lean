import Dubon2026.SourceJointReductionPoleCharts
import Dubon2026.SourceCurveLocalDifferentials

/-! DUB-17/18 -> Picard torsion injectivity -> original-field Kummer
power lifting -> genus inequality -> two-chart dimension comparison.
These helpers identify the actual residue chart windows with products of
pole spaces. Adapted from Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Existing valuation-ring closure
replaces separate order-addition and scalar-order lemmas. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open Polynomial
universe u v w

section General

variable {k : Type u} [Field k] {ι : Type v} {Fb : ι → Type w} [∀ i, Field (Fb i)]
  [∀ i, Algebra k (Fb i)]

/-- Multiply every residue component by a nonzero coordinate. -/
def mulEquiv (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) : (∀ i, Fb i) ≃ₗ[k] (∀ i, Fb i) where
  toFun x := u * x
  invFun x := u⁻¹ * x
  map_add' x y := mul_add u x y
  map_smul' c x := by
    ext i
    simp [Pi.smul_apply]
  left_inv x := by
    ext i
    simp [hu i]
  right_inv x := by
    ext i
    simp [hu i]

@[scoped simp] theorem mulEquiv_apply (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (x : ∀ i, Fb i) :
    mulEquiv (k := k) u hu x = u * x := rfl

theorem inv_ne_zero_pi {u : ∀ i, Fb i} (hu : ∀ i, u i ≠ 0) : ∀ i, u⁻¹ i ≠ 0 := fun i => by
  simpa using inv_ne_zero (hu i)

theorem mulEquiv_symm_eq (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) :
    ((mulEquiv (k := k) u hu).symm : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) =
      (mulEquiv (k := k) u⁻¹ (inv_ne_zero_pi hu) : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) :=
  LinearMap.ext fun _ => rfl

theorem mulEquiv_pow_apply (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (M : ℕ) (x : ∀ i, Fb i) :
    ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M) x = u ^ M * x := by
  induction M generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, LinearEquiv.coe_coe, mulEquiv_apply, ih, pow_succ]
    ring

theorem aeval_mulEquiv_apply (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (c : k[X]) (x : ∀ i, Fb i) :
    Polynomial.aeval (mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) c x =
      fun i => Polynomial.aeval (u i) c * x i := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq =>
    ext i
    simp only [map_add, LinearMap.add_apply, hp, hq, Pi.add_apply, add_mul]
  | monomial n a =>
    ext i
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, mulEquiv_pow_apply,
      Module.algebraMap_end_apply, Polynomial.aeval_monomial]
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, Algebra.smul_def]
    ring

/-- Simultaneous nonnegative orders on the selected residue places. -/
def ordSub (s : ∀ i, Place k (Fb i) → Prop) : Submodule k (∀ i, Fb i) where
  carrier := {h | ∀ i (w : Place k (Fb i)), s i w → 0 ≤ w.ord (h i)}
  add_mem' {a b} ha hb i w hw :=
    w.ord_nonneg_of_mem (add_mem (w.mem_of_ord_nonneg (ha i w hw))
      (w.mem_of_ord_nonneg (hb i w hw)))
  zero_mem' i w _ := by rw [Pi.zero_apply, Place.ord_zero]
  smul_mem' c a ha i w hw := by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact w.ord_nonneg_of_mem (mul_mem (w.algebraMap_mem' c)
      (w.mem_of_ord_nonneg (ha i w hw)))

theorem ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (g : F) (n : ℕ) :
    v.ord (g ^ n) = n * v.ord g := by
  simpa using Place.ord_zpow v g (n : ℤ)

end General

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
