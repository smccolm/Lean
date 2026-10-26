import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! DUB-17/18 -> primitive determinant -> the original specialization
fixes the arithmetic projector. Adapt the repository's complex polynomial
intertwiner argument only to the needed zero-action case over the actual
coefficient field; no new spectral decomposition is required. -/
namespace Dubon2026
noncomputable section
open Polynomial
variable {E V W : Type*} [Field E]
variable [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]

theorem specialization_aeval_zero (π : V →ₗ[E] W) (H : Module.End E V)
    (hH : ∀ x, π (H x) = 0) (P : E[X]) (x : V) :
    π (aeval H P x) = P.eval 0 • π x := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, LinearMap.add_apply, hP, hQ, eval_add, add_smul]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    cases n with
    | zero => simp
    | succ n =>
      simp only [map_mul, map_pow, aeval_C, aeval_X, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul, pow_succ', Module.End.mul_apply, hH,
        smul_zero, eval_mul, eval_C, eval_pow, eval_X, zero_mul, mul_zero, zero_smul]

theorem specialization_shifted_squares_zero {I : Type*}
    (π : V →ₗ[E] W) (s : Finset I) (H : I → Module.End E V) (a : I → E)
    (hH : ∀ i ∈ s, ∀ x, π (H i x) = a i • π x) (x : V) :
    π ((∑ i ∈ s, (H i - a i • 1) ^ 2 : Module.End E V) x) = 0 := by
  classical
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hz : ∀ y, π ((H i - a i • 1) y) = 0 := by
    intro y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, hH i hi, sub_self]
  simpa only [pow_two, Module.End.mul_apply] using hz ((H i - a i • 1) x)

end
end Dubon2026
