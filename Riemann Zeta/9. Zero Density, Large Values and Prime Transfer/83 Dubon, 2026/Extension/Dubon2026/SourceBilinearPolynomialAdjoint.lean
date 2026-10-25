import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! DUB-17/18 -> primitive determinant -> self-adjointness of the primitive
Tate projector. Only polynomials in the constructed good-prime operator
are needed; adjointness of the full Hecke algebra is not assumed. -/
namespace Dubon2026
noncomputable section
open Polynomial
variable {R V W : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem bilinear_selfAdjoint_pow (B : V →ₗ[R] V →ₗ[R] W)
    (H : Module.End R V) (hH : B.IsSelfAdjoint H) (n : ℕ) :
    B.IsSelfAdjoint (H ^ n : Module.End R V) := by
  induction n with
  | zero => exact LinearMap.isAdjointPair_one
  | succ n hn =>
    have h := LinearMap.IsAdjointPair.mul hn hH
    simpa only [← pow_succ, ← pow_succ'] using h

theorem bilinear_selfAdjoint_aeval (B : V →ₗ[R] V →ₗ[R] W)
    (H : Module.End R V) (hH : B.IsSelfAdjoint H) (P : R[X]) :
    B.IsSelfAdjoint (aeval H P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [map_add] using (B.selfAdjointSubmodule).add_mem hP hQ
  | monomial n a =>
    have h := (B.selfAdjointSubmodule).smul_mem a (bilinear_selfAdjoint_pow B H hH n)
    simpa only [aeval_monomial, Algebra.smul_def] using h

theorem bilinear_selfAdjoint_sum_shifted_squares {I : Type*}
    (B : V →ₗ[R] V →ₗ[R] W) (s : Finset I)
    (H : I → Module.End R V) (a : I → R)
    (hH : ∀ i ∈ s, B.IsSelfAdjoint (H i)) :
    B.IsSelfAdjoint (∑ i ∈ s, (H i - a i • 1) ^ 2 : Module.End R V) := by
  apply (B.selfAdjointSubmodule).sum_mem
  intro i hi
  apply bilinear_selfAdjoint_pow
  exact (B.selfAdjointSubmodule).sub_mem (hH i hi)
    ((B.selfAdjointSubmodule).smul_mem (a i) LinearMap.isAdjointPair_one)

end
end Dubon2026
