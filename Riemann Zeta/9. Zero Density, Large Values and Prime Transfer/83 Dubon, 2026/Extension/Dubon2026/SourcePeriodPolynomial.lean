/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Polynomial estimates used by the actual period integrand.
Selected from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
injective period pairing -> convergent additive periods of f(z)P(z,1).
Homogeneous scaling supplies the exact slash law. Polynomial growth combines
with the already proved cusp decay to discharge integrability and strip decay.
-/

namespace Dubon2026
open Asymptotics Filter MvPolynomial UpperHalfPlane
open scoped MatrixGroups Manifold

/-- Scaling all variables by `a` scales the value of a degree-`n` homogeneous polynomial
by `a ^ n`, after any change of coefficient ring.

This is not a global `simp` lemma: the degree `n` cannot be inferred from its left-hand side. -/
theorem sourceHomogeneous_eval₂_const_mul {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (g : σ → S) (a : S) :
    _root_.MvPolynomial.eval₂ f (fun i ↦ a * g i) p =
      a ^ n * _root_.MvPolynomial.eval₂ f g p := by
  classical
  simp only [_root_.MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ i ∈ d.support, d i = n := (hp.degree_eq_sum_deg_support hd).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- Scaling the variables of a homogeneous polynomial by a scalar scales its algebra
evaluation by the corresponding power of that scalar. The scalar algebra may differ
from the coefficient algebra. -/
theorem sourceHomogeneous_aeval_smul {σ R S A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A] [Algebra R A] [Algebra S A]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (g : σ → A) (a : S) :
    _root_.MvPolynomial.aeval (a • g) p = a ^ n • _root_.MvPolynomial.aeval g p := by
  rw [Pi.smul_def]
  simpa only [_root_.MvPolynomial.aeval_def, Algebra.smul_def, map_pow] using
    sourceHomogeneous_eval₂_const_mul hp (algebraMap R A) g (algebraMap S A a)

/-- **Polynomial growth of a polynomial in `O(u)` variables.** If each coordinate of `x` is `O(u)`
along `l`, and `1 = O(u)`, then `aeval (x a) P` is `O(u a ^ n)` for every `n ≥ P.totalDegree`. -/
theorem sourceIsBigO_aeval_of_totalDegree_le {α ι R 𝕜 : Type*} [CommSemiring R]
    [SeminormedCommRing 𝕜] [Algebra R 𝕜] {l : Filter α} {P : MvPolynomial ι R} {n : ℕ}
    (hP : P.totalDegree ≤ n) {x : α → ι → 𝕜} {u : α → ℝ} (hx : ∀ i, (fun a ↦ x a i) =O[l] u)
    (hu : (fun _ ↦ (1 : ℝ)) =O[l] u) :
    (fun a ↦ aeval (x a) P) =O[l] fun a ↦ u a ^ n := by
  simp only [aeval_def, eval₂_eq]
  refine IsBigO.sum fun d hd ↦ ?_
  refine IsBigO.const_mul_left ?_ _
  -- each monomial has degree at most `n`
  have hdeg : ∑ i ∈ d.support, d i ≤ n := (le_totalDegree hd).trans hP
  have hprod : (fun a ↦ ∏ i ∈ d.support, x a i ^ d i) =O[l]
      fun a ↦ ∏ i ∈ d.support, u a ^ d i :=
    IsBigO.finsetProd fun i _ ↦ (hx i).pow (d i)
  simp only [Finset.prod_pow_eq_pow_sum] at hprod
  refine hprod.trans ?_
  -- pad the exponent up to `n` using `1 = O(u)`
  calc (fun a ↦ u a ^ ∑ i ∈ d.support, d i)
      = fun a ↦ u a ^ (∑ i ∈ d.support, d i) * (1 : ℝ) ^ (n - ∑ i ∈ d.support, d i) := by simp
    _ =O[l] fun a ↦ u a ^ (∑ i ∈ d.support, d i) * u a ^ (n - ∑ i ∈ d.support, d i) :=
      (isBigO_refl _ _).mul (hu.pow _)
    _ = fun a ↦ u a ^ n := by
      funext a
      rw [← pow_add, Nat.add_sub_cancel' hdeg]
open Asymptotics in
/-- Along the imaginary axis, a polynomial `P` in the numerator `a i t + b` and denominator
`c i t + d` of the Möbius transformation of a real matrix grows at most like `t ^ n` for
`n ≥ P.totalDegree`. -/
theorem sourceIsBigO_aeval_num_denom {R : Type*} [CommSemiring R] [Algebra R ℂ]
    {P : MvPolynomial (Fin 2) R} {n : ℕ} (hP : P.totalDegree ≤ n) (g : GL (Fin 2) ℝ) :
    (fun t : ℝ ↦ MvPolynomial.aeval ![num g (Complex.I * t), denom g (Complex.I * t)] P) =O[atTop]
      fun t ↦ t ^ n := by
  have hI : (fun t : ℝ ↦ Complex.I * (t : ℂ)) =O[atTop] fun t : ℝ ↦ t :=
    isBigO_of_le _ fun t ↦ by simp
  have haffine (a b : ℂ) : (fun t : ℝ ↦ a * (Complex.I * (t : ℂ)) + b) =O[atTop] fun t : ℝ ↦ t :=
    (hI.const_mul_left a).add (isLittleO_const_id_atTop b).isBigO
  refine sourceIsBigO_aeval_of_totalDegree_le hP (fun i ↦ ?_)
    (isLittleO_const_id_atTop (1 : ℝ)).isBigO
  fin_cases i
  · simpa [num] using haffine (g 0 0 : ℂ) (g 0 1 : ℂ)
  · simpa [denom] using haffine (g 1 0 : ℂ) (g 1 1 : ℂ)

/-- For a polynomial `P` in two variables with coefficients mapping to `ℂ`, the function
`z ↦ P(z, 1)` is holomorphic on `ℍ`. -/
lemma sourceMDifferentiable_aeval_coe {R : Type*} [CommSemiring R] [Algebra R ℂ]
    (P : MvPolynomial (Fin 2) R) : MDiff fun z : ℍ ↦ MvPolynomial.aeval ![(z : ℂ), 1] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using mdifferentiable_const
  | add p q hp hq =>
    simp only [map_add]
    exact MDifferentiable.add hp hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    refine MDifferentiable.mul hp ?_
    fin_cases i
    · simpa using mdifferentiable_coe
    · simpa using mdifferentiable_const


end Dubon2026
