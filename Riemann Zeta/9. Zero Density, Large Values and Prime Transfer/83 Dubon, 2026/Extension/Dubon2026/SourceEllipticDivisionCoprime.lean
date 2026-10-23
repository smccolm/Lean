import Dubon2026.SourceEllipticDivisionZeros
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction ->
reverse genus -> finite exceptional fibers -> elliptic inertia orbits ->
actual torsion cardinality. The proved actual point-multiplication formula
now controls the native univariate division polynomials and their fibers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean. -/
namespace Dubon2026.SourceEllipticTorsion
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticPointFormula
noncomputable section
/-- Native ellipticity is preserved by the actual coefficient-field base change. -/
instance baseChangeElliptic {F K : Type*} [Field F] [Field K] [Algebra F K]
    (W : WeierstrassCurve F) [W.IsElliptic] : (W.baseChange K).IsElliptic :=
  inferInstanceAs (W.map (algebraMap F K)).IsElliptic

section
variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
theorem sub_negY_sq_eq_Ψ₂Sq_eval {x y : F} (e : W.Equation x y) :
    (y - W.negY x y) ^ 2 = (WeierstrassCurve.Ψ₂Sq W).eval x := by
  rw [equation_iff] at e
  simp only [negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * e


end

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)
omit [DecidableEq K] in
theorem ΨSq_eval_eq_zero_of_preΨ {m : ℕ} {x₀ : K}
    (h : ((W.baseChange K).preΨ (m : ℤ)).eval x₀ = 0) :
    ((W.baseChange K).ΨSq m).eval x₀ = 0 := by
  rw [preΨ_ofNat] at h
  rw [ΨSq_ofNat, eval_mul, eval_pow, h, zero_pow two_ne_zero, zero_mul]

variable [IsAlgClosed K]

theorem isCoprime_ΨSq_succ [W.IsElliptic] (n : ℕ) :
    IsCoprime ((W.baseChange K).ΨSq n) ((W.baseChange K).ΨSq (n + 1)) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
  intro x₀
  by_contra hcon
  push Not at hcon
  obtain ⟨hn0, hn1⟩ := hcon
  rw [coe_aeval_eq_eval] at hn0 hn1

  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
    (C (1 : K) * X ^ 2 + C ((W.baseChange K).a₁ * x₀ + (W.baseChange K).a₃) * X +
      C (-(x₀ ^ 3 + (W.baseChange K).a₂ * x₀ ^ 2 + (W.baseChange K).a₄ * x₀ +
        (W.baseChange K).a₆)))
    (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  have heq : (W.baseChange K).toAffine.Equation x₀ y₀ := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [IsRoot.def, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hy₀
    linear_combination hy₀
  have hns : (W.baseChange K).toAffine.Nonsingular x₀ y₀ :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq

  have hψ0 : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ = 0 := by
    have h2 := evalEval_ψ_sq (W.baseChange K) heq (n : ℤ)
    rw [hn0] at h2
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hψ1 : ((W.baseChange K).ψ ((n : ℤ) + 1)).evalEval x₀ y₀ = 0 := by
    have h2 := evalEval_ψ_sq (W.baseChange K) heq ((n : ℤ) + 1)
    rw [hn1] at h2
    exact (pow_eq_zero_iff two_ne_zero).mp h2

  have h0 : (n : ℤ) • (WeierstrassCurve.Affine.Point.some x₀ y₀ hns) = 0 :=
    (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) hns (n : ℤ)).mpr hψ0
  have h1 : ((n : ℤ) + 1) • (WeierstrassCurve.Affine.Point.some x₀ y₀ hns) = 0 :=
    (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) hns ((n : ℤ) + 1)).mpr hψ1
  have hP : (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : (W.baseChange K).toAffine.Point) = 0 := by
    have hsub := sub_smul ((n : ℤ) + 1) (n : ℤ) (WeierstrassCurve.Affine.Point.some x₀ y₀ hns)
    rw [h1, h0, sub_zero, add_sub_cancel_left, one_smul] at hsub
    exact hsub
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns hP


end
end Dubon2026.SourceEllipticTorsion
