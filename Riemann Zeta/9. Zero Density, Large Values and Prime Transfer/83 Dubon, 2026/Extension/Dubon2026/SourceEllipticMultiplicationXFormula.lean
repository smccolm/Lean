import Dubon2026.SourceEllipticDivisionCoprime

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
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)
theorem smul_formula_or_zero {n : ℕ} {x₀ y₀ : K}
    (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀) :
    (((W.baseChange K).ΨSq n).eval x₀ ≠ 0 →
      ∃ (x' y' : K) (h' : (W.baseChange K).toAffine.Nonsingular x' y'),
        n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = Point.some x' y' h' ∧
          x' * ((W.baseChange K).ΨSq n).eval x₀ = ((W.baseChange K).Φ n).eval x₀) ∧
    (((W.baseChange K).ΨSq n).eval x₀ = 0 →
      n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = 0) := by
  have heq : (W.baseChange K).toAffine.Equation x₀ y₀ := h.left
  have hψsq := evalEval_ψ_sq (W.baseChange K) heq (n : ℤ)
  constructor
  ·
    intro hΨ
    have hψ : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ ≠ 0 := by
      intro h0
      exact hΨ (by rw [← hψsq, h0]; exact zero_pow two_ne_zero)
    have key := zsmul_eq_smulEval (W.baseChange K) h (n : ℤ)
    have hVz : smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ≠ 0 := hψ
    have hV := key ▸ ((n : ℤ) • WeierstrassCurve.Jacobian.Point.fromAffine (Point.some x₀ y₀ h)).nonsingular
    have hQeq : ((n : ℤ) • WeierstrassCurve.Jacobian.Point.fromAffine (Point.some x₀ y₀ h)) =
        WeierstrassCurve.Jacobian.Point.mk hV := WeierstrassCurve.Jacobian.Point.ext key
    refine ⟨smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 0 /
        smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ^ 2,
      smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 1 /
        smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ^ 3,
      (WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_, ?_⟩
    · calc n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point)
          = WeierstrassCurve.Jacobian.Point.toAffineAddEquiv (W.baseChange K)
            ((n : ℤ) • WeierstrassCurve.Jacobian.Point.fromAffine (Point.some x₀ y₀ h)) := by
            rw [map_zsmul, ← WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_symm_apply,
              AddEquiv.apply_symm_apply, natCast_zsmul]
        _ = _ := by
            rw [hQeq, WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply]
            exact WeierstrassCurve.Jacobian.Point.toAffineLift_of_Z_ne_zero hVz
    · show ((W.baseChange K).φ (n : ℤ)).evalEval x₀ y₀ /
          ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ ^ 2 *
          ((W.baseChange K).ΨSq (n : ℤ)).eval x₀ =
          ((W.baseChange K).Φ (n : ℤ)).eval x₀
      rw [← hψsq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ),
        evalEval_φ (W.baseChange K) heq]
  ·
    intro hΨ
    have hψ0 : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ = 0 :=
      sq_eq_zero_iff.mp (hψsq.trans hΨ)
    rw [← natCast_zsmul]
    exact (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) h (n : ℤ)).mpr hψ0

theorem smul_x_eq {n : ℕ} {x₀ y₀ : K}
    (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀)
    (hns : ((W.baseChange K).ΨSq n).eval x₀ ≠ 0) :
    ∃ (x' y' : K) (h' : (W.baseChange K).toAffine.Nonsingular x' y'),
      n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = Point.some x' y' h' ∧
        x' * ((W.baseChange K).ΨSq n).eval x₀ = ((W.baseChange K).Φ n).eval x₀ :=
  (smul_formula_or_zero W h).1 hns


end
end Dubon2026.SourceEllipticTorsion
