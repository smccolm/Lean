import Dubon2026.SourceEllipticVeluCoefficients
import Dubon2026.SourceEllipticMultiplicationXFormula

/-! Reuse the already proved point-multiplication formula for the doubling
numerator needed in the odd-degree quotient discriminant argument. Native
division-polynomial identities provide the quartic without a new expanded
certificate. The formula retains all characteristics and is used by the
odd-prime quotient and inertia-census chain for DUB-17 / DUB-18. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem double_x_mul_psi2Sq {x y : F} (heq : W.toAffine.Equation x y)
    (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) *
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) =
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  have hns : W.toAffine.Nonsingular x y :=
    (WeierstrassCurve.Affine.nonsingular_iff x y).mpr ⟨heq, Or.inr hy⟩
  have hg : veluGy W x y ≠ 0 := by
    intro hg
    apply hy
    simp only [veluGy] at hg
    simp only [WeierstrassCurve.Affine.negY]
    linear_combination -hg
  have hψ : (W.ΨSq 2).eval x ≠ 0 := by
    rw [ΨSq_two, ← veluU_eq_Ψ₂Sq_eval W heq]
    exact pow_ne_zero 2 hg
  obtain ⟨x', y', h', hP, hx⟩ :=
    Dubon2026.SourceEllipticTorsion.smul_x_eq (K := F) (n := 2) W hns hψ
  change (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hns : W.toAffine.Point) =
    WeierstrassCurve.Affine.Point.some x' y' h' at hP
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy] at hP
  have hxx := congrArg (fun P : W.toAffine.Point =>
    match P with | .zero => 0 | .some a _ _ => a) hP
  change W.toAffine.addX x x (W.toAffine.slope x x y y) = x' at hxx
  change x' * (W.ΨSq 2).eval x = (W.Φ 2).eval x at hx
  rw [← hxx, ΨSq_two, Φ_two] at hx
  simpa only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X,
    eval_C, eval_sub] using hx

end
end Dubon2026.SourceEllipticVelu
