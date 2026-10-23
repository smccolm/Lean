import Dubon2026.SourceEllipticNumeratorCoprime

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
theorem smul_eq_zero_of_ΨSq_eval_eq_zero {n : ℕ}
    {x₀ y₀ : K} (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀)
    (hz : ((W.baseChange K).ΨSq n).eval x₀ = 0) :
    n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = 0 :=
  (smul_formula_or_zero W h).2 hz

end
end Dubon2026.SourceEllipticTorsion
