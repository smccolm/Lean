import Dubon2026.SourceEllipticGenericProjectiveAddition

/-! The actual division-polynomial multiplication formula at every
nonsingular Weierstrass point. Universal integral group-law identities
specialize through the actual coordinate ring, including characteristics
two and three; the native point group then gives multiplication by every
integer. Its zero criterion is the required input for torsion cardinality.
This serves DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 through the finite
exceptional-fiber census, reverse genus, good reduction and continuation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. -/
namespace Dubon2026.SourceEllipticPointFormula
open WeierstrassCurve Polynomial Dubon2026.SourceEllipticDivision
open WeierstrassCurve.Jacobian
open Dubon2026.SourceEllipticUniversal Dubon2026.SourceEllipticUniversal.JacobianFormula
open scoped Polynomial.Bivariate nonZeroDivisors
noncomputable section
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}

variable (x y) in

/-- The actual integral division-polynomial triple evaluated at a point. -/
abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, (ωe W) n, W.ψ n]

variable {W} (eqn : W.toAffine.Equation x y)

open Dubon2026.SourceEllipticUniversal Dubon2026.SourceEllipticUniversal.JacobianFormula WeierstrassCurve.Jacobian

theorem ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by

  conv_rhs => rw [smulEval, ← map_specialize W, map_φ, map_ωe, map_ψ, ← coe_mapRingHom,
    ← WeierstrassCurve.Jacobian.comp_fin3, ← Function.comp_assoc, ← smulPoly, ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]

theorem ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

include eqn in
theorem dblXYZ_smulEval (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

include eqn in
theorem addXYZ_smulEval (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by

  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← WeierstrassCurve.Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]

  simp_rw [curveRing_map_ringEval]

include eqn in
theorem addXYZ_smulEval₁ (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]


end
end Dubon2026.SourceEllipticPointFormula
