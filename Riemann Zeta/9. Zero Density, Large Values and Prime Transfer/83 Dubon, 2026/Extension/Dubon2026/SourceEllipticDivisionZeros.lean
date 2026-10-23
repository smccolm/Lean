import Dubon2026.SourceEllipticPointMultiplication

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
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in

theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h0 : W.toAffine.polynomial.eval₂ (evalRingHom x) y = 0 := by
    rw [eval₂_evalRingHom]; exact h
  let e : W.toAffine.CoordinateRing →+* F := AdjoinRoot.lift (evalRingHom x) y h0
  have he : ∀ p : F[X][Y], e (WeierstrassCurve.Affine.CoordinateRing.mk W p) = p.evalEval x y := fun p ↦ by
    show AdjoinRoot.lift (evalRingHom x) y h0 (AdjoinRoot.mk _ p) = _
    rw [AdjoinRoot.lift_mk, eval₂_evalRingHom]
  calc ((W.ψ n).evalEval x y) ^ 2
      = e (WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n)) ^ 2 := by rw [he]
    _ = e (WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n) ^ 2) := (map_pow e _ 2).symm
    _ = e (WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.ΨSq n))) := by
        rw [WeierstrassCurve.Affine.CoordinateRing.mk_ψ, WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]
    _ = (C (W.ΨSq n)).evalEval x y := he _
    _ = (W.ΨSq n).eval x := evalEval_C x y _

omit [DecidableEq F] in

theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

theorem smul_eq_zero_iff_evalEval_ψ {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 := by
  have key := zsmul_eq_smulEval (W := W) h n
  have hQns := (n • WeierstrassCurve.Jacobian.Point.fromAffine (WeierstrassCurve.Affine.Point.some x y h)).nonsingular
  rw [key] at hQns
  calc n • (WeierstrassCurve.Affine.Point.some x y h) = 0
      ↔ (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W).symm (n • WeierstrassCurve.Affine.Point.some x y h) =
        (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W).symm 0 := (AddEquiv.injective _).eq_iff.symm
    _ ↔ n • WeierstrassCurve.Jacobian.Point.fromAffine (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
        rw [map_zsmul, map_zero, WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_symm_apply]
    _ ↔ (⟦smulEval W x y n⟧ : WeierstrassCurve.Jacobian.PointClass F) = ⟦![1, 1, 0]⟧ := by
        rw [WeierstrassCurve.Jacobian.Point.ext_iff, key, WeierstrassCurve.Jacobian.Point.zero_point]
    _ ↔ (W.ψ n).evalEval x y = 0 := by
        constructor
        · intro heq
          have hz := (WeierstrassCurve.Jacobian.Z_eq_zero_of_equiv (Quotient.eq.mp heq)).mpr rfl
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz
        · intro hz
          refine Quotient.eq.mpr (WeierstrassCurve.Jacobian.equiv_zero_of_Z_eq_zero
            ((WeierstrassCurve.Jacobian.nonsingularLift_iff _).mp hQns) ?_)
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz


end
end Dubon2026.SourceEllipticPointFormula
