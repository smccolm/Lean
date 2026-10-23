import Dubon2026.SourceEllipticPointSpecialization

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
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem zsmul_eq_smulEval {x y : F} (h : WeierstrassCurve.Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (WeierstrassCurve.Affine.Point.some x y h)).point = ⟦smulEval W x y n⟧ := by

  have add_point_eq : ∀ (P Q : WeierstrassCurve.Jacobian.Point W) (P' Q' : Fin 3 → F),
      P.point = ⟦P'⟧ → Q.point = ⟦Q'⟧ → (P + Q).point = ⟦WeierstrassCurve.Jacobian.add W P' Q'⟧ := by
    intro P Q P' Q' hP hQ
    rw [Point.add_point, hP, hQ, addMap_eq]
  have two_zsmul_point : ∀ (P : WeierstrassCurve.Jacobian.Point W) (P' : Fin 3 → F), P.point = ⟦P'⟧ →
      (2 • P).point = ⟦dblXYZ W P'⟧ := by
    intro P P' hP
    rw [two_smul, add_point_eq P P P' P' hP hP, WeierstrassCurve.Jacobian.add_self]
  have add_point_of_ne : ∀ (P Q : WeierstrassCurve.Jacobian.Point W) (P' Q' : Fin 3 → F), P.point = ⟦P'⟧ →
      Q.point = ⟦Q'⟧ → P ≠ Q → (P + Q).point = ⟦addXYZ W P' Q'⟧ := by
    intro P Q P' Q' hP hQ ne
    rw [add_point_eq P Q P' Q' hP hQ, WeierstrassCurve.Jacobian.add_of_not_equiv fun h' ↦
      ne (Point.ext <| hP.trans <| (Quotient.sound h').trans hQ.symm)]
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _|_|n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl|rfl⟩ := n.even_or_odd'
    · rw [add_assoc, ← two_mul, ← left_distrib, Nat.cast_mul, mul_smul, natCast_zsmul,
        two_zsmul_point _ _ (ih _ <| by omega), dblXYZ_smulEval h.1]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul,
        add_point_of_ne _ _ _ _ (ih _ <| by omega) (ih _ <| by omega), Nat.cast_add (n + 1),
        Nat.cast_one, addXYZ_smulEval₁ h.1, ← add_assoc, two_mul]
      simp_rw [Nat.cast_add]
      rw [ne_comm, ← sub_ne_zero, ← sub_smul, add_sub_cancel_left, Nat.cast_one, one_smul]
      apply Point.fromAffine_some_ne_zero
  | neg hn n =>
    simp_rw [_root_.neg_smul, Point.neg_point, hn, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, WeierstrassCurve.Jacobian.comp_smul, ← WeierstrassCurve.Jacobian.map_neg,
      curveRing_map_ringEval, map_neg, map_one]
    rfl

end
end Dubon2026.SourceEllipticPointFormula
