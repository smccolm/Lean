import Dubon2026.SourceEllipticGenericAddition

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction ->
reverse genus -> finite exceptional fibers -> actual elliptic torsion count
-> division-polynomial point multiplication. The actual universal point is
multiplied using the native elliptic-curve group law. The identities will
descend to the integral coordinate ring and specialize to every nonsingular
point. Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. -/
namespace Dubon2026.SourceEllipticUniversal.AffineFormula
open WeierstrassCurve Polynomial Dubon2026.SourceEllipticDivision
open WeierstrassCurve (ψ φ)
open Dubon2026.SourceEllipticSequence
open scoped Polynomial.Bivariate nonZeroDivisors
noncomputable section
variable {m n : ℤ}
open WeierstrassCurve.Affine.Point

theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : WeierstrassCurve.Affine.Nonsingular curveField (smulX n) (smulY n),
      n • affinePoint = .some (smulX n) (smulY n) h := by

  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _|_|_|n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨(pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        (by simpa only [pointedCurve, WeierstrassCurve.baseChange,
          map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
          using Δ_curve_ne_zero)).mp equation_point, rfl⟩
    all_goals obtain ⟨ns, eq⟩ := ih 1 (by omega) one_ne_zero
    · erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]
      exact ⟨WeierstrassCurve.Affine.nonsingular_add ns ns fun h ↦ smulY_one_ne_negY h.2,
        dif_neg fun h ↦ smulY_one_ne_negY h.2⟩
    set n2 := n + 1 + 1
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    simp_rw [show (n + 1 : ℕ) = n2 + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    let _U := pointedCurve.toAffine
    erw [eq2, eq, add_of_X_ne ne, WeierstrassCurve.Affine.Point.some.injEq] at eq1
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX (n2 + 1 : ℕ) = _U.addX (smulX n2) (smulX 1) L := by
      rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega),
        WeierstrassCurve.Affine.addX_eq_addX_negY_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]; rfl
    have Y_eq : smulY (n2 + 1 : ℕ) = _U.addY (smulX n2) (smulX 1) (smulY n2) L := by
      rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero functionField_two_ne_zero),
        ← add_right_cancel_iff (a := _U.a₁ * smulX (n2 + 1 : ℕ) + _U.a₃)]
      convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1
      · simp_rw [WeierstrassCurve.Affine.negY, Nat.cast_add]; simp only [_U]; ring_nf
      convert _U.addY_sub_negY_addY (smulY n2) (smulY 1) ne using 1
      · rw [WeierstrassCurve.Affine.negY, ← X_eq]; ring
      · rw [← X_eq]; rfl
    rw [X_eq, Y_eq, n2.cast_add, add_zsmul, eq, eq2]
    exact ⟨WeierstrassCurve.Affine.nonsingular_add ns2 ns fun h ↦ (ne h.1).elim, add_of_X_ne ne⟩
  | neg hn n =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := hn n h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]
    exact ⟨(WeierstrassCurve.Affine.nonsingular_neg ..).mpr ns, trivial⟩

theorem nonsingular_smulX_smulY (hn : n ≠ 0) : WeierstrassCurve.Affine.Nonsingular curveField (smulX n) (smulY n) := by
  exact (zsmul_point_eq_smulX_smulY hn).1

theorem zsmul_point_ne_zero (h0 : n ≠ 0) : n • affinePoint ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]; exact WeierstrassCurve.Affine.Point.some_ne_zero ns


end
end Dubon2026.SourceEllipticUniversal.AffineFormula
