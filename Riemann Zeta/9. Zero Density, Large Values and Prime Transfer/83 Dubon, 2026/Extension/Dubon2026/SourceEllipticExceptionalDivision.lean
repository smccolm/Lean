import Dubon2026.SourceEllipticExceptionalCoordinates
import Dubon2026.SourceEllipticTorsionDivisionRoot
import Dubon2026.SourceEllipticMultiplicationXFormula

/-! DUB-17/18 -> exceptional-fiber counts -> non-scalar prime-torsion
action. The existing multiplication formula and zero criterion give the
actual abscissa fraction, and native polynomial degrees bound its roots. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
noncomputable section
variable {L : Type*} [Field L]

theorem natDegree_Phi_add_X_mul_PsiSq_le (W : WeierstrassCurve L)
    (m : ℕ) (hm : 1 ≤ m) :
    (W.Φ (m : ℤ) + X * W.ΨSq (m : ℤ)).natDegree ≤ m ^ 2 := by
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · have hΦ := W.natDegree_Φ_le (m : ℤ)
    simpa only [Int.natAbs_natCast] using hΦ
  · refine (natDegree_mul_le).trans ?_
    have hΨ := W.natDegree_ΨSq_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΨ
    have hX : (X : L[X]).natDegree ≤ 1 := natDegree_X_le
    omega

theorem nsmul_xco_eq_div [DecidableEq L] (W : WeierstrassCurve L)
    (m : ℕ) {x y : L} (h : W.toAffine.Nonsingular x y)
    (hm : m • Point.some x y h ≠ 0) :
    (W.ΨSq (m : ℤ)).eval x ≠ 0 ∧
      xco ((m : ℤ) • Point.some x y h) =
        some ((W.Φ (m : ℤ)).eval x / (W.ΨSq (m : ℤ)).eval x) := by
  have hΨ : (W.ΨSq (m : ℤ)).eval x ≠ 0 := fun he =>
    hm ((SourceEllipticDivisionField.nsmul_eq_zero_iff_division_eval W h m).mpr he)
  have hself : W.baseChange L = W := by
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  have hform := SourceEllipticTorsion.smul_formula_or_zero
    (K := L) W (n := m) (x₀ := x) (y₀ := y)
  rw [hself] at hform
  obtain ⟨x', y', h', he, hx⟩ := (hform h).1 hΨ
  refine ⟨hΨ, ?_⟩
  rw [natCast_zsmul, he, xco_some]
  exact congrArg some ((eq_div_iff hΨ).mpr hx)

theorem prime_torsion_mul_coordinates [DecidableEq L]
    (W : WeierstrassCurve L) (m : ℕ) (hm : 1 ≤ m)
    (q : ℕ) (hq : q.Prime) (hmq : m < q)
    (x y : L) (h : W.toAffine.Nonsingular x y)
    (hkill : (q : ℤ) • Point.some x y h = 0) :
    (W.ΨSq (m : ℤ)).eval x ≠ 0 ∧
      xco ((m : ℤ) • Point.some x y h) =
        some ((W.Φ (m : ℤ)).eval x / (W.ΨSq (m : ℤ)).eval x) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hord : addOrderOf (Point.some x y h) = q :=
    addOrderOf_eq_prime_iff.mpr ⟨by rwa [← natCast_zsmul], Point.some_ne_zero h⟩
  apply nsmul_xco_eq_div W m h
  intro he
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero he
  rw [hord] at hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

end
end Dubon2026.SourceEllipticExceptional
