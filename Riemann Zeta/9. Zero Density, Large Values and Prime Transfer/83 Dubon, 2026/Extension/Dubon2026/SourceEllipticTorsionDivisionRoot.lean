import Dubon2026.SourceEllipticDivisionZeros

/-! Exact all-order abscissa root criterion, reused in the separability
count for the finite Galois torsion field and DUB-17/18 inertia census. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticPointFormula
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)

theorem nsmul_eq_zero_iff_division_eval {x y : F}
    (h : E.toAffine.Nonsingular x y) (n : ℕ) :
    n • Point.some x y h = 0 ↔ (E.ΨSq n).eval x = 0 := by
  rw [← natCast_zsmul (Point.some x y h) n,
    smul_eq_zero_iff_evalEval_ψ E h, ← evalEval_ψ_sq E h.1]
  exact sq_eq_zero_iff.symm

theorem two_nsmul_eq_zero_iff_division_eval {x y : F}
    (h : E.toAffine.Nonsingular x y) :
    (2 : ℕ) • Point.some x y h = 0 ↔ E.Ψ₂Sq.eval x = 0 := by
  simpa only [Nat.cast_ofNat, ΨSq_two] using nsmul_eq_zero_iff_division_eval E h 2

theorem preDivision_eval_zero_of_torsion {x y : F}
    (h : E.toAffine.Nonsingular x y) {n : ℕ}
    (hn : n • Point.some x y h = 0)
    (h2 : Even n → (2 : ℕ) • Point.some x y h ≠ 0) :
    (E.preΨ n).eval x = 0 := by
  have hz := (nsmul_eq_zero_iff_division_eval E h n).mp hn
  rw [ΨSq, eval_mul, eval_pow] at hz
  by_cases he : Even n
  · rw [if_pos ((Int.even_coe_nat n).mpr he)] at hz
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_right
      (fun e => h2 he ((two_nsmul_eq_zero_iff_division_eval E h).mpr e)))
  · rw [if_neg (fun e => he ((Int.even_coe_nat n).mp e)), eval_one, mul_one] at hz
    exact sq_eq_zero_iff.mp hz

end
end Dubon2026.SourceEllipticDivisionField
