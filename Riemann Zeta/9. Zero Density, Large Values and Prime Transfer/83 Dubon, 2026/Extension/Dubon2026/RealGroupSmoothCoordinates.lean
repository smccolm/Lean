import Dubon2026.AdelicRealHolomorphicFormula
import Dubon2026.AdelicHilbertAffineSmoothness

/-! # Genuine smooth real matrix families and their original upper-half-plane coordinates -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual automorphy denominator is smooth along every smooth family of original real matrix entries. -/
theorem realGroupDenom_contDiffAt (h : E → SL(2, ℝ)) {x : E}
    (hh : ∀ i j : Fin 2, ContDiffAt ℝ ∞ (fun w => h w i j) x) :
    ContDiffAt ℝ ∞ (fun w => denom (mapGL ℝ (h w)) I) x := by
  change ContDiffAt ℝ ∞ (fun w => (h w 1 0 : ℂ) * Complex.I + (h w 1 1 : ℂ)) x
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp x (hh 1 0)).mul contDiffAt_const).add
    (Complex.ofRealCLM.contDiff.contDiffAt.comp x (hh 1 1))

/-- The exact integral-weight factor is smooth along every original smooth real matrix family. -/
theorem realGroupWeight_contDiffAt (k : ℤ) (h : E → SL(2, ℝ)) {x : E}
    (hh : ∀ i j : Fin 2, ContDiffAt ℝ ∞ (fun w => h w i j) x) :
    ContDiffAt ℝ ∞ (fun w => denom (mapGL ℝ (h w)) I ^ (-k)) x := by
  have hd := realGroupDenom_contDiffAt h hh
  cases he : -k with
  | ofNat n => simpa only [he, zpow_natCast] using hd.pow n
  | negSucc n =>
    simpa only [he, zpow_negSucc] using
      (hd.pow (n + 1)).inv (pow_ne_zero _ (denom_ne_zero (mapGL ℝ (h x)) I))

/-- The original Möbius coordinate is smooth along every smooth family of actual real matrix entries. -/
theorem realGroupHolomorphicParameter_contDiffAt (h : E → SL(2, ℝ)) {x : E}
    (hh : ∀ i j : Fin 2, ContDiffAt ℝ ∞ (fun w => h w i j) x) :
    ContDiffAt ℝ ∞ (fun w => realGroupHolomorphicParameter (h w)) x := by
  have hn : ContDiffAt ℝ ∞ (fun w => (h w 0 0 : ℂ) * Complex.I + (h w 0 1 : ℂ)) x :=
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp x (hh 0 0)).mul contDiffAt_const).add
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x (hh 0 1))
  have ht := (hn.mul ((realGroupDenom_contDiffAt h hh).inv (denom_ne_zero (mapGL ℝ (h x)) I))).sub
    (contDiffAt_const (c := Complex.I))
  simpa only [realGroupHolomorphicParameter, coe_specialLinearGroup_apply,
    Algebra.algebraMap_self_apply, coe_I, div_eq_mul_inv] using ht

/-- Multiplication by a fixed original real matrix preserves smoothness of each genuine matrix entry. -/
theorem realSL2_left_mul_entries_contDiffAt (g : SL(2, ℝ)) (h : E → SL(2, ℝ)) {x : E}
    (hh : ∀ i j : Fin 2, ContDiffAt ℝ ∞ (fun w => h w i j) x) (i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun w => (g * h w) i j) x := by
  change ContDiffAt ℝ ∞ (fun w => ∑ l : Fin 2, g i l * h w l j) x
  exact ContDiffAt.sum (fun l _ => contDiffAt_const.mul (hh l j))

end
end Dubon2026
