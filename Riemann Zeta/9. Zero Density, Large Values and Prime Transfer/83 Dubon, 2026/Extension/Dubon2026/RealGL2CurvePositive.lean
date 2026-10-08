import Dubon2026.RealGL2Sign
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Every actual identity-based general-linear curve lies in the positive component locally -/

namespace Dubon2026

noncomputable section
open Matrix Filter
open scoped Topology MatrixGroups

/-- An actual real general-linear curve with differentiable original entries has positive determinant near its identity value. -/
theorem realGL2Curve_eventually_positive (c : ℝ → GeneralLinearGroup (Fin 2) ℝ) (hc : c 0 = 1)
    (a : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => (c t).val i j) (a i j) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (c t).val.det := by
  have hD : HasDerivAt (fun t => (c t).val.det) (Matrix.trace a) 0 := by
    simpa [Matrix.det_fin_two, hc, Matrix.trace, Fin.sum_univ_two, add_comm] using
      ((hd 0 0).mul (hd 1 1)).sub ((hd 0 1).mul (hd 1 0))
  exact hD.continuousAt.eventually (lt_mem_nhds (by simp [hc]))

/-- The actual positive part is literally the original general-linear curve in a neighborhood of its identity value. -/
theorem realGL2Curve_positivePart_eventually (c : ℝ → GeneralLinearGroup (Fin 2) ℝ) (hc : c 0 = 1)
    (a : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => (c t).val i j) (a i j) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (realGL2PositivePart (c t)).val = c t := by
  filter_upwards [realGL2Curve_eventually_positive c hc a hd] with t ht
  exact congrArg Subtype.val (realGL2PositivePart_of_positive ⟨c t, ht⟩)

end
end Dubon2026
