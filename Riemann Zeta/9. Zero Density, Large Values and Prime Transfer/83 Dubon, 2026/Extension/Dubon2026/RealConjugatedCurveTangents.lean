import Dubon2026.RealInfinitesimalEntryTangents

/-! # Exact smoothness and entry tangents of genuinely conjugated real curves -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

/-- Conjugation of the actual real curve by an actual fixed matrix. -/
def realConjugatedCurve (g : SL(2, ℝ)) (c : ℝ → SL(2, ℝ)) (t : ℝ) : SL(2, ℝ) :=
  g * c t * g⁻¹

/-- Fixed actual conjugation preserves smoothness of all original matrix entries. -/
theorem realConjugatedCurve_entries_contDiff (g : SL(2, ℝ)) (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun t => realConjugatedCurve g c t i j) := by
  apply realSL2_right_mul_entries_contDiff g⁻¹ (fun t => g * c t)
  intro i j
  change ContDiff ℝ ∞ (fun t => ∑ l : Fin 2, g i l * c t l j)
  exact ContDiff.sum (fun l _ => contDiff_const.mul (hc l j))

/-- Conjugating an original curve through the identity still passes through that identity. -/
theorem realConjugatedCurve_zero (g : SL(2, ℝ)) (c : ℝ → SL(2, ℝ)) (hc : c 0 = 1) :
    realConjugatedCurve g c 0 = 1 := by simp [realConjugatedCurve, hc]

/-- The exact matrix tangent of the original conjugated curve is the conjugate of its original tangent. -/
theorem realConjugatedCurve_entry_hasDerivAt (g : SL(2, ℝ)) (c : ℝ → SL(2, ℝ))
    (m : Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ∀ i j : Fin 2, HasDerivAt (fun t => c t i j) (m i j) 0) (i j : Fin 2) :
    HasDerivAt (fun t => realConjugatedCurve g c t i j)
      (((g : Matrix (Fin 2) (Fin 2) ℝ) * m * (g⁻¹ : SL(2, ℝ))) i j) 0 := by
  change HasDerivAt (fun t => ∑ l : Fin 2, (∑ q : Fin 2, g i q * c t q l) * g⁻¹ l j)
    (∑ l : Fin 2, (∑ q : Fin 2, g i q * m q l) * g⁻¹ l j) 0
  exact HasDerivAt.fun_sum (fun l _ =>
    (HasDerivAt.fun_sum (fun q _ => (hc q l).const_mul (g i q))).mul_const (g⁻¹ l j))

/-- Actual conjugation preserves the exact exponential semidirect subgroup relation. -/
theorem realConjugatedCurve_semidirect (g : SL(2, ℝ)) (a b : ℝ → SL(2, ℝ)) (r : ℝ)
    (hab : ∀ s t, a s * b t = b (Real.exp (r * s) * t) * a s) (s t : ℝ) :
    realConjugatedCurve g a s * realConjugatedCurve g b t =
      realConjugatedCurve g b (Real.exp (r * s) * t) * realConjugatedCurve g a s := by
  simpa only [realConjugatedCurve, mul_assoc, inv_mul_cancel_left] using
    congrArg (fun h => g * h * g⁻¹) (hab s t)

/-- The original geodesic conjugated by U(1) has the precise diagonal-minus-upper tangent. -/
theorem realUpperConjugatedGeodesic_entry_hasDerivAt (i j : Fin 2) :
    HasDerivAt (fun t => realConjugatedCurve (realUpperUnipotent 1) realGeodesicCurve t i j)
      (!![(1 / 2 : ℝ), -1; 0, -(1 / 2)] i j) 0 := by
  have he := realConjugatedCurve_entry_hasDerivAt (realUpperUnipotent 1) realGeodesicCurve
    !![(1 / 2 : ℝ), 0; 0, -(1 / 2)] realGeodesicCurve_entry_hasDerivAt i j
  fin_cases i <;> fin_cases j <;>
    convert he using 1 <;> norm_num [realUpperUnipotent, coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The original lower curve conjugated by U(1) has the precise lower-plus-diagonal-minus-upper tangent. -/
theorem realUpperConjugatedLower_entry_hasDerivAt (i j : Fin 2) :
    HasDerivAt (fun t => realConjugatedCurve (realUpperUnipotent 1) realLowerUnipotent t i j)
      (!![(1 : ℝ), -1; 1, -1] i j) 0 := by
  have he := realConjugatedCurve_entry_hasDerivAt (realUpperUnipotent 1) realLowerUnipotent
    !![(0 : ℝ), 0; 1, 0] realLowerUnipotent_entry_hasDerivAt i j
  fin_cases i <;> fin_cases j <;>
    simpa [realUpperUnipotent, coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two] using he

end
end Dubon2026
