import Dubon2026.CuspFourierEnergy

/-! # Extracting the original cusp coefficients from their actual horizontal Fourier integrals -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups CongruenceSubgroup

/-- Actual integration extracts each mode of a norm-summable one-sided Fourier expansion. -/
theorem fourierCoeff_of_hasSum_nat {c : ℕ → ℂ} {g : UnitAddCircle → ℂ}
    (hc : Summable (fun n => ‖c n‖))
    (hg : ∀ z, HasSum (fun n => c n * fourier (n : ℤ) z) (g z)) (m : ℤ) :
    fourierCoeff g m = ∑' n : ℕ, if (n : ℤ) = m then c n else 0 := by
  let F : ℕ → UnitAddCircle → ℂ := fun n z =>
    fourier (-m) z * (c n * fourier (n : ℤ) z)
  have hn (n : ℕ) (z : UnitAddCircle) : ‖F n z‖ = ‖c n‖ := by
    simp [F, fourier_apply]
  have hi (n : ℕ) : Integrable (F n) AddCircle.haarAddCircle :=
    (by dsimp [F]; fun_prop : Continuous (F n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hni : Summable (fun n => ∫ z : UnitAddCircle, ‖F n z‖ ∂AddCircle.haarAddCircle) := by
    simp_rw [hn]
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hc
  have hs (z : UnitAddCircle) : HasSum (fun n => F n z) (fourier (-m) z * g z) :=
    (hg z).mul_left _
  have he (n : ℕ) : (∫ z : UnitAddCircle, F n z ∂AddCircle.haarAddCircle) =
      if (n : ℤ) = m then c n else 0 := by
    have hf (z : UnitAddCircle) : F n z = c n * fourier ((n : ℤ) - m) z := by
      simp only [F, sub_eq_add_neg, fourier_add]
      ring
    simp_rw [hf]
    rw [integral_const_mul, integral_circle_fourier]
    split_ifs with hh <;> simp_all [sub_eq_zero]
  have hh := hasSum_integral_of_summable_integral_norm hi hni
  simp_rw [he, (hs _).tsum_eq] at hh
  exact hh.tsum_eq.symm

/-- The positive modes of the original cusp function are its original q-expansion coefficients. -/
theorem cuspCircleFunction_fourierCoeff_nat {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    fourierCoeff (cuspCircleFunction f r) (n : ℤ) = cuspCoefficients f n * (r : ℂ) ^ n := by
  rw [fourierCoeff_of_hasSum_nat (summable_norm_cuspCircleCoefficients f hr hr1)
    (hasSum_cuspCircleFunction f hr hr1)]
  simp

/-- Every negative mode of the actual holomorphic cusp function vanishes. -/
theorem cuspCircleFunction_fourierCoeff_neg {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {m : ℤ} (hm : m < 0) :
    fourierCoeff (cuspCircleFunction f r) m = 0 := by
  rw [fourierCoeff_of_hasSum_nat (summable_norm_cuspCircleCoefficients f hr hr1)
    (hasSum_cuspCircleFunction f hr hr1)]
  have hne (n : ℕ) : (n : ℤ) ≠ m := by omega
  simp [hne]

end
end Dubon2026
