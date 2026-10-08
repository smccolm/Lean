import Dubon2026.RealCompactWeight
import Dubon2026.CuspFourierCoefficients

/-! # Actual real-group Fourier integrals and the original classical coefficients -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups CongruenceSubgroup

/-- The genuine frequency-n unipotent period of the original real-group lift. -/
def realWhittakerCoefficient {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, fourier (-n) (x : UnitAddCircle) *
    realWeightLift k f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ).toSL2R

/-- The actual unipotent integral equals the original cusp-circle Fourier coefficient with its exact weight. -/
theorem realWhittakerCoefficient_eq_fourierCoeff {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) (n : ℤ) :
    realWhittakerCoefficient f hy n = ((Real.sqrt y : ℝ) : ℂ) ^ k *
      fourierCoeff (cuspCircleFunction f (Real.exp (-2 * Real.pi * y))) n := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [div_one, one_smul, zero_add]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [realWeightLift_section, ← cuspCircleFunction_horizontal f x hy]
  simp only [smul_eq_mul]
  have hi : (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ).im = y := by simp
  rw [hi]
  ring

/-- Each nonnegative actual unipotent Fourier integral contains exactly the original coefficient. -/
theorem realWhittakerCoefficient_nat {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    realWhittakerCoefficient f hy (n : ℤ) = cuspCoefficients f n *
      ((Real.sqrt y : ℝ) : ℂ) ^ k * (Real.exp (-2 * Real.pi * n * y) : ℂ) := by
  have hr1 : Real.exp (-2 * Real.pi * y) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  rw [realWhittakerCoefficient_eq_fourierCoeff,
    cuspCircleFunction_fourierCoeff_nat f (Real.exp_pos _).le hr1]
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
  have he : (n : ℝ) * (-2 * Real.pi * y) = -2 * Real.pi * n * y := by ring
  rw [he]
  ring

/-- The actual real-group lift has no negative unipotent frequencies. -/
theorem realWhittakerCoefficient_neg {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) {n : ℤ} (hn : n < 0) :
    realWhittakerCoefficient f hy n = 0 := by
  have hr1 : Real.exp (-2 * Real.pi * y) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  rw [realWhittakerCoefficient_eq_fourierCoeff,
    cuspCircleFunction_fourierCoeff_neg f (Real.exp_pos _).le hr1 hn, mul_zero]

/-- Cuspidality of the original function is exactly vanishing of the constant real-group unipotent integral. -/
theorem realWhittakerCoefficient_zero {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) : realWhittakerCoefficient f hy 0 = 0 := by
  simpa [cuspCoefficients_zero] using realWhittakerCoefficient_nat f hy 0

end
end Dubon2026
