import Dubon2026.AdelicHilbertGeneratorDerivatives
import Dubon2026.AdelicHilbertCompactWeight
import Dubon2026.RealCompactInfinitesimal

/-! # The actual compact Hilbert derivative of the original adelic generator -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The original completed compact orbit is the literal rotation weight times the original completed generator. -/
theorem adelicCyclicHilbertGenerator_rotation_formula {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (t : ℝ) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t))
      (adelicCyclicHilbertGenerator f) =
      ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) ^ (-k) •
        adelicCyclicHilbertGenerator f := by
  let a : realCompactSubgroup := ⟨realRotationCurve t, realRotationCurve_smul_I t⟩
  have h := adelicCyclicHilbertGenerator_compact_weight f a
  change adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t))
    (adelicCyclicHilbertGenerator f) =
    denom (mapGL ℝ (realRotationCurve t)) I ^ (-k) • adelicCyclicHilbertGenerator f at h
  simpa only [realRotationCurve_denom] using h

/-- The compact rotation weight has its genuine scalar derivative i times the original integral weight. -/
theorem realRotationWeight_hasDerivAt (k : ℤ) :
    HasDerivAt (fun t : ℝ =>
      ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) ^ (-k)) ((k : ℂ) * Complex.I) 0 := by
  have hd : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I)
      (-Complex.I) 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp.sub
      ((Real.hasDerivAt_sin 0).ofReal_comp.mul_const Complex.I)
  have hp := (hasDerivAt_zpow (-k) (1 : ℂ) (Or.inl one_ne_zero)).comp_of_eq 0 hd (by simp)
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hp

/-- The actual completed generator's compact rotation derivative equals i times its original weight in the genuine Hilbert norm. -/
theorem adelicCyclicHilbertGenerator_rotation_hasDerivAt {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    HasDerivAt (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve t)) (adelicCyclicHilbertGenerator f))
      (((k : ℂ) * Complex.I) • adelicCyclicHilbertGenerator f) 0 := by
  letI := NormedSpace.restrictScalars ℝ ℂ (AdelicCyclicHilbert f)
  simpa only [adelicCyclicHilbertGenerator_rotation_formula] using
    (realRotationWeight_hasDerivAt k).smul_const (adelicCyclicHilbertGenerator f)

end
end Dubon2026
