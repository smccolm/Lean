import Dubon2026.AdelicHilbertAffineSmoothness

/-! # Joint smoothness in the original three real Iwasawa parameters -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

/-- The original completed Iwasawa orbit has exactly its original compact character and affine orbit. -/
theorem adelicCyclicHilbertGenerator_iwasawa_formula {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (x y t : ℝ) :
    adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realAffineMatrix x (Real.exp_pos y) * realRotationCurve t))
      (adelicCyclicHilbertGenerator f) =
      ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) ^ (-k) •
        adelicCyclicHilbertRepresentation f
          (adelicRealSL2Embedding (realAffineMatrix x (Real.exp_pos y)))
          (adelicCyclicHilbertGenerator f) := by
  rw [map_mul, map_mul, Module.End.mul_apply, adelicCyclicHilbertGenerator_rotation_formula]
  exact (adelicCyclicHilbertRepresentation f _).map_smul _ _

/-- The genuine original Hilbert orbit is jointly smooth in all three Iwasawa parameters throughout the proved affine neighborhood. -/
theorem adelicCyclicHilbertGenerator_iwasawa_contDiffAt {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {v : (ℝ × ℝ) × ℝ}
    (hv : ‖realAffineHolomorphicParameter v.1.1 v.1.2‖ < (1 / 2 : ℝ)) :
    ContDiffAt ℝ ∞ (fun w : (ℝ × ℝ) × ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding
        (realAffineMatrix w.1.1 (Real.exp_pos w.1.2) * realRotationCurve w.2))
      (adelicCyclicHilbertGenerator f)) v := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  have ha := (adelicCyclicHilbertGenerator_affine_contDiffAt f hv).comp v contDiffAt_fst
  have hk := (realRotationWeight_contDiff k).contDiffAt.comp v contDiffAt_snd
  simpa only [Function.comp_def, Pi.smul_apply, adelicCyclicHilbertGenerator_iwasawa_formula]
    using hk.smul ha

/-- At the actual identity coordinate, joint smoothness of the original three-parameter orbit needs no analytic premise. -/
theorem adelicCyclicHilbertGenerator_iwasawa_contDiffAt_zero {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ContDiffAt ℝ ∞ (fun w : (ℝ × ℝ) × ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding
        (realAffineMatrix w.1.1 (Real.exp_pos w.1.2) * realRotationCurve w.2))
      (adelicCyclicHilbertGenerator f)) 0 := by
  apply adelicCyclicHilbertGenerator_iwasawa_contDiffAt f
  norm_num [realAffineHolomorphicParameter]

end
end Dubon2026
