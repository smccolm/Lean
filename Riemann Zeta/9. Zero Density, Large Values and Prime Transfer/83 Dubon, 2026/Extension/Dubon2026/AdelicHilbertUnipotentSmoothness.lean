import Dubon2026.AdelicGeneratorUnipotentSmoothness
import Dubon2026.AdelicHilbertHolomorphicIdentity
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Smoothness of the actual original unipotent Hilbert orbit -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ContDiff

/-- The adjoint of the actual Hilbert-to-L2 isometry retracts the entire quotient L2 space onto the original completed space. -/
def adelicCyclicHilbertL2Retraction {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) →L[ℂ]
      AdelicCyclicHilbert f :=
  (@ContinuousLinearMap.adjoint ℂ (AdelicCyclicHilbert f)
    (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance)
    (adelicCyclicHilbertToL2 f)

/-- The actual adjoint retraction fixes every vector of the original completed space after realization. -/
theorem adelicCyclicHilbertL2Retraction_toL2 {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : AdelicCyclicHilbert f) :
    adelicCyclicHilbertL2Retraction f (adelicCyclicHilbertToL2 f v) = v := by
  have h := congrArg (fun T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f => T v)
    (@LinearIsometry.adjoint_comp_self ℂ inferInstance (AdelicCyclicHilbert f)
      (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (adelicCyclicHilbertL2Isometry f))
  exact h

/-- Every curve smooth in the actual quotient realization is smooth in its original completed adelic Hilbert space. -/
theorem adelicCyclicHilbert_contDiff_of_toL2 {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (C : ℝ → AdelicCyclicHilbert f)
    (h : ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertToL2 f (C t))) :
    ContDiff ℝ ∞ C := by
  have hr := @ContinuousLinearMap.contDiff ℝ
    (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance inferInstance ∞
    ((adelicCyclicHilbertL2Retraction f).restrictScalars ℝ)
  have ht := hr.comp h
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    adelicCyclicHilbertL2Retraction_toL2] using ht

/-- The original completed adelic generator is smooth to every order under the genuine unipotent one-parameter subgroup. -/
theorem adelicCyclicHilbertGenerator_unipotent_contDiff {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) := by
  apply adelicCyclicHilbert_contDiff_of_toL2 f
  simp only [adelicCyclicHilbertGenerator_orbit_toL2]
  exact adelicCyclicGenerator_unipotent_L2_contDiff N f

end
end Dubon2026
