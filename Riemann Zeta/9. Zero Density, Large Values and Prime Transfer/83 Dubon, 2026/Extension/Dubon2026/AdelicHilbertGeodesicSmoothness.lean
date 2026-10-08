import Dubon2026.AdelicGeneratorGeodesicSmoothness
import Dubon2026.AdelicHilbertUnipotentSmoothness
import Dubon2026.AdelicHilbertCompactDerivative

/-! # Smooth original geodesic and compact generator orbits in the genuine Hilbert space -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

/-- The actual original completed generator is smooth to every order along the genuine geodesic subgroup. -/
theorem adelicCyclicHilbertGenerator_geodesic_contDiff {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) := by
  apply adelicCyclicHilbert_contDiff_of_toL2 f
  simp only [adelicCyclicHilbertGenerator_orbit_toL2]
  exact adelicCyclicGenerator_geodesic_L2_contDiff N f

/-- The actual original rotation character is smooth for every integral weight. -/
theorem realRotationWeight_contDiff (k : ℤ) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) ^ (-k)) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp Real.contDiff_cos).sub
      ((Complex.ofRealCLM.contDiff.comp Real.contDiff_sin).mul contDiff_const)
  have hn (t : ℝ) : (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I ≠ 0 := by
    rw [← realRotationCurve_denom]
    exact denom_ne_zero _ _
  cases he : -k with
  | ofNat n => simpa only [he, zpow_natCast] using hs.pow n
  | negSucc n =>
    simpa only [he, zpow_negSucc] using (hs.pow (n + 1)).inv (fun t => pow_ne_zero _ (hn t))

/-- The actual original completed generator is smooth to every order under compact rotation, with its precise original weight. -/
theorem adelicCyclicHilbertGenerator_rotation_contDiff {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve t)) (adelicCyclicHilbertGenerator f)) := by
  let L : ℂ →L[ℂ] AdelicCyclicHilbert f :=
    ContinuousLinearMap.toSpanSingleton ℂ (adelicCyclicHilbertGenerator f)
  have hL := @ContinuousLinearMap.contDiff ℝ ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance ∞ (L.restrictScalars ℝ)
  have ht := hL.comp (realRotationWeight_contDiff k)
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', L,
    ContinuousLinearMap.toSpanSingleton_apply, adelicCyclicHilbertGenerator_rotation_formula] using ht

end
end Dubon2026
