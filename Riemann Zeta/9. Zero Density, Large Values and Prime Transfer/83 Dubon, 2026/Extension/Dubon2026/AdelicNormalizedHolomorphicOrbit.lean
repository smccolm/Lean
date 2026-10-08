import Dubon2026.RealAffineMultiplication
import Dubon2026.AdelicHolomorphicRaisingSpan

/-! # The genuine normalized affine Hilbert orbit and its exact holomorphic local formula -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The actual logarithmic affine parameter agrees with its original complex coordinate. -/
theorem realAffineHolomorphicParameter_log (x : ℝ) {y : ℝ} (hy : 0 < y) :
    realAffineHolomorphicParameter x (Real.log y) = (x : ℂ) + y * Complex.I - Complex.I := by
  simp only [realAffineHolomorphicParameter, Real.exp_log hy]

/-- Relative affine coordinates give exactly the normalized displacement from the original base point. -/
theorem realAffineHolomorphicParameter_relative {z z₀ : ℂ} (hz : 0 < z.im) (hz₀ : 0 < z₀.im) :
    realAffineHolomorphicParameter ((z.re - z₀.re) / z₀.im) (Real.log (z.im / z₀.im)) =
      (z - z₀) / (z₀.im : ℂ) := by
  rw [realAffineHolomorphicParameter_log _ (div_pos hz hz₀)]
  apply Complex.ext <;> simp
  field_simp

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

private theorem normalizedRepresentation_product {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (g h : G) (v w : V) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (he : ρ h v = b • w) : (a * b)⁻¹ • ρ (g * h) v = a⁻¹ • ρ g w := by
  rw [map_mul, Module.End.mul_apply, he, map_smul, smul_smul]
  congr 1
  field_simp

/-- The genuine original local holomorphic L2 curve retracted to its original Hilbert space. -/
def adelicHolomorphicHilbertCurve (z : ℂ) : AdelicCyclicHilbert f :=
  adelicCyclicHilbertL2Retraction f (adelicHolomorphicL2Curve N f z)

/-- The original affine Hilbert generator orbit with its precise real half-weight factor removed. -/
def adelicNormalizedAffineHilbertOrbit (z : ℂ) : AdelicCyclicHilbert f :=
  ((Real.exp (Real.log z.im * ((k : ℝ) / 2)) : ℂ))⁻¹ •
    adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realAffineMatrix z.re (Real.exp_pos (Real.log z.im))))
      (adelicCyclicHilbertGenerator f)

/-- On the original upper half-plane the normalized orbit uses exactly the original affine matrix. -/
theorem adelicNormalizedAffineHilbertOrbit_eq {z : ℂ} (hz : 0 < z.im) :
    adelicNormalizedAffineHilbertOrbit f z =
      ((Real.exp (Real.log z.im * ((k : ℝ) / 2)) : ℂ))⁻¹ •
        adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realAffineMatrix z.re hz))
          (adelicCyclicHilbertGenerator f) := by
  simp only [adelicNormalizedAffineHilbertOrbit, Real.exp_log hz]

/-- The genuine positive affine orbit retains the exact holomorphic slice and half-weight scalar. -/
theorem adelicCyclicHilbertGenerator_affine_positive_formula (x : ℝ) {y : ℝ} (hy : 0 < y)
    (hz : ‖(x : ℂ) + y * Complex.I - Complex.I‖ < (1 / 2 : ℝ)) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realAffineMatrix x hy))
      (adelicCyclicHilbertGenerator f) =
      (Real.exp (Real.log y * ((k : ℝ) / 2)) : ℂ) •
        adelicHolomorphicHilbertCurve f ((x : ℂ) + y * Complex.I - Complex.I) := by
  have h := adelicCyclicHilbertGenerator_affine_formula f x (Real.log y)
    (by simpa only [realAffineHolomorphicParameter_log x hy] using hz)
  simpa only [Real.exp_log hy, realAffineHolomorphicParameter_log x hy] using h

/-- Around every actual upper-half-plane point, the original normalized orbit is an original bounded translate of the genuine local holomorphic curve. -/
theorem adelicNormalizedAffineHilbertOrbit_local_formula {z z₀ : ℂ}
    (hz : 0 < z.im) (hz₀ : 0 < z₀.im) (hw : ‖(z - z₀) / (z₀.im : ℂ)‖ < (1 / 2 : ℝ)) :
    adelicNormalizedAffineHilbertOrbit f z =
      ((Real.exp (Real.log z₀.im * ((k : ℝ) / 2)) : ℂ))⁻¹ •
        adelicCyclicHilbertOperator f (adelicRealSL2Embedding (realAffineMatrix z₀.re hz₀))
          (adelicHolomorphicHilbertCurve f ((z - z₀) / (z₀.im : ℂ))) := by
  have hcoord : (((z.re - z₀.re) / z₀.im : ℝ) : ℂ) +
      ((z.im / z₀.im : ℝ) : ℂ) * Complex.I - Complex.I = (z - z₀) / (z₀.im : ℂ) :=
    (realAffineHolomorphicParameter_log _ (div_pos hz hz₀)).symm.trans
      (realAffineHolomorphicParameter_relative hz hz₀)
  have horbit := adelicCyclicHilbertGenerator_affine_positive_formula f
    ((z.re - z₀.re) / z₀.im) (div_pos hz hz₀) (hcoord ▸ hw)
  have hweight : (Real.exp (Real.log z.im * ((k : ℝ) / 2)) : ℂ) =
      (Real.exp (Real.log z₀.im * ((k : ℝ) / 2)) : ℂ) *
        (Real.exp (Real.log (z.im / z₀.im) * ((k : ℝ) / 2)) : ℂ) := by
    have hm : z₀.im * (z.im / z₀.im) = z.im := by field_simp
    exact_mod_cast (hm ▸ realAffineWeight_mul ((k : ℝ) / 2) hz₀ (div_pos hz hz₀))
  rw [hcoord] at horbit
  rw [adelicNormalizedAffineHilbertOrbit_eq f hz, hweight,
    realAffineMatrix_relative z.re z₀.re hz hz₀, map_mul]
  exact @normalizedRepresentation_product RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (adelicRealSL2Embedding (realAffineMatrix z₀.re hz₀))
    (adelicRealSL2Embedding (realAffineMatrix ((z.re - z₀.re) / z₀.im) (div_pos hz hz₀)))
    (adelicCyclicHilbertGenerator f) _ _ _
    (by exact_mod_cast (Real.exp_pos _).ne') (by exact_mod_cast (Real.exp_pos _).ne') horbit

end
end Dubon2026
