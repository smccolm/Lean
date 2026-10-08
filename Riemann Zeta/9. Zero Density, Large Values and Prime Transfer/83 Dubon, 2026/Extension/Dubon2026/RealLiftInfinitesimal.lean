import Dubon2026.RealUnipotentCuspPeriod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Geometry.Manifold.Notation

/-! # The original holomorphic lift along genuine real unipotent and geodesic curves -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Manifold

/-- The actual determinant-one geodesic matrix with height exp(t). -/
def realGeodesicCurve (t : ℝ) : SL(2, ℝ) :=
  realAffineMatrix 0 (Real.exp_pos t)

/-- The original lift along the genuine right unipotent curve is its actual slashed holomorphic function. -/
theorem realWeightLift_right_unipotent_formula (k : ℤ) (f : ℍ → ℂ)
    (g : SL(2, ℝ)) (t : ℝ) :
    realWeightLift k f (g * realUpperUnipotent t) =
      ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex) ((t : ℂ) + Complex.I) := by
  rw [realWeightLift_mul, realWeightLift, ← realAffineMatrix_one_eq_upperUnipotent,
    realAffineMatrix_slash_apply]
  simp only [Real.one_rpow, Complex.ofReal_one, one_mul, Function.comp_apply]
  apply congrArg (f ∣[k] (mapGL ℝ g))
  apply UpperHalfPlane.ext
  rw [realAffineMatrix_smul, ofComplex_apply_of_im_pos (by simp)]
  simp [add_comm]

/-- The original lift along the genuine right geodesic curve has exactly the half-weight exponential factor. -/
theorem realWeightLift_right_geodesic_formula (k : ℤ) (f : ℍ → ℂ)
    (g : SL(2, ℝ)) (t : ℝ) :
    realWeightLift k f (g * realGeodesicCurve t) =
      (Real.exp (t * ((k : ℝ) / 2)) : ℂ) *
        ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex) ((Real.exp t : ℂ) * Complex.I) := by
  rw [realWeightLift_mul, realWeightLift, realGeodesicCurve,
    realAffineMatrix_slash_apply, ← Real.exp_mul]
  congr 1
  apply congrArg (f ∣[k] (mapGL ℝ g))
  apply UpperHalfPlane.ext
  rw [realAffineMatrix_smul, ofComplex_apply_of_im_pos (by simpa using Real.exp_pos t)]
  simp

/-- Holomorphy of the original function gives the actual unipotent derivative at every real-group point. -/
theorem realWeightLift_right_unipotent_hasDerivAt (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) :
    HasDerivAt (fun t : ℝ => realWeightLift k f (g * realUpperUnipotent t))
      (deriv (((f ∣[k] (mapGL ℝ g))) ∘ ofComplex) Complex.I) 0 := by
  have hd := (UpperHalfPlane.mdifferentiableAt_iff.mp ((hf.slash k (mapGL ℝ g)) I)).hasDerivAt
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ) + Complex.I) 1 0 := by
    simpa using Complex.ofRealCLM.hasDerivAt.add_const Complex.I
  have he := hd.comp_of_eq 0 ht (by simp)
  simpa only [Function.comp_def, mul_one, realWeightLift_right_unipotent_formula] using he

/-- Holomorphy gives the genuine geodesic derivative, retaining both its weight and complex derivative terms. -/
theorem realWeightLift_right_geodesic_hasDerivAt (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) :
    HasDerivAt (fun t : ℝ => realWeightLift k f (g * realGeodesicCurve t))
      ((k : ℂ) / 2 * realWeightLift k f g +
        Complex.I * deriv (((f ∣[k] (mapGL ℝ g))) ∘ ofComplex) Complex.I) 0 := by
  have hd := (UpperHalfPlane.mdifferentiableAt_iff.mp ((hf.slash k (mapGL ℝ g)) I)).hasDerivAt
  have ht : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (Real.hasDerivAt_exp 0).ofReal_comp.mul_const Complex.I
  have he := hd.comp_of_eq 0 ht (by simp)
  have hw : HasDerivAt (fun t : ℝ => (Real.exp (t * ((k : ℝ) / 2)) : ℂ))
      ((k : ℂ) / 2) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const ((k : ℝ) / 2)).exp).ofReal_comp
  have hp := hw.mul he
  simp_rw [realWeightLift_right_geodesic_formula]
  have hi : ofComplex Complex.I = I := ofComplex_apply I
  simpa [Function.comp_def, hi, realWeightLift, mul_comm] using hp

/-- The actual original lift satisfies the precise first-order holomorphic infinitesimal identity everywhere. -/
theorem realWeightLift_holomorphic_infinitesimal (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) :
    deriv (fun t : ℝ => realWeightLift k f (g * realGeodesicCurve t)) 0 -
      Complex.I * deriv (fun t : ℝ => realWeightLift k f (g * realUpperUnipotent t)) 0 =
        (k : ℂ) / 2 * realWeightLift k f g := by
  rw [(realWeightLift_right_geodesic_hasDerivAt k hf g).deriv,
    (realWeightLift_right_unipotent_hasDerivAt k hf g).deriv]
  ring

end
end Dubon2026
