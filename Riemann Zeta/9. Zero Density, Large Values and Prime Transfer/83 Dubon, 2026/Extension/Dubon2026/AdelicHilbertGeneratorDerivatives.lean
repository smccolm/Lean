import Dubon2026.AdelicGeneratorL2Derivatives
import Dubon2026.AdelicCyclicHilbertGenerator
import Dubon2026.ClosedIsometryDerivative

/-! # Genuine Hilbert norm derivatives of the original adelic generator -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The original completed generator orbit realizes exactly the original quotient L2 orbit. -/
theorem adelicCyclicHilbertGenerator_orbit_toL2 {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2) :
    adelicCyclicHilbertToL2 f
      (adelicCyclicHilbertRepresentation f a (adelicCyclicHilbertGenerator f)) =
      adelicProjectiveCyclicToL2 N f
        ((adelicLiftCyclicRepresentation N k f).toRepresentation a (adelicCyclicGenerator N f)) := by
  rw [adelicCyclicHilbertGenerator, adelicCyclicHilbertEmbedding_intertwines,
    adelicCyclicHilbertToL2_embedding]

/-- The original completed adelic cusp generator has a genuine Hilbert norm derivative under the actual unipotent one-parameter subgroup. -/
theorem adelicCyclicHilbertGenerator_unipotent_differentiableAt {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0 := by
  letI := NormedSpace.restrictScalars ℝ ℂ (AdelicCyclicHilbert f)
  let e : AdelicCyclicHilbert f →ₗᵢ[ℝ] _ :=
    { (adelicCyclicHilbertToL2 f).restrictScalars ℝ with
      norm_map' := adelicCyclicHilbertToL2_norm f }
  apply differentiableAt_of_linearIsometry_comp e
  change DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertToL2 f
    (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realUpperUnipotent t))
      (adelicCyclicHilbertGenerator f))) 0
  simp only [adelicCyclicHilbertGenerator_orbit_toL2]
  exact adelicCyclicGenerator_unipotent_L2_differentiableAt N f

/-- The original completed adelic cusp generator has a genuine Hilbert norm derivative under the actual geodesic one-parameter subgroup. -/
theorem adelicCyclicHilbertGenerator_geodesic_differentiableAt {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0 := by
  letI := NormedSpace.restrictScalars ℝ ℂ (AdelicCyclicHilbert f)
  let e : AdelicCyclicHilbert f →ₗᵢ[ℝ] _ :=
    { (adelicCyclicHilbertToL2 f).restrictScalars ℝ with
      norm_map' := adelicCyclicHilbertToL2_norm f }
  apply differentiableAt_of_linearIsometry_comp e
  change DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertToL2 f
    (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realGeodesicCurve t))
      (adelicCyclicHilbertGenerator f))) 0
  simp only [adelicCyclicHilbertGenerator_orbit_toL2]
  exact adelicCyclicGenerator_geodesic_L2_differentiableAt N f

end
end Dubon2026
