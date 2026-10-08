import Dubon2026.AdelicHilbertInfinitesimal

/-! # The genuine completed infinitesimal second-order eigenvalue of the original generator -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The displayed normalized operator made from actual successive Hilbert infinitesimal actions. -/
def adelicHilbertCasimirOperator {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : AdelicCyclicHilbert f) :
    AdelicCyclicHilbert f :=
  -adelicHilbertInfinitesimal f realGeodesicCurve (adelicHilbertInfinitesimal f realGeodesicCurve v) +
    adelicHilbertInfinitesimal f realGeodesicCurve v -
    adelicHilbertInfinitesimal f realUpperUnipotent (adelicHilbertInfinitesimal f realUpperUnipotent v) +
    adelicHilbertInfinitesimal f realUpperUnipotent (adelicHilbertInfinitesimal f realRotationCurve v)

/-- The actual completed compact infinitesimal action has precisely the original integral weight. -/
theorem adelicCyclicHilbertGenerator_compact_infinitesimal {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    adelicHilbertInfinitesimal f realRotationCurve (adelicCyclicHilbertGenerator f) =
      ((k : ℂ) * Complex.I) • adelicCyclicHilbertGenerator f := by
  exact @HasDerivAt.deriv ℝ inferInstance (AdelicCyclicHilbert f) inferInstance inferInstance
    _ _ _ (adelicCyclicHilbertGenerator_rotation_hasDerivAt f)

/-- The genuine successive Hilbert infinitesimal operator has the exact original k/2(1-k/2) eigenvalue on the actual completed generator. -/
theorem adelicCyclicHilbertGenerator_casimir {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    adelicHilbertCasimirOperator f (adelicCyclicHilbertGenerator f) =
      (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • adelicCyclicHilbertGenerator f := by
  rw [adelicHilbertCasimirOperator,
    adelicHilbertInfinitesimal_twice f realGeodesicCurve realGeodesicCurve_add
      (adelicCyclicHilbertGenerator f) (adelicCyclicHilbertGenerator_geodesic_differentiableAt f),
    adelicHilbertInfinitesimal_twice f realUpperUnipotent realUpperUnipotent_add
      (adelicCyclicHilbertGenerator f) (adelicCyclicHilbertGenerator_unipotent_differentiableAt f),
    adelicCyclicHilbertGenerator_compact_infinitesimal,
    adelicHilbertInfinitesimal_smul f realUpperUnipotent (adelicCyclicHilbertGenerator f)
      (adelicCyclicHilbertGenerator_unipotent_differentiableAt f)]
  have h := adelicCyclicHilbertGenerator_second_order_identity f
  simp only [iteratedDeriv_one] at h
  unfold adelicHilbertInfinitesimal
  calc
    _ = -(iteratedDeriv 2 (fun t : ℝ => adelicCyclicHilbertRepresentation f
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0 -
      deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0 +
      iteratedDeriv 2 (fun t : ℝ => adelicCyclicHilbertRepresentation f
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0 -
      ((k : ℂ) * Complex.I) • deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0) := by abel
    _ = -((((k : ℂ) / 2) * ((k : ℂ) / 2 - 1)) • adelicCyclicHilbertGenerator f) := congrArg Neg.neg h
    _ = _ := by
      rw [← neg_smul (((k : ℂ) / 2) * ((k : ℂ) / 2 - 1)) (adelicCyclicHilbertGenerator f)]
      congr 1
      ring

end
end Dubon2026
