import Dubon2026.BoundedL2JetIdentification
import Dubon2026.AdelicProjectiveRepresentative
import Dubon2026.AdelicGeneratorGeodesicSmoothness

/-! # Exact original representatives of every genuine real L2 orbit jet -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- Actual full adelic pointwise derivatives and uniform bounds identify every original quotient L2 jet. -/
theorem adelicCyclicGenerator_L2_jets_ae_of_bounds (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (hd : ∀ (g : RationalAdelicGL2) (n : ℕ) (t : ℝ),
      HasDerivAt (iteratedDeriv n (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (c u))))
        (iteratedDeriv (n + 1) (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
          (g * adelicRealSL2Embedding (c u))) t) t)
    (hB : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : RationalAdelicGL2, ∀ t : ℝ,
      ‖iteratedDeriv n (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (c u))) t‖ ≤ C) (n : ℕ) (t : ℝ) :
    ⇑(iteratedDeriv n (fun u : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (c u)) (adelicCyclicGenerator N f))) t) =ᵐ[
          adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
      fun p => iteratedDeriv n (fun u : ℝ => adelicProjectiveRealOrbit N f c u p) t := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  let J : ℕ → ℝ → AdelicProjectiveGroup → ℂ := fun m u p =>
    iteratedDeriv m (fun s : ℝ => adelicProjectiveRealOrbit N f c s p) u
  have hD (m : ℕ) (u : ℝ) (p : AdelicProjectiveGroup) :
      HasDerivAt (fun s : ℝ => J m s p) (J (m + 1) u p) u := by
    unfold J
    simp_rw [adelicProjectiveRealOrbit_representative_eq]
    exact hd (adelicProjectiveRepresentative p) m u
  have hb (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u p, ‖J m u p‖ ≤ C := by
    obtain ⟨C, hC0, hC⟩ := hB m
    refine ⟨C, hC0, fun u p => ?_⟩
    unfold J
    simp_rw [adelicProjectiveRealOrbit_representative_eq]
    exact hC (adelicProjectiveRepresentative p) u
  have hmem : ∀ m u, MemLp (J m u) 2 μ := memLp_bounded_jet_family J
    (fun u => by
      simpa only [J, iteratedDeriv_zero] using
        (adelicProjectiveRealOrbit_memLp N f c u).aestronglyMeasurable)
    hD (fun m => let ⟨C, _, hC⟩ := hb m; ⟨C, hC⟩)
  have he := iteratedDeriv_toLp_ae_of_bounded_jet_family J hmem hD hb n t
  simpa only [J, iteratedDeriv_zero] using he

/-- Every actual unipotent quotient L2 derivative has precisely its original pointwise jet as representative. -/
theorem adelicCyclicGenerator_unipotent_L2_jets_ae (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (t : ℝ) :
    ⇑(iteratedDeriv n (fun u : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent u)) (adelicCyclicGenerator N f))) t) =ᵐ[
          adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
      fun p => iteratedDeriv n (fun u : ℝ => adelicProjectiveRealOrbit N f realUpperUnipotent u p) t := by
  apply adelicCyclicGenerator_L2_jets_ae_of_bounds N f realUpperUnipotent
    (canonicalAdelicGL2CuspLift_unipotent_jet_hasDerivAt N f)
  intro m
  obtain ⟨C, hC0, hC⟩ := canonicalAdelicGL2CuspLift_unipotent_jets_bounded N f
  exact ⟨(m.factorial : ℝ) * C / (1 / 2 : ℝ) ^ m, by positivity, hC m⟩

/-- Every actual geodesic quotient L2 derivative has precisely its original pointwise jet as representative. -/
theorem adelicCyclicGenerator_geodesic_L2_jets_ae (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (t : ℝ) :
    ⇑(iteratedDeriv n (fun u : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve u)) (adelicCyclicGenerator N f))) t) =ᵐ[
          adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
      fun p => iteratedDeriv n (fun u : ℝ => adelicProjectiveRealOrbit N f realGeodesicCurve u p) t := by
  apply adelicCyclicGenerator_L2_jets_ae_of_bounds N f realGeodesicCurve
    (canonicalAdelicGL2CuspLift_geodesic_jet_hasDerivAt N f)
  intro m
  obtain ⟨B, hB0, hB⟩ := canonicalAdelicGL2CuspLift_geodesic_jets_bounded N f
  exact ⟨B m, hB0 m, fun g u => hB m g u⟩

end
end Dubon2026
