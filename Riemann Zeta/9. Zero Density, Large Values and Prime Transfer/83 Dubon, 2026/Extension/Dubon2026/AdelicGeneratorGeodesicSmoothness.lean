import Dubon2026.AdelicGeodesicJetBounds
import Dubon2026.BoundedL2Smoothness
import Dubon2026.AdelicProjectiveRealDerivative

/-! # Smoothness of the actual original geodesic quotient L2 orbit -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ContDiff

/-- The original adelic cusp generator's actual geodesic orbit is smooth to every order in the genuine arithmetic quotient L2 norm. -/
theorem adelicCyclicGenerator_geodesic_L2_contDiff (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ContDiff ℝ ∞ (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))) := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  let F := adelicProjectiveRealOrbit N f realGeodesicCurve
  let J : ℕ → ℝ → AdelicProjectiveGroup → ℂ := fun n t p =>
    iteratedDeriv n (fun u : ℝ => F u p) t
  have hd (n : ℕ) (t : ℝ) (p : AdelicProjectiveGroup) :
      HasDerivAt (fun u : ℝ => J n u p) (J (n + 1) t p) t := by
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f realGeodesicCurve p
    have he : (fun u : ℝ => F u p) = fun u : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realGeodesicCurve u)) := funext hg
    change HasDerivAt (iteratedDeriv n (fun u : ℝ => F u p))
      (iteratedDeriv (n + 1) (fun u : ℝ => F u p) t) t
    rw [he]
    exact canonicalAdelicGL2CuspLift_geodesic_jet_hasDerivAt N f g n t
  have hB (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t p, ‖J n t p‖ ≤ C := by
    obtain ⟨C, hC0, hC⟩ := canonicalAdelicGL2CuspLift_geodesic_jets_bounded N f
    refine ⟨C n, hC0 n, fun t p => ?_⟩
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f realGeodesicCurve p
    have he : (fun u : ℝ => F u p) = fun u : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realGeodesicCurve u)) := funext hg
    change ‖iteratedDeriv n (fun u : ℝ => F u p) t‖ ≤ _
    rw [he]
    exact hC n g t
  have hmem : ∀ n t, MemLp (J n t) 2 μ := memLp_bounded_jet_family J
    (fun t => by
      simpa only [J, iteratedDeriv_zero] using
        (adelicProjectiveRealOrbit_memLp N f realGeodesicCurve t).aestronglyMeasurable)
    hd (fun n => let ⟨C, _, hC⟩ := hB n; ⟨C, hC⟩)
  have hc := contDiff_toLp_of_bounded_jet_family J hmem hd hB
  simpa only [J, iteratedDeriv_zero] using hc

end
end Dubon2026
