import Dubon2026.AdelicUnipotentJetBounds
import Dubon2026.BoundedL2Smoothness
import Dubon2026.AdelicProjectiveRealDerivative

/-! # Smoothness of the actual original unipotent quotient L2 orbit -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ContDiff

/-- The original adelic cusp generator's actual unipotent orbit is smooth to every order in the genuine arithmetic quotient L2 norm. -/
theorem adelicCyclicGenerator_unipotent_L2_contDiff (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ContDiff ℝ ∞ (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))) := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  let F := adelicProjectiveRealOrbit N f realUpperUnipotent
  let J : ℕ → ℝ → AdelicProjectiveGroup → ℂ := fun n t p =>
    iteratedDeriv n (fun u : ℝ => F u p) t
  have hd (n : ℕ) (t : ℝ) (p : AdelicProjectiveGroup) :
      HasDerivAt (fun u : ℝ => J n u p) (J (n + 1) t p) t := by
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f realUpperUnipotent p
    have he : (fun u : ℝ => F u p) = fun u : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realUpperUnipotent u)) := funext hg
    change HasDerivAt (iteratedDeriv n (fun u : ℝ => F u p))
      (iteratedDeriv (n + 1) (fun u : ℝ => F u p) t) t
    rw [he]
    exact canonicalAdelicGL2CuspLift_unipotent_jet_hasDerivAt N f g n t
  have hB (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t p, ‖J n t p‖ ≤ C := by
    obtain ⟨C, hC0, hC⟩ := canonicalAdelicGL2CuspLift_unipotent_jets_bounded N f
    refine ⟨(n.factorial : ℝ) * C / (1 / 2 : ℝ) ^ n, by positivity, fun t p => ?_⟩
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f realUpperUnipotent p
    have he : (fun u : ℝ => F u p) = fun u : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realUpperUnipotent u)) := funext hg
    change ‖iteratedDeriv n (fun u : ℝ => F u p) t‖ ≤ _
    rw [he]
    exact hC n g t
  have hmem : ∀ n t, MemLp (J n t) 2 μ := memLp_bounded_jet_family J
    (fun t => by
      simpa only [J, iteratedDeriv_zero] using
        (adelicProjectiveRealOrbit_memLp N f realUpperUnipotent t).aestronglyMeasurable)
    hd (fun n => let ⟨C, _, hC⟩ := hB n; ⟨C, hC⟩)
  have hc := contDiff_toLp_of_bounded_jet_family J hmem hd hB
  simpa only [J, iteratedDeriv_zero] using hc

end
end Dubon2026
