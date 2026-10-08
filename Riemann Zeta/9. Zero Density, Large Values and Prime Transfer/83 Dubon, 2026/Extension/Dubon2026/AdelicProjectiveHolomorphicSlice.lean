import Dubon2026.AdelicProjectiveRepresentative
import Mathlib.Analysis.Complex.TaylorSeries

/-! # The actual original holomorphic slice and its measurable original Taylor series -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory Filter
open scoped MatrixGroups ModularForm Topology BigOperators

/-- The original slash transform at the genuine real base of each full adelic representative, evaluated at i+z. -/
def adelicProjectiveHolomorphicSlice (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (z : ℂ) (p : AdelicProjectiveGroup) : ℂ :=
  (((f : ℍ → ℂ) ∣[k] (mapGL ℝ (canonicalAdelicRealBase N (adelicProjectiveRepresentative p)))) ∘
    ofComplex) (Complex.I + z)

/-- Every original zero-parameter projective jet is exactly the holomorphic jet of its original slash transform. -/
theorem adelicUnipotentPointwiseJet_realBase (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (p : AdelicProjectiveGroup) :
    adelicUnipotentPointwiseJet N f n 0 p =
      iteratedDeriv n (((f : ℍ → ℂ) ∣[k]
        (mapGL ℝ (canonicalAdelicRealBase N (adelicProjectiveRepresentative p)))) ∘ ofComplex)
        Complex.I := by
  unfold adelicUnipotentPointwiseJet
  simp_rw [adelicProjectiveRealOrbit_representative_eq, canonicalAdelicGL2CuspLift_real_orbit]
  exact realWeightLift_unipotent_iteratedDeriv k (ModularFormClass.holo f) _ n

/-- The literal original holomorphic slice is the actual Taylor series of the original measurable projective jets. -/
theorem adelicProjectiveHolomorphicSlice_hasSum (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ))
    (p : AdelicProjectiveGroup) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • z ^ n • adelicUnipotentPointwiseJet N f n 0 p)
      (adelicProjectiveHolomorphicSlice N f z p) := by
  let F := (((f : ℍ → ℂ) ∣[k]
    (mapGL ℝ (canonicalAdelicRealBase N (adelicProjectiveRepresentative p)))) ∘ ofComplex)
  have hf : DifferentiableOn ℂ F (Metric.ball Complex.I (1 / 2 : ℝ)) := by
    apply (UpperHalfPlane.mdifferentiable_iff.mp ((ModularFormClass.holo f).slash k _)).mono
    intro w hw
    change 0 < w.im
    linarith [(half_disk_im_bounds (Metric.ball_subset_closedBall hw)).1]
  have hpoint : Complex.I + z ∈ Metric.ball Complex.I (1 / 2 : ℝ) := by
    simpa only [mem_ball_iff_norm, add_sub_cancel_left] using hz
  have hs := Complex.hasSum_taylorSeries_on_ball hf hpoint
  simpa only [adelicUnipotentPointwiseJet_realBase, add_sub_cancel_left,
    adelicProjectiveHolomorphicSlice, F] using hs

/-- The actual original holomorphic slice is measurable because its genuine Taylor partial sums are measurable original jets. -/
theorem adelicProjectiveHolomorphicSlice_aestronglyMeasurable (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    AEStronglyMeasurable (adelicProjectiveHolomorphicSlice N f z)
      (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) := by
  let q : ℕ → AdelicProjectiveGroup → ℂ := fun n p =>
    (n.factorial : ℂ)⁻¹ • z ^ n • adelicUnipotentPointwiseJet N f n 0 p
  have hq (n : ℕ) : MemLp (q n) 2
      (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) :=
    ((adelicUnipotentPointwiseJet_memLp N f n 0).const_smul (z ^ n)).const_smul
      ((n.factorial : ℂ)⁻¹)
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun j p => ∑ n ∈ Finset.range j, q n p)
    (fun j => (memLp_finsetSum (Finset.range j) (fun n _ => hq n)).aestronglyMeasurable)
  exact ae_of_all _ (fun p => (adelicProjectiveHolomorphicSlice_hasSum N f hz p).tendsto_sum_nat)

/-- The actual original complex slice is square-integrable on the genuine arithmetic domain throughout its proved disk. -/
theorem adelicProjectiveHolomorphicSlice_memLp (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    MemLp (adelicProjectiveHolomorphicSlice N f z) 2
      (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  obtain ⟨C, _, hC⟩ := realWeightLift_slash_disk_bounded f
  apply MemLp.of_bound (adelicProjectiveHolomorphicSlice_aestronglyMeasurable N f hz) C
  apply ae_of_all
  intro p
  apply hC _ (Complex.I + z)
  simpa only [mem_closedBall_iff_norm, add_sub_cancel_left] using hz.le

end
end Dubon2026
