import Dubon2026.AdelicGeneratorUnipotentSmoothness

/-! # Genuine measurable jet vectors of the original adelic unipotent orbit -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The literal original projective unipotent orbit jet, retaining its derivative order and real parameter. -/
def adelicUnipotentPointwiseJet (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (t : ℝ)
    (p : AdelicProjectiveGroup) : ℂ :=
  iteratedDeriv n (fun u : ℝ => adelicProjectiveRealOrbit N f realUpperUnipotent u p) t

/-- Every original projective jet has the next original jet as its genuine derivative. -/
theorem adelicUnipotentPointwiseJet_hasDerivAt (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (t : ℝ)
    (p : AdelicProjectiveGroup) :
    HasDerivAt (fun u : ℝ => adelicUnipotentPointwiseJet N f n u p)
      (adelicUnipotentPointwiseJet N f (n + 1) t p) t := by
  obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f realUpperUnipotent p
  have he := funext hg
  unfold adelicUnipotentPointwiseJet
  rw [he]
  exact canonicalAdelicGL2CuspLift_unipotent_jet_hasDerivAt N f g n t

/-- The genuine original projective jet family retains the exact uniform factorial Cauchy bound. -/
theorem adelicUnipotentPointwiseJet_bound (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ t : ℝ, ∀ p : AdelicProjectiveGroup,
      ‖adelicUnipotentPointwiseJet N f n t p‖ ≤ (n.factorial : ℝ) * C / (1 / 2 : ℝ) ^ n := by
  obtain ⟨C, hC0, hC⟩ := canonicalAdelicGL2CuspLift_unipotent_jets_bounded N f
  refine ⟨C, hC0, fun n t p => ?_⟩
  obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f realUpperUnipotent p
  unfold adelicUnipotentPointwiseJet
  rw [funext hg]
  exact hC n g t

/-- Every original projective jet is genuinely square-integrable on the original arithmetic fundamental domain. -/
theorem adelicUnipotentPointwiseJet_memLp (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (t : ℝ) :
    MemLp (adelicUnipotentPointwiseJet N f n t) 2
      (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  apply memLp_bounded_jet_family (μ := μ) (adelicUnipotentPointwiseJet N f)
  · intro u
    simpa only [adelicUnipotentPointwiseJet, iteratedDeriv_zero] using
      (adelicProjectiveRealOrbit_memLp N f realUpperUnipotent u).aestronglyMeasurable
  · exact adelicUnipotentPointwiseJet_hasDerivAt N f
  · intro m
    obtain ⟨C, _, hC⟩ := adelicUnipotentPointwiseJet_bound N f
    exact ⟨(m.factorial : ℝ) * C / (1 / 2 : ℝ) ^ m, hC m⟩

/-- The actual original unipotent jet as a vector in the genuine arithmetic quotient L2 space. -/
def adelicUnipotentL2Jet (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (t : ℝ) :
    Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) :=
  (adelicUnipotentPointwiseJet_memLp N f n t).toLp (adelicUnipotentPointwiseJet N f n t)

/-- The genuine original Taylor coefficient vector is exactly its original zero-parameter jet divided by the factorial. -/
def adelicUnipotentTaylorCoefficient (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) :
    Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) :=
  (n.factorial : ℂ)⁻¹ • adelicUnipotentL2Jet N f n 0

/-- The actual original Taylor coefficient vectors satisfy a genuine geometric Hilbert norm bound. -/
theorem adelicUnipotentTaylorCoefficient_norm_bound (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖adelicUnipotentTaylorCoefficient N f n‖ ≤ K * 2 ^ n := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  have h1 : MemLp (fun _ : AdelicProjectiveGroup => (1 : ℂ)) 2 μ := memLp_const 1
  let v := h1.toLp (fun _ : AdelicProjectiveGroup => (1 : ℂ))
  obtain ⟨C, hC0, hC⟩ := adelicUnipotentPointwiseJet_bound N f
  refine ⟨C * ‖v‖, mul_nonneg hC0 (norm_nonneg _), fun n => ?_⟩
  have hn : ‖adelicUnipotentL2Jet N f n 0‖ ≤
      ((n.factorial : ℝ) * C / (1 / 2 : ℝ) ^ n) * ‖v‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(adelicUnipotentPointwiseJet_memLp N f n 0).coeFn_toLp, h1.coeFn_toLp]
      with p hp hv
    change ‖adelicUnipotentL2Jet N f n 0 p‖ ≤ _ * ‖v p‖
    change ‖(adelicUnipotentPointwiseJet_memLp N f n 0).toLp _ p‖ ≤
      _ * ‖h1.toLp _ p‖
    rw [hp, hv, norm_one, mul_one]
    exact hC n 0 p
  rw [adelicUnipotentTaylorCoefficient, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * (((n.factorial : ℝ) * C / (1 / 2 : ℝ) ^ n) * ‖v‖) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (C * ‖v‖) * 2 ^ n := by
      have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have he : (1 / 2 : ℝ) ^ n = (2 ^ n : ℝ)⁻¹ := by rw [one_div_pow, one_div]
      rw [he, div_inv_eq_mul]
      field_simp

end
end Dubon2026
