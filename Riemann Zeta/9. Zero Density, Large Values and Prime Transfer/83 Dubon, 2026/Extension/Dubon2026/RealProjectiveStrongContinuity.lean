import Dubon2026.RealProjectiveRepresentation

/-! # Strong continuity of the original cyclic action in its actual L2 realization -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- The genuine matrix coefficients are jointly continuous by the original global cusp bound and finite quotient volume. -/
theorem realProjectiveCyclic_matrixCoefficient_continuous {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v w : (realLiftCyclicRepresentation k f).toSubmodule) :
    Continuous (fun p : PSL(2, ℝ) × PSL(2, ℝ) =>
      inner ℂ (realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f p.1 v))
        (realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f p.2 w))) := by
  simp_rw [realProjectiveCyclicToL2_inner, realProjectiveCyclicPairing,
    realProjectiveCyclicRepresentation_apply]
  letI : IsFiniteMeasure (realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q)) := by
    constructor
    simpa only [Measure.restrict_apply_univ] using realProjectiveGamma0Domain_volume_lt_top Q
  obtain ⟨Cv, hCv0, hCv⟩ := realProjectiveCyclicVector_bounded f v
  obtain ⟨Cw, _, hCw⟩ := realProjectiveCyclicVector_bounded f w
  apply continuous_of_dominated (bound := fun _ => Cv * Cw)
  · intro p
    exact (((realProjectiveCyclicVector_continuous f v).comp
      (continuous_id.mul_const p.1)).star.mul
        ((realProjectiveCyclicVector_continuous f w).comp
          (continuous_id.mul_const p.2))).aestronglyMeasurable
  · intro p
    apply Filter.Eventually.of_forall
    intro q
    simpa only [norm_mul, Complex.norm_conj] using
      mul_le_mul (hCv (q * p.1)) (hCw (q * p.2)) (norm_nonneg _) hCv0
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro q
    exact (((realProjectiveCyclicVector_continuous f v).comp
      (continuous_const.mul continuous_fst)).star.mul
        ((realProjectiveCyclicVector_continuous f w).comp
          (continuous_const.mul continuous_snd)))

/-- Every actual cyclic orbit is continuous in the genuine quotient L2 norm. -/
theorem realProjectiveCyclicRepresentation_stronglyContinuous {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    Continuous (fun a : PSL(2, ℝ) =>
      realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f a v)) := by
  let F := fun a : PSL(2, ℝ) =>
    realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f a v)
  have hc : Continuous (fun p : PSL(2, ℝ) × PSL(2, ℝ) => inner ℂ (F p.1) (F p.2)) :=
    realProjectiveCyclic_matrixCoefficient_continuous f v v
  have hd : Continuous (fun p : PSL(2, ℝ) × PSL(2, ℝ) => ‖F p.1 - F p.2‖ ^ 2) := by
    simp_rw [norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact (((Complex.continuous_re.comp (hc.comp (continuous_fst.prodMk continuous_fst))).sub
      (continuous_const.mul (Complex.continuous_re.comp hc))).add
      (Complex.continuous_re.comp (hc.comp (continuous_snd.prodMk continuous_snd))))
  apply continuous_iff_continuous_dist.mpr
  have hs := Real.continuous_sqrt.comp hd
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, dist_eq_norm] using hs

end
end Dubon2026
