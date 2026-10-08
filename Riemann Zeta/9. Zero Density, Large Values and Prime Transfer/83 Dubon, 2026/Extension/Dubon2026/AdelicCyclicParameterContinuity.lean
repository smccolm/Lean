import Dubon2026.AdelicCyclicUnitary

/-! # Genuine L2 continuity of parameterized original adelic cyclic translates -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- All actual right translates of an original cyclic vector satisfy the same genuine global bound. -/
theorem adelicCyclicProjectiveFunction_right_uniform_bound (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : RationalAdelicGL2, ∀ p,
      ‖adelicCyclicProjectiveFunction N f
        ((adelicLiftCyclicRepresentation N k f).toRepresentation h v) p‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := adelicLiftCyclic_bounded N f v.property
  refine ⟨C, hC0, ?_⟩
  intro h p
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
  obtain ⟨a, ha⟩ := Matrix.ProjGenLinGroup.mk_surjective p.2
  have hp : p = (QuotientGroup.mk r, Matrix.ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
  rw [hp, adelicCyclicProjectiveFunction_mk]
  exact hC _

/-- At each original projective point, every continuous family of original adelic right translates varies continuously. -/
theorem adelicCyclicProjectiveFunction_right_parameter_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    {X : Type*} [TopologicalSpace X] (h : X → RationalAdelicGL2) (hh : Continuous h)
    (p : AdelicProjectiveGroup) :
    Continuous (fun x => adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (h x) v) p) := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
  obtain ⟨a, ha⟩ := Matrix.ProjGenLinGroup.mk_surjective p.2
  have hp : p = (QuotientGroup.mk r, Matrix.ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
  rw [hp]
  exact (adelicLiftCyclic_continuous N f v.property).comp (continuous_const.mul hh)

/-- Genuine bounded original matrix coefficients are continuous along every continuous first-countable parameter family. -/
theorem adelicLiftCyclic_parameter_matrixCoefficient_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (h₁ h₂ : X → RationalAdelicGL2) (hh₁ : Continuous h₁) (hh₂ : Continuous h₂) :
    Continuous (fun x => inner ℂ
      (adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation (h₁ x) v))
      (adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation (h₂ x) w))) := by
  simp_rw [adelicProjectiveCyclicToL2_inner, adelicProjectiveCyclicPairing]
  letI : IsFiniteMeasure (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) := by
    constructor
    simpa only [Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  obtain ⟨Cv, hCv0, hCv⟩ := adelicCyclicProjectiveFunction_right_uniform_bound N f v
  obtain ⟨Cw, _, hCw⟩ := adelicCyclicProjectiveFunction_right_uniform_bound N f w
  apply continuous_of_dominated (bound := fun _ => Cv * Cw)
  · intro x
    exact ((adelicCyclicProjectiveFunction_continuous N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (h₁ x) v)).star.mul
        (adelicCyclicProjectiveFunction_continuous N f
          ((adelicLiftCyclicRepresentation N k f).toRepresentation (h₂ x) w))).aestronglyMeasurable
  · intro x
    apply Filter.Eventually.of_forall
    intro p
    simpa only [norm_mul, Complex.norm_conj] using
      mul_le_mul (hCv (h₁ x) p) (hCw (h₂ x) p) (norm_nonneg _) hCv0
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro p
    exact (adelicCyclicProjectiveFunction_right_parameter_continuous N f v h₁ hh₁ p).star.mul
      (adelicCyclicProjectiveFunction_right_parameter_continuous N f w h₂ hh₂ p)

/-- Joint continuity of the actual complex inner products implies continuity in the original Hilbert norm. -/
theorem continuous_of_joint_complex_inner {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (F : X → E)
    (hc : Continuous (fun p : X × X => inner ℂ (F p.1) (F p.2))) : Continuous F := by
  have hd : Continuous (fun p : X × X => ‖F p.1 - F p.2‖ ^ 2) := by
    simp_rw [norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact (((Complex.continuous_re.comp (hc.comp (continuous_fst.prodMk continuous_fst))).sub
      (continuous_const.mul (Complex.continuous_re.comp hc))).add
      (Complex.continuous_re.comp (hc.comp (continuous_snd.prodMk continuous_snd))))
  apply continuous_iff_continuous_dist.mpr
  have hs := Real.continuous_sqrt.comp hd
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, dist_eq_norm] using hs

/-- The actual original adelic cyclic orbit is continuous in genuine L2 along every continuous first-countable parameter family. -/
theorem adelicLiftCyclic_parameter_stronglyContinuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (h : X → RationalAdelicGL2) (hh : Continuous h) :
    Continuous (fun x => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (h x) v)) := by
  apply continuous_of_joint_complex_inner
  exact adelicLiftCyclic_parameter_matrixCoefficient_continuous N f v v
    (h ∘ Prod.fst) (h ∘ Prod.snd) (hh.comp continuous_fst) (hh.comp continuous_snd)

end
end Dubon2026
