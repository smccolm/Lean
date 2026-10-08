import Dubon2026.RealProjectiveArithmetic

/-! # Actual cyclic cusp vectors descend to the true projective arithmetic quotient -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The actual matrix extension agrees with the original general-linear integer embedding. -/
theorem integralToRealSL_mapGL (a : SL(2, ℤ)) :
    mapGL ℝ (integralToRealSL a) = mapGL ℝ a := by
  ext i j
  simp [integralToRealSL, Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map]

/-- Every original Gamma0 cyclic vector is unchanged under the genuine central sign. -/
theorem realLiftCyclic_neg {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {v : SL(2, ℝ) → ℂ} (hv : v ∈ (realLiftCyclicRepresentation k f).toSubmodule)
    (g : SL(2, ℝ)) : v (-g) = v g := by
  have hm : mapGL ℝ (-1 : SL(2, ℝ)) ∈ (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) := by
    rw [← integralToRealSL_neg_one, integralToRealSL_mapGL]
    exact ⟨-1, by simp [Gamma0_mem], rfl⟩
  simpa only [neg_one_mul] using realLiftCyclic_left_invariant f hv (-1) hm g

/-- The actual cyclic vector on the genuine central quotient, with representative independence proved. -/
def realProjectiveCyclicVector {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) : PSL(2, ℝ) → ℂ :=
  Quotient.lift v.val (by
    intro a b hab
    rcases (realSL2_projective_eq_iff a b).mp (Quotient.sound hab) with he | he
    · rw [he]
    · rw [he, realLiftCyclic_neg f v.property])

/-- The descended vector evaluates to the exact original vector at every representative. -/
theorem realProjectiveCyclicVector_mk {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) (g : SL(2, ℝ)) :
    realProjectiveCyclicVector f v (QuotientGroup.mk g) = v.val g := rfl

/-- The true projective vector retains continuity of the original cyclic vector. -/
theorem realProjectiveCyclicVector_continuous {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    Continuous (realProjectiveCyclicVector f v) :=
  (realLiftCyclic_continuous f v.property).quotient_lift _

/-- The descended vector retains the actual global cusp bound. -/
theorem realProjectiveCyclicVector_bounded {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : PSL(2, ℝ), ‖realProjectiveCyclicVector f v q‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := realLiftCyclic_bounded f v.property
  refine ⟨C, hC0, ?_⟩
  intro q
  induction q using Quotient.inductionOn with | h g => exact hC g

/-- The actual projective cyclic vector is invariant under the original projective arithmetic group. -/
theorem realProjectiveCyclicVector_arithmetic {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule)
    (γ : projectiveGamma0 Q) (q : PSL(2, ℝ)) :
    realProjectiveCyclicVector f v (γ • q) = realProjectiveCyclicVector f v q := by
  obtain ⟨a, ha, he⟩ := γ.property
  induction q using Quotient.inductionOn with | h g => ?_
  change realProjectiveCyclicVector f v (integralToRealPSL γ.val * QuotientGroup.mk g) = _
  rw [← he]
  change v.val (integralToRealSL a * g) = v.val g
  apply realLiftCyclic_left_invariant f v.property (integralToRealSL a)
  rw [integralToRealSL_mapGL]
  exact ⟨a, ha, rfl⟩

/-- Every actual cyclic vector is genuinely L2 on a true projective arithmetic fundamental domain. -/
theorem realProjectiveCyclicVector_memLp_two {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    MemLp (realProjectiveCyclicVector f v) 2
      (realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q)) := by
  letI : IsFiniteMeasure (realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q)) := by
    constructor
    simpa only [Measure.restrict_apply_univ] using realProjectiveGamma0Domain_volume_lt_top Q
  obtain ⟨C, _, hC⟩ := realProjectiveCyclicVector_bounded f v
  exact MemLp.of_bound (realProjectiveCyclicVector_continuous f v).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end
end Dubon2026
