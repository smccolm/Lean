import Dubon2026.AdelicCyclicHilbertCompletion
import Mathlib.Analysis.Normed.Operator.Extend

/-! # The completed original representation inside its genuine quotient L2 space -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory UniformSpace
open scoped MatrixGroups

/-- Extension of the actual cyclic range inclusion into the original complete quotient L2 space. -/
def adelicCyclicHilbertToL2 {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    AdelicCyclicHilbert f →L[ℂ]
      Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) :=
  (adelicCyclicRange f).subtypeₗᵢ.toContinuousLinearMap.extend
    (Completion.toComplL (𝕜 := ℂ) (E := adelicCyclicRange f))

/-- The completed realization agrees with the literal original range inclusion. -/
theorem adelicCyclicHilbertToL2_coe {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : adelicCyclicRange f) :
    adelicCyclicHilbertToL2 f (v : AdelicCyclicHilbert f) = v.val :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe _) v

/-- The completed realization preserves precisely the original quotient L2 norm. -/
theorem adelicCyclicHilbertToL2_norm {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : AdelicCyclicHilbert f) : ‖adelicCyclicHilbertToL2 f v‖ = ‖v‖ := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (adelicCyclicHilbertToL2 f).continuous.norm continuous_norm
  | ih v => rw [adelicCyclicHilbertToL2_coe, Completion.norm_coe]; rfl

/-- The completed original space is isometrically realized inside the genuine quotient L2 space. -/
def adelicCyclicHilbertL2Isometry {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    AdelicCyclicHilbert f →ₗᵢ[ℂ]
      Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) where
  toLinearMap := (adelicCyclicHilbertToL2 f).toLinearMap
  norm_map' := adelicCyclicHilbertToL2_norm f

/-- No completed original vector is lost in the actual quotient realization. -/
theorem adelicCyclicHilbertToL2_injective {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Function.Injective (adelicCyclicHilbertToL2 f) :=
  (adelicCyclicHilbertL2Isometry f).injective

/-- The actual quotient realization retains exactly the original cyclic cusp function. -/
theorem adelicCyclicHilbertToL2_embedding {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    adelicCyclicHilbertToL2 f (adelicCyclicHilbertEmbedding f v) =
      adelicProjectiveCyclicToL2 N f v :=
  adelicCyclicHilbertToL2_coe f (adelicCyclicRangeEquiv f v)

/-- The completed original representation occupies exactly the closure of its literal cyclic L2 range. -/
theorem adelicCyclicHilbertToL2_range {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Set.range (adelicCyclicHilbertToL2 f) = closure (Set.range (adelicProjectiveCyclicToL2 N f)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    induction v using Completion.induction_on with
    | hp => exact isClosed_closure.preimage (adelicCyclicHilbertToL2 f).continuous
    | ih v =>
      rw [adelicCyclicHilbertToL2_coe]
      exact subset_closure v.property
  · apply closure_minimal
    · rintro _ ⟨v, rfl⟩
      exact ⟨adelicCyclicHilbertEmbedding f v, adelicCyclicHilbertToL2_embedding f v⟩
    · exact (adelicCyclicHilbertL2Isometry f).isometry.isClosedEmbedding.isClosed_range

/-- The genuine quotient integral pairing is retained on the entire completed original space. -/
theorem adelicCyclicHilbertToL2_inner {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : AdelicCyclicHilbert f) :
    inner ℂ (adelicCyclicHilbertToL2 f v) (adelicCyclicHilbertToL2 f w) = inner ℂ v w := by
  refine Completion.induction_on₂ v w (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x y
  rw [adelicCyclicHilbertToL2_coe, adelicCyclicHilbertToL2_coe, Completion.inner_coe]
  rfl

end
end Dubon2026
