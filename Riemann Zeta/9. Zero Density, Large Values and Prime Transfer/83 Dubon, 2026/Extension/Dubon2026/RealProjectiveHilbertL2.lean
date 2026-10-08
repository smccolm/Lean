import Dubon2026.RealProjectiveHilbertCompletion
import Mathlib.Analysis.Normed.Operator.Extend

/-! # The completed original representation inside its genuine quotient L2 space -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane CongruenceSubgroup MeasureTheory UniformSpace
open scoped MatrixGroups

/-- Extension of the actual cyclic range inclusion into the original complete quotient L2 space. -/
def realProjectiveHilbertToL2 {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    RealProjectiveHilbert f →L[ℂ]
      Lp ℂ 2 (realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q)) :=
  (realProjectiveCyclicRange f).subtypeₗᵢ.toContinuousLinearMap.extend
    (Completion.toComplL (𝕜 := ℂ) (E := realProjectiveCyclicRange f))

/-- The completed realization agrees with the literal original range inclusion. -/
theorem realProjectiveHilbertToL2_coe {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : realProjectiveCyclicRange f) :
    realProjectiveHilbertToL2 f (v : RealProjectiveHilbert f) = v.val :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe _) v

/-- The completed realization preserves precisely the original quotient L2 norm. -/
theorem realProjectiveHilbertToL2_norm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : RealProjectiveHilbert f) : ‖realProjectiveHilbertToL2 f v‖ = ‖v‖ := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (realProjectiveHilbertToL2 f).continuous.norm continuous_norm
  | ih v => rw [realProjectiveHilbertToL2_coe, Completion.norm_coe]; rfl

/-- The completed original space is isometrically realized inside the genuine quotient L2 space. -/
def realProjectiveHilbertL2Isometry {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    RealProjectiveHilbert f →ₗᵢ[ℂ]
      Lp ℂ 2 (realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q)) where
  toLinearMap := (realProjectiveHilbertToL2 f).toLinearMap
  norm_map' := realProjectiveHilbertToL2_norm f

/-- No completed original vector is lost in the actual quotient realization. -/
theorem realProjectiveHilbertToL2_injective {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Function.Injective (realProjectiveHilbertToL2 f) :=
  (realProjectiveHilbertL2Isometry f).injective

/-- The actual quotient realization retains exactly the original cyclic cusp function. -/
theorem realProjectiveHilbertToL2_embedding {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    realProjectiveHilbertToL2 f (realProjectiveHilbertEmbedding f v) =
      realProjectiveCyclicToL2 f v :=
  realProjectiveHilbertToL2_coe f (realProjectiveRangeEquiv f v)

/-- The completed original representation occupies exactly the closure of its literal cyclic L2 range. -/
theorem realProjectiveHilbertToL2_range {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Set.range (realProjectiveHilbertToL2 f) = closure (Set.range (realProjectiveCyclicToL2 f)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    induction v using Completion.induction_on with
    | hp => exact isClosed_closure.preimage (realProjectiveHilbertToL2 f).continuous
    | ih v =>
      rw [realProjectiveHilbertToL2_coe]
      exact subset_closure v.property
  · apply closure_minimal
    · rintro _ ⟨v, rfl⟩
      exact ⟨realProjectiveHilbertEmbedding f v, realProjectiveHilbertToL2_embedding f v⟩
    · exact (realProjectiveHilbertL2Isometry f).isometry.isClosedEmbedding.isClosed_range

/-- The genuine quotient integral pairing is retained on the entire completed original space. -/
theorem realProjectiveHilbertToL2_inner {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v w : RealProjectiveHilbert f) :
    inner ℂ (realProjectiveHilbertToL2 f v) (realProjectiveHilbertToL2 f w) = inner ℂ v w := by
  refine Completion.induction_on₂ v w (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x y
  rw [realProjectiveHilbertToL2_coe, realProjectiveHilbertToL2_coe, Completion.inner_coe]
  rfl

end
end Dubon2026
