import Dubon2026.RealProjectiveStrongContinuity

/-! # The actual normed cyclic range inside quotient L2 -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The actual image of the original cyclic cusp representation in quotient L2. -/
def realProjectiveCyclicRange {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Submodule ℂ (Lp ℂ 2 (realProjectiveMeasure.restrict (realProjectiveGamma0Domain Q))) :=
  (realProjectiveCyclicToL2 f).range

/-- The original cyclic vectors are linearly equivalent to their faithful actual L2 image. -/
def realProjectiveRangeEquiv {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    (realLiftCyclicRepresentation k f).toSubmodule ≃ₗ[ℂ] realProjectiveCyclicRange f :=
  LinearEquiv.ofInjective (realProjectiveCyclicToL2 f) (realProjectiveCyclicToL2_injective f)

/-- The range equivalence still evaluates to the literal original L2 realization. -/
theorem realProjectiveRangeEquiv_coe {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    (realProjectiveRangeEquiv f v).val = realProjectiveCyclicToL2 f v := rfl

/-- The original representation transported to its actual L2 range, with no chosen norm. -/
def realProjectiveRangeRepresentation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Representation ℂ PSL(2, ℝ) (realProjectiveCyclicRange f) :=
  ((realProjectiveRangeEquiv f).conjRingEquiv.toMonoidHom).comp
    (realProjectiveCyclicRepresentation f)

/-- Transport intertwines exactly the original right-translation representation. -/
theorem realProjectiveRangeRepresentation_apply {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ))
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    realProjectiveRangeRepresentation f a (realProjectiveRangeEquiv f v) =
      realProjectiveRangeEquiv f (realProjectiveCyclicRepresentation f a v) := by
  change realProjectiveRangeEquiv f (realProjectiveCyclicRepresentation f a
    ((realProjectiveRangeEquiv f).symm (realProjectiveRangeEquiv f v))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The transported representation preserves the inherited actual L2 norm. -/
theorem realProjectiveRangeRepresentation_norm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ))
    (v : realProjectiveCyclicRange f) : ‖realProjectiveRangeRepresentation f a v‖ = ‖v‖ := by
  obtain ⟨w, rfl⟩ := (realProjectiveRangeEquiv f).surjective v
  rw [realProjectiveRangeRepresentation_apply]
  change ‖realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f a w)‖ =
    ‖realProjectiveCyclicToL2 f w‖
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    realProjectiveCyclicRepresentation_inner]

/-- Every genuine group element acts by a linear isometry of the actual cyclic L2 range. -/
def realProjectiveRangeIsometry {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ)) :
    realProjectiveCyclicRange f →ₗᵢ[ℂ] realProjectiveCyclicRange f where
  toLinearMap := realProjectiveRangeRepresentation f a
  norm_map' := realProjectiveRangeRepresentation_norm f a

/-- The inherited normed realization has genuinely continuous original group orbits. -/
theorem realProjectiveRangeRepresentation_continuous {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : realProjectiveCyclicRange f) :
    Continuous (fun a : PSL(2, ℝ) => realProjectiveRangeRepresentation f a v) := by
  obtain ⟨w, rfl⟩ := (realProjectiveRangeEquiv f).surjective v
  simp_rw [realProjectiveRangeRepresentation_apply]
  exact (realProjectiveCyclicRepresentation_stronglyContinuous f w).subtype_mk _

end
end Dubon2026
