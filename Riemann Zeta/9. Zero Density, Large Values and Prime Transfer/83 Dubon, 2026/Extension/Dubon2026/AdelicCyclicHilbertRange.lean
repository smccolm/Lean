import Dubon2026.AdelicCyclicStrongContinuity

/-! # The actual normed cyclic range inside quotient L2 -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The actual image of the original cyclic cusp representation in quotient L2. -/
def adelicCyclicRange {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Submodule ℂ (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N))) :=
  (adelicProjectiveCyclicToL2 N f).range

/-- The original cyclic vectors are linearly equivalent to their faithful actual L2 image. -/
def adelicCyclicRangeEquiv {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (adelicLiftCyclicRepresentation N k f).toSubmodule ≃ₗ[ℂ] adelicCyclicRange f :=
  LinearEquiv.ofInjective (adelicProjectiveCyclicToL2 N f) (adelicProjectiveCyclicToL2_injective N f)

/-- The range equivalence still evaluates to the literal original L2 realization. -/
theorem adelicCyclicRangeEquiv_coe {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    (adelicCyclicRangeEquiv f v).val = adelicProjectiveCyclicToL2 N f v := rfl

/-- The original representation transported to its actual L2 range, with no chosen norm. -/
def adelicCyclicRangeRepresentation {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Representation ℂ RationalAdelicGL2 (adelicCyclicRange f) :=
  ((adelicCyclicRangeEquiv f).conjRingEquiv.toMonoidHom).comp
    ((adelicLiftCyclicRepresentation N k f).toRepresentation)

/-- Transport intertwines exactly the original right-translation representation. -/
theorem adelicCyclicRangeRepresentation_apply {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    adelicCyclicRangeRepresentation f a (adelicCyclicRangeEquiv f v) =
      adelicCyclicRangeEquiv f ((adelicLiftCyclicRepresentation N k f).toRepresentation a v) := by
  change adelicCyclicRangeEquiv f ((adelicLiftCyclicRepresentation N k f).toRepresentation a
    ((adelicCyclicRangeEquiv f).symm (adelicCyclicRangeEquiv f v))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The transported representation preserves the inherited actual L2 norm. -/
theorem adelicCyclicRangeRepresentation_norm {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2)
    (v : adelicCyclicRange f) : ‖adelicCyclicRangeRepresentation f a v‖ = ‖v‖ := by
  obtain ⟨w, rfl⟩ := (adelicCyclicRangeEquiv f).surjective v
  rw [adelicCyclicRangeRepresentation_apply]
  change ‖adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation a w)‖ =
    ‖adelicProjectiveCyclicToL2 N f w‖
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    adelicLiftCyclic_inner]

/-- Every genuine group element acts by a linear isometry of the actual cyclic L2 range. -/
def adelicCyclicRangeIsometry {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2) :
    adelicCyclicRange f →ₗᵢ[ℂ] adelicCyclicRange f where
  toLinearMap := adelicCyclicRangeRepresentation f a
  norm_map' := adelicCyclicRangeRepresentation_norm f a

/-- The inherited normed realization has genuinely continuous original group orbits. -/
theorem adelicCyclicRangeRepresentation_continuous {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : adelicCyclicRange f) :
    Continuous (fun a : RationalAdelicGL2 => adelicCyclicRangeRepresentation f a v) := by
  obtain ⟨w, rfl⟩ := (adelicCyclicRangeEquiv f).surjective v
  simp_rw [adelicCyclicRangeRepresentation_apply]
  exact (adelicLiftCyclic_stronglyContinuous N f w).subtype_mk _

end
end Dubon2026
