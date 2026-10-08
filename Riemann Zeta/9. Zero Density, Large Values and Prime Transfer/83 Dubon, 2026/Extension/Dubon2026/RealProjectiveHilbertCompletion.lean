import Dubon2026.RealProjectiveHilbertRange
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Completion of the genuine original cyclic L2 representation -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory UniformSpace
open scoped MatrixGroups

/-- The actual Hilbert completion of the original faithful cyclic L2 range. -/
abbrev RealProjectiveHilbert {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :=
  Completion (realProjectiveCyclicRange f)

/-- Each original isometry extends as the actual completion of its continuous linear map. -/
def realProjectiveHilbertOperator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ)) :
    RealProjectiveHilbert f →L[ℂ] RealProjectiveHilbert f :=
  (realProjectiveRangeIsometry f a).toContinuousLinearMap.completion

/-- The completed operator agrees exactly with original right translation on the dense original range. -/
theorem realProjectiveHilbertOperator_coe {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ))
    (v : realProjectiveCyclicRange f) :
    realProjectiveHilbertOperator f a (v : Completion (realProjectiveCyclicRange f)) =
      (realProjectiveRangeRepresentation f a v : Completion (realProjectiveCyclicRange f)) :=
  ContinuousLinearMap.completion_apply_coe _ v

/-- Actual completion retains norm preservation on every Hilbert vector. -/
theorem realProjectiveHilbertOperator_norm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ))
    (v : RealProjectiveHilbert f) : ‖realProjectiveHilbertOperator f a v‖ = ‖v‖ := by
  have hi : Isometry (realProjectiveHilbertOperator f a) :=
    (realProjectiveRangeIsometry f a).isometry.completion_map
  exact hi.norm_map_of_map_zero (map_zero _) v

/-- The genuine identity group element acts as the identity on the completed original space. -/
theorem realProjectiveHilbertOperator_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (v : RealProjectiveHilbert f) :
    realProjectiveHilbertOperator f 1 v = v := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (realProjectiveHilbertOperator f 1).continuous continuous_id
  | ih v =>
    rw [realProjectiveHilbertOperator_coe]
    simp only [map_one, Module.End.one_apply]

/-- The actual completed operators retain the original group multiplication law. -/
theorem realProjectiveHilbertOperator_mul {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a b : PSL(2, ℝ))
    (v : RealProjectiveHilbert f) :
    realProjectiveHilbertOperator f (a * b) v =
      realProjectiveHilbertOperator f a (realProjectiveHilbertOperator f b v) := by
  induction v using Completion.induction_on with
  | hp =>
    exact isClosed_eq (realProjectiveHilbertOperator f (a * b)).continuous
      ((realProjectiveHilbertOperator f a).continuous.comp
        (realProjectiveHilbertOperator f b).continuous)
  | ih v =>
    rw [realProjectiveHilbertOperator_coe, realProjectiveHilbertOperator_coe,
      realProjectiveHilbertOperator_coe]
    simp only [map_mul, Module.End.mul_apply]

/-- The actual original cyclic representation on its Hilbert completion. -/
def realProjectiveHilbertRepresentation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Representation ℂ PSL(2, ℝ) (RealProjectiveHilbert f) where
  toFun a := (realProjectiveHilbertOperator f a).toLinearMap
  map_one' := by ext v; exact realProjectiveHilbertOperator_one f v
  map_mul' a b := by ext v; exact realProjectiveHilbertOperator_mul f a b v

/-- The extended original action preserves genuine Hilbert distances. -/
theorem realProjectiveHilbertOperator_dist {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ))
    (v w : RealProjectiveHilbert f) :
    dist (realProjectiveHilbertOperator f a v) (realProjectiveHilbertOperator f a w) =
      dist v w := by
  rw [dist_eq_norm, ← map_sub]
  exact (realProjectiveHilbertOperator_norm f a (v - w)).trans (dist_eq_norm v w).symm

/-- Density and actual isometries extend strong continuity to every completed original cusp vector. -/
theorem realProjectiveHilbertRepresentation_stronglyContinuous {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : RealProjectiveHilbert f) :
    Continuous (fun a : PSL(2, ℝ) => realProjectiveHilbertRepresentation f a v) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w, hw⟩ := Completion.denseRange_coe.exists_dist_lt v
    (show 0 < ε / 4 by positivity)
  have hc : Continuous (fun b : PSL(2, ℝ) => realProjectiveHilbertOperator f b
      (w : Completion (realProjectiveCyclicRange f))) := by
    simpa only [realProjectiveHilbertOperator_coe] using
      (Completion.continuous_coe (realProjectiveCyclicRange f)).comp
        (realProjectiveRangeRepresentation_continuous f w)
  have he := Metric.tendsto_nhds.mp (hc.tendsto a) (ε / 2) (by positivity)
  filter_upwards [he] with b hb
  change dist (realProjectiveHilbertOperator f b v) (realProjectiveHilbertOperator f a v) < ε
  have ht := dist_triangle (realProjectiveHilbertOperator f b v)
    (realProjectiveHilbertOperator f b (w : Completion (realProjectiveCyclicRange f)))
    (realProjectiveHilbertOperator f a v)
  have ht' := dist_triangle
    (realProjectiveHilbertOperator f b (w : Completion (realProjectiveCyclicRange f)))
    (realProjectiveHilbertOperator f a (w : Completion (realProjectiveCyclicRange f)))
    (realProjectiveHilbertOperator f a v)
  rw [realProjectiveHilbertOperator_dist] at ht ht'
  rw [dist_comm (w : Completion (realProjectiveCyclicRange f)) v] at ht'
  linarith

/-- The literal original cyclic representation embeds linearly in its actual Hilbert completion. -/
def realProjectiveHilbertEmbedding {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    (realLiftCyclicRepresentation k f).toSubmodule →ₗ[ℂ] RealProjectiveHilbert f :=
  (Completion.toComplₗᵢ (𝕜 := ℂ) (E := realProjectiveCyclicRange f)).toLinearMap.comp
    (realProjectiveRangeEquiv f).toLinearMap

/-- No original cusp vector disappears on passage to the actual Hilbert completion. -/
theorem realProjectiveHilbertEmbedding_injective {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Function.Injective (realProjectiveHilbertEmbedding f) :=
  (Completion.coe_injective _).comp (realProjectiveRangeEquiv f).injective

/-- The original cyclic vectors are dense in precisely their constructed Hilbert space. -/
theorem realProjectiveHilbertEmbedding_dense {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    DenseRange (realProjectiveHilbertEmbedding f) := by
  change Dense (Set.range (((↑) : realProjectiveCyclicRange f →
    Completion (realProjectiveCyclicRange f)) ∘ realProjectiveRangeEquiv f))
  rw [Set.range_comp, (realProjectiveRangeEquiv f).surjective.range_eq, Set.image_univ]
  exact Completion.denseRange_coe

/-- The completed representation intertwines the exact original right-translation representation. -/
theorem realProjectiveHilbertEmbedding_intertwines {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ))
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    realProjectiveHilbertRepresentation f a (realProjectiveHilbertEmbedding f v) =
      realProjectiveHilbertEmbedding f (realProjectiveCyclicRepresentation f a v) := by
  change realProjectiveHilbertOperator f a
    ((realProjectiveRangeEquiv f v) : Completion (realProjectiveCyclicRange f)) = _
  rw [realProjectiveHilbertOperator_coe, realProjectiveRangeRepresentation_apply]
  rfl

/-- The completed actual representation is unitary for its genuine Hilbert inner product. -/
theorem realProjectiveHilbertRepresentation_inner {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : PSL(2, ℝ))
    (v w : RealProjectiveHilbert f) :
    inner ℂ (realProjectiveHilbertRepresentation f a v) (realProjectiveHilbertRepresentation f a w) =
      inner ℂ v w := by
  change inner ℂ (realProjectiveHilbertOperator f a v)
    (realProjectiveHilbertOperator f a w) = inner ℂ v w
  refine Completion.induction_on₂ v w (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x y
  rw [realProjectiveHilbertOperator_coe, realProjectiveHilbertOperator_coe,
    Completion.inner_coe, Completion.inner_coe]
  obtain ⟨u, rfl⟩ := (realProjectiveRangeEquiv f).surjective x
  obtain ⟨z, rfl⟩ := (realProjectiveRangeEquiv f).surjective y
  rw [realProjectiveRangeRepresentation_apply, realProjectiveRangeRepresentation_apply]
  exact realProjectiveCyclicRepresentation_inner f a u z

end
end Dubon2026
