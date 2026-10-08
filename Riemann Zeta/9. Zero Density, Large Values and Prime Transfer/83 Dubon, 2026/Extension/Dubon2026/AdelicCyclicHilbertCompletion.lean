import Dubon2026.AdelicCyclicHilbertRange
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Completion of the genuine original cyclic L2 representation -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory UniformSpace
open scoped MatrixGroups

/-- The actual Hilbert completion of the original faithful cyclic L2 range. -/
abbrev AdelicCyclicHilbert {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  Completion (adelicCyclicRange f)

/-- Each original isometry extends as the actual completion of its continuous linear map. -/
def adelicCyclicHilbertOperator {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  (adelicCyclicRangeIsometry f a).toContinuousLinearMap.completion

/-- The completed operator agrees exactly with original right translation on the dense original range. -/
theorem adelicCyclicHilbertOperator_coe {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2)
    (v : adelicCyclicRange f) :
    adelicCyclicHilbertOperator f a (v : Completion (adelicCyclicRange f)) =
      (adelicCyclicRangeRepresentation f a v : Completion (adelicCyclicRange f)) :=
  ContinuousLinearMap.completion_apply_coe _ v

/-- Actual completion retains norm preservation on every Hilbert vector. -/
theorem adelicCyclicHilbertOperator_norm {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2)
    (v : AdelicCyclicHilbert f) : ‖adelicCyclicHilbertOperator f a v‖ = ‖v‖ := by
  have hi : Isometry (adelicCyclicHilbertOperator f a) :=
    (adelicCyclicRangeIsometry f a).isometry.completion_map
  exact hi.norm_map_of_map_zero (map_zero _) v

/-- The genuine identity group element acts as the identity on the completed original space. -/
theorem adelicCyclicHilbertOperator_one {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : AdelicCyclicHilbert f) :
    adelicCyclicHilbertOperator f 1 v = v := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (adelicCyclicHilbertOperator f 1).continuous continuous_id
  | ih v =>
    rw [adelicCyclicHilbertOperator_coe]
    simp only [map_one, Module.End.one_apply]

/-- The actual completed operators retain the original group multiplication law. -/
theorem adelicCyclicHilbertOperator_mul {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a b : RationalAdelicGL2)
    (v : AdelicCyclicHilbert f) :
    adelicCyclicHilbertOperator f (a * b) v =
      adelicCyclicHilbertOperator f a (adelicCyclicHilbertOperator f b v) := by
  induction v using Completion.induction_on with
  | hp =>
    exact isClosed_eq (adelicCyclicHilbertOperator f (a * b)).continuous
      ((adelicCyclicHilbertOperator f a).continuous.comp
        (adelicCyclicHilbertOperator f b).continuous)
  | ih v =>
    rw [adelicCyclicHilbertOperator_coe, adelicCyclicHilbertOperator_coe,
      adelicCyclicHilbertOperator_coe]
    simp only [map_mul, Module.End.mul_apply]

/-- The actual original cyclic representation on its Hilbert completion. -/
def adelicCyclicHilbertRepresentation {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Representation ℂ RationalAdelicGL2 (AdelicCyclicHilbert f) where
  toFun a := (adelicCyclicHilbertOperator f a).toLinearMap
  map_one' := by ext v; exact adelicCyclicHilbertOperator_one f v
  map_mul' a b := by ext v; exact adelicCyclicHilbertOperator_mul f a b v

/-- The extended original action preserves genuine Hilbert distances. -/
theorem adelicCyclicHilbertOperator_dist {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2)
    (v w : AdelicCyclicHilbert f) :
    dist (adelicCyclicHilbertOperator f a v) (adelicCyclicHilbertOperator f a w) =
      dist v w := by
  rw [dist_eq_norm, ← map_sub]
  exact (adelicCyclicHilbertOperator_norm f a (v - w)).trans (dist_eq_norm v w).symm

/-- Density and actual isometries extend strong continuity to every completed original cusp vector. -/
theorem adelicCyclicHilbertRepresentation_stronglyContinuous {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : AdelicCyclicHilbert f) :
    Continuous (fun a : RationalAdelicGL2 => adelicCyclicHilbertRepresentation f a v) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w, hw⟩ := Completion.denseRange_coe.exists_dist_lt v
    (show 0 < ε / 4 by positivity)
  have hc : Continuous (fun b : RationalAdelicGL2 => adelicCyclicHilbertOperator f b
      (w : Completion (adelicCyclicRange f))) := by
    simpa only [adelicCyclicHilbertOperator_coe] using
      (Completion.continuous_coe (adelicCyclicRange f)).comp
        (adelicCyclicRangeRepresentation_continuous f w)
  have he := Metric.tendsto_nhds.mp (hc.tendsto a) (ε / 2) (by positivity)
  filter_upwards [he] with b hb
  change dist (adelicCyclicHilbertOperator f b v) (adelicCyclicHilbertOperator f a v) < ε
  have ht := dist_triangle (adelicCyclicHilbertOperator f b v)
    (adelicCyclicHilbertOperator f b (w : Completion (adelicCyclicRange f)))
    (adelicCyclicHilbertOperator f a v)
  have ht' := dist_triangle
    (adelicCyclicHilbertOperator f b (w : Completion (adelicCyclicRange f)))
    (adelicCyclicHilbertOperator f a (w : Completion (adelicCyclicRange f)))
    (adelicCyclicHilbertOperator f a v)
  rw [adelicCyclicHilbertOperator_dist] at ht ht'
  rw [dist_comm (w : Completion (adelicCyclicRange f)) v] at ht'
  linarith

/-- The literal original cyclic representation embeds linearly in its actual Hilbert completion. -/
def adelicCyclicHilbertEmbedding {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (adelicLiftCyclicRepresentation N k f).toSubmodule →ₗ[ℂ] AdelicCyclicHilbert f :=
  (Completion.toComplₗᵢ (𝕜 := ℂ) (E := adelicCyclicRange f)).toLinearMap.comp
    (adelicCyclicRangeEquiv f).toLinearMap

/-- No original cusp vector disappears on passage to the actual Hilbert completion. -/
theorem adelicCyclicHilbertEmbedding_injective {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Function.Injective (adelicCyclicHilbertEmbedding f) :=
  (Completion.coe_injective _).comp (adelicCyclicRangeEquiv f).injective

/-- The original cyclic vectors are dense in precisely their constructed Hilbert space. -/
theorem adelicCyclicHilbertEmbedding_dense {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    DenseRange (adelicCyclicHilbertEmbedding f) := by
  change Dense (Set.range (((↑) : adelicCyclicRange f →
    Completion (adelicCyclicRange f)) ∘ adelicCyclicRangeEquiv f))
  rw [Set.range_comp, (adelicCyclicRangeEquiv f).surjective.range_eq, Set.image_univ]
  exact Completion.denseRange_coe

/-- The completed representation intertwines the exact original right-translation representation. -/
theorem adelicCyclicHilbertEmbedding_intertwines {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    adelicCyclicHilbertRepresentation f a (adelicCyclicHilbertEmbedding f v) =
      adelicCyclicHilbertEmbedding f ((adelicLiftCyclicRepresentation N k f).toRepresentation a v) := by
  change adelicCyclicHilbertOperator f a
    ((adelicCyclicRangeEquiv f v) : Completion (adelicCyclicRange f)) = _
  rw [adelicCyclicHilbertOperator_coe, adelicCyclicRangeRepresentation_apply]
  rfl

/-- The completed actual representation is unitary for its genuine Hilbert inner product. -/
theorem adelicCyclicHilbertRepresentation_inner {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2)
    (v w : AdelicCyclicHilbert f) :
    inner ℂ (adelicCyclicHilbertRepresentation f a v) (adelicCyclicHilbertRepresentation f a w) =
      inner ℂ v w := by
  change inner ℂ (adelicCyclicHilbertOperator f a v)
    (adelicCyclicHilbertOperator f a w) = inner ℂ v w
  refine Completion.induction_on₂ v w (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x y
  rw [adelicCyclicHilbertOperator_coe, adelicCyclicHilbertOperator_coe,
    Completion.inner_coe, Completion.inner_coe]
  obtain ⟨u, rfl⟩ := (adelicCyclicRangeEquiv f).surjective x
  obtain ⟨z, rfl⟩ := (adelicCyclicRangeEquiv f).surjective y
  rw [adelicCyclicRangeRepresentation_apply, adelicCyclicRangeRepresentation_apply]
  exact adelicLiftCyclic_inner N f u z a

end
end Dubon2026
