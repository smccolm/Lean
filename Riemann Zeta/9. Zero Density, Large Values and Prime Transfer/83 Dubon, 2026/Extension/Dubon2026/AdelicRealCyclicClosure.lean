import Dubon2026.RealClosedCyclicSubspace
import Dubon2026.AdelicGlobalRaisingClosure

/-! # Equality of the original real cyclic Hilbert space and original raising closure -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The literal closed span of the original real-group translates of the original cusp generator. -/
def adelicRealCyclicClosedSpan : Submodule ℂ (AdelicCyclicHilbert f) :=
  (Submodule.span ℂ (Set.range (fun g : SL(2, ℝ) =>
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g)
      (adelicCyclicHilbertGenerator f)))).topologicalClosure

/-- The genuine original real cyclic span is closed in its original Hilbert topology. -/
theorem adelicRealCyclicClosedSpan_isClosed :
    IsClosed (adelicRealCyclicClosedSpan f : Set (AdelicCyclicHilbert f)) :=
  Submodule.isClosed_topologicalClosure _

/-- Every original real translate belongs to the genuine original real cyclic closure. -/
theorem adelicRealCyclicClosedSpan_orbit_mem (g : SL(2, ℝ)) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g)
      (adelicCyclicHilbertGenerator f) ∈ adelicRealCyclicClosedSpan f :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, rfl⟩)

/-- The actual closed real cyclic span is invariant under the original real group action. -/
theorem adelicRealCyclicClosedSpan_invariant (g : SL(2, ℝ)) (v : AdelicCyclicHilbert f)
    (hv : v ∈ adelicRealCyclicClosedSpan f) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v ∈ adelicRealCyclicClosedSpan f :=
  @closedCyclicSpan_invariant SL(2, ℝ) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)) (fun _ _ => rfl)
    (adelicCyclicHilbertGenerator f) g v hv

/-- Every original smooth-curve infinitesimal preserves genuine real cyclic membership on the original smooth domain. -/
theorem adelicRealCyclicClosedSpan_infinitesimal (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (v : adelicRealSmoothSubmodule f) (hv : v.val ∈ adelicRealCyclicClosedSpan f) :
    (adelicSmoothInfinitesimal f c hc v).val ∈ adelicRealCyclicClosedSpan f := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothInfinitesimal_mem_closedInvariant (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) (adelicRealCyclicClosedSpan f) (adelicRealCyclicClosedSpan_isClosed f)
    (adelicRealCyclicClosedSpan_invariant f) c hc v hv

/-- Every genuine complex matrix Lie action preserves the original real cyclic closure on its original smooth domain. -/
theorem adelicRealCyclicClosedSpan_matrix (x : ComplexSl2) (v : adelicRealSmoothSubmodule f)
    (hv : v.val ∈ adelicRealCyclicClosedSpan f) :
    (adelicComplexSl2Action f x v).val ∈ adelicRealCyclicClosedSpan f := by
  change (2 * x.val 0 0) • (adelicSmoothInfinitesimal f realGeodesicCurve
      realGeodesicCurve_entries_contDiff v).val +
    x.val 0 1 • (adelicSmoothInfinitesimal f realUpperUnipotent
      realUpperUnipotent_entries_contDiff v).val +
    x.val 1 0 • (adelicSmoothInfinitesimal f realLowerUnipotent
      realLowerUnipotent_entries_contDiff v).val ∈ adelicRealCyclicClosedSpan f
  exact (adelicRealCyclicClosedSpan f).add_mem
    ((adelicRealCyclicClosedSpan f).add_mem
      ((adelicRealCyclicClosedSpan f).smul_mem _ (adelicRealCyclicClosedSpan_infinitesimal f
        realGeodesicCurve realGeodesicCurve_entries_contDiff v hv))
      ((adelicRealCyclicClosedSpan f).smul_mem _ (adelicRealCyclicClosedSpan_infinitesimal f
        realUpperUnipotent realUpperUnipotent_entries_contDiff v hv)))
    ((adelicRealCyclicClosedSpan f).smul_mem _ (adelicRealCyclicClosedSpan_infinitesimal f
      realLowerUnipotent realLowerUnipotent_entries_contDiff v hv))

/-- Each original raising derivative belongs to the original real cyclic closure. -/
theorem adelicRaisingJet_mem_realCyclicClosedSpan (n : ℕ) :
    (adelicRaisingJet f n).val ∈ adelicRealCyclicClosedSpan f := by
  induction n with
  | zero =>
      simpa only [map_one, Module.End.one_apply] using adelicRealCyclicClosedSpan_orbit_mem f 1
  | succ n ih =>
      exact (congrArg Subtype.val (adelicRaisingJet_raise f n)) ▸
        (adelicRealCyclicClosedSpan_matrix f compactSl2E (adelicRaisingJet f n) ih)

/-- The original raising Hilbert closure is exactly the original closed real cyclic representation. -/
theorem adelicRaisingClosedSpan_eq_realCyclicClosedSpan (hf : f ≠ 0) :
    adelicRaisingClosedSpan f = adelicRealCyclicClosedSpan f := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact adelicRaisingJet_mem_realCyclicClosedSpan f n
    · exact adelicRealCyclicClosedSpan_isClosed f
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      exact adelicCyclicHilbertGenerator_real_mem_closedSpan f hf g
    · exact Submodule.isClosed_topologicalClosure _

/-- The original raising Hilbert closure is invariant under the entire genuine real group action. -/
theorem adelicRaisingClosedSpan_real_invariant (hf : f ≠ 0) (g : SL(2, ℝ))
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRaisingClosedSpan f) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v ∈ adelicRaisingClosedSpan f := by
  rw [adelicRaisingClosedSpan_eq_realCyclicClosedSpan f hf] at hv ⊢
  exact adelicRealCyclicClosedSpan_invariant f g v hv

end
end Dubon2026
