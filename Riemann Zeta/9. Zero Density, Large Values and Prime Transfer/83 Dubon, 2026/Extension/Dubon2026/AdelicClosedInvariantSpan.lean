import Dubon2026.AdelicClosedSpanSchur
import Dubon2026.UnitaryInvariantProjection
import Dubon2026.ScalarProjectionSubspace

/-! # Closed original real-invariant subspaces inside the original raising closure -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- A genuine closed real-invariant subspace contained in the original raising closure is zero or that entire original closure. -/
theorem adelicRaisingClosedSpan_invariant_eq_bot_or_eq (hf : f ≠ 0) (hk : 0 < k)
    (p : Submodule ℂ (AdelicCyclicHilbert f)) (hclosed : IsClosed (p : Set (AdelicCyclicHilbert f)))
    (hpq : p ≤ adelicRaisingClosedSpan f)
    (hp : ∀ g : SL(2, ℝ), ∀ v ∈ p,
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v ∈ p) :
    p = ⊥ ∨ p = adelicRaisingClosedSpan f := by
  letI : CompleteSpace p := hclosed.isComplete.completeSpace_coe
  let T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
    @Submodule.starProjection ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance p
      inferInstance
  have hT : ∀ g : SL(2, ℝ), ∀ v,
      T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
        adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v) := by
    intro g v
    exact @unitary_invariant_starProjection SL(2, ℝ) (AdelicCyclicHilbert f)
      inferInstance inferInstance inferInstance
      ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
      (fun g v w => adelicCyclicHilbertRepresentation_inner f (adelicRealSL2Embedding g) v w)
      p inferInstance hp g v
  have hs := adelicIntertwiner_closedSpan_scalar f hf hk T hT
    (hpq (@Submodule.starProjection_apply_mem ℂ (AdelicCyclicHilbert f)
      inferInstance inferInstance inferInstance p inferInstance (adelicCyclicHilbertGenerator f)))
  exact @scalarProjection_eq_bot_or_eq (AdelicCyclicHilbert f) inferInstance inferInstance
    p (adelicRaisingClosedSpan f) inferInstance hpq
    (adelicCyclicHilbertGenerator f) (adelicRaisingJet_mem_closedSpan f 0)
    (adelicCyclicHilbertGenerator_ne_zero f hf) hs

end
end Dubon2026
