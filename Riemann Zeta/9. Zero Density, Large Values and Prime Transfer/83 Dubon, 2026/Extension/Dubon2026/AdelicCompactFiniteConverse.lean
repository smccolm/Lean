import Dubon2026.AdelicRaisingCompactFinite
import Dubon2026.AdelicRaisingHilbertBasis
import Dubon2026.IrrationalRotationCharacter
import Dubon2026.FiniteUnitaryEigenSpan

/-! # Every genuine compact-finite vector in the original real Hilbert component is a finite raising combination -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Each actual normalized Hilbert basis vector has the original distinct irrational-angle eigenvalue. -/
theorem adelicRaisingHilbertBasis_irrational_rotation (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) :
    adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2)))
      (adelicRaisingHilbertBasis f hf hk n).val =
        irrationalRotationCharacter k n • (adelicRaisingHilbertBasis f hf hk n).val := by
  rw [adelicRaisingHilbertBasis_apply, map_smul, adelicRaisingJet_rotation f hf]
  exact smul_comm _ _ _

/-- The original compact orbit span contains its actual starting vector. -/
theorem adelicCompactOrbitSpan_self (v : AdelicCyclicHilbert f) : v ∈ adelicCompactOrbitSpan f v := by
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, map_one, Module.End.one_apply]

/-- The actual compact orbit span is invariant under every original compact translate. -/
theorem adelicCompactOrbitSpan_invariant (v : AdelicCyclicHilbert f) (g : realCompactSubgroup)
    (w : AdelicCyclicHilbert f) (hw : w ∈ adelicCompactOrbitSpan f v) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g.val) w ∈ adelicCompactOrbitSpan f v :=
  @representationOrbitSpan_invariant realCompactSubgroup ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp (adelicRealSL2Embedding.comp realCompactSubgroup.subtype))
    v g w hw

/-- Every K-finite vector of the actual raising Hilbert closure belongs to its original algebraic raising span. -/
theorem adelicCompactFinite_mem_raisingSpan (hf : f ≠ 0) (hk : 0 < k)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRaisingClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v)] :
    v ∈ Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val)) := by
  let g : realCompactSubgroup :=
    ⟨realRotationCurve (Real.pi * Real.sqrt 2), realRotationCurve_smul_I _⟩
  have hm := @finiteInvariant_mem_hilbert_eigen_span (AdelicCyclicHilbert f) ℕ
    inferInstance inferInstance (adelicRaisingClosedSpan f) (adelicRaisingHilbertBasis f hf hk)
    (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g.val))
    (fun x y => adelicCyclicHilbertRepresentation_inner f _ x y)
    (irrationalRotationCharacter k) (irrationalRotationCharacter_injective k)
    (irrationalRotationCharacter_norm k) (adelicRaisingHilbertBasis_irrational_rotation f hf hk)
    (adelicCompactOrbitSpan f v) inferInstance (adelicCompactOrbitSpan_invariant f v g)
    v hv (adelicCompactOrbitSpan_self f v)
  have hspan : Submodule.span ℂ (Set.range (fun n => (adelicRaisingHilbertBasis f hf hk n).val)) =
      Submodule.span ℂ (Set.range (fun n => (adelicRaisingJet f n).val)) := by
    have he : (fun n => (adelicRaisingHilbertBasis f hf hk n).val) = adelicNormalizedRaisingJet f :=
      funext (adelicRaisingHilbertBasis_apply f hf hk)
    rw [he]
    exact adelicNormalizedRaisingJet_span f hf hk
  exact hspan ▸ hm

end
end Dubon2026
