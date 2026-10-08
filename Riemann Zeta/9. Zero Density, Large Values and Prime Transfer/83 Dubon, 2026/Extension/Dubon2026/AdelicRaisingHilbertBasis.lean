import Dubon2026.AdelicRaisingHilbertNorms
import Dubon2026.OrthogonalClosureBasis

/-! # The actual normalized Hilbert basis of the original raising closure -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The closed span of the original raising derivatives inside the original completed adelic Hilbert space. -/
def adelicRaisingClosedSpan : Submodule ℂ (AdelicCyclicHilbert f) :=
  (Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val))).topologicalClosure

/-- The original raising closure is complete with its original inherited norm. -/
instance adelicRaisingClosedSpan_complete : CompleteSpace (adelicRaisingClosedSpan f) := by
  unfold adelicRaisingClosedSpan
  infer_instance

/-- The original closed raising span carries exactly the inner product of its ambient adelic Hilbert space. -/
instance adelicRaisingClosedSpanInnerProductSpace : InnerProductSpace ℂ (adelicRaisingClosedSpan f) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicRaisingClosedSpan f)

/-- Every actual raising derivative belongs to its original Hilbert closure. -/
theorem adelicRaisingJet_mem_closedSpan (n : ℕ) :
    (adelicRaisingJet f n).val ∈ adelicRaisingClosedSpan f :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

/-- The original raising derivatives remain nonzero under their actual Hilbert inclusion. -/
theorem adelicRaisingJet_val_ne_zero (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) :
    (adelicRaisingJet f n).val ≠ 0 := fun h => adelicRaisingJet_ne_zero f hf hk n (Subtype.ext h)

/-- The original Hilbert raising derivatives normalized by their actual Hilbert norms. -/
def adelicNormalizedRaisingJet (n : ℕ) : AdelicCyclicHilbert f :=
  ((‖(adelicRaisingJet f n).val‖⁻¹ : ℝ) : ℂ) • (adelicRaisingJet f n).val

/-- The actual normalized original raising derivatives are orthonormal in the original adelic Hilbert space. -/
theorem adelicNormalizedRaisingJet_orthonormal (hf : f ≠ 0) (hk : 0 < k) :
    Orthonormal ℂ (adelicNormalizedRaisingJet f) :=
  @normalizedOrthogonal_orthonormal (AdelicCyclicHilbert f) ℕ inferInstance inferInstance
    (fun n => (adelicRaisingJet f n).val) (adelicRaisingJet_val_ne_zero f hf hk)
    (fun m n hmn => adelicRaisingJet_inner_zero f hf m n hmn)

/-- Actual normalization preserves precisely the original algebraic Hilbert span. -/
theorem adelicNormalizedRaisingJet_span (hf : f ≠ 0) (hk : 0 < k) :
    Submodule.span ℂ (Set.range (adelicNormalizedRaisingJet f)) =
      Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val)) :=
  @normalizedOrthogonal_span (AdelicCyclicHilbert f) ℕ inferInstance inferInstance
    (fun n => (adelicRaisingJet f n).val) (adelicRaisingJet_val_ne_zero f hf hk)

/-- The original normalized raising derivatives form a genuine Hilbert basis of exactly their original closed span. -/
def adelicRaisingHilbertBasis (hf : f ≠ 0) (hk : 0 < k) :
    HilbertBasis ℕ ℂ (adelicRaisingClosedSpan f) :=
  orthonormalClosureBasis (adelicNormalizedRaisingJet f)
    (adelicNormalizedRaisingJet_orthonormal f hf hk) (adelicRaisingClosedSpan f)
    (congrArg Submodule.topologicalClosure (adelicNormalizedRaisingJet_span f hf hk)).symm

/-- The actual Hilbert basis vectors are exactly the normalized original Hilbert derivatives. -/
theorem adelicRaisingHilbertBasis_apply (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) :
    (adelicRaisingHilbertBasis f hf hk n).val =
      ((‖(adelicRaisingJet f n).val‖⁻¹ : ℝ) : ℂ) • (adelicRaisingJet f n).val :=
  orthonormalClosureBasis_apply (adelicNormalizedRaisingJet f)
    (adelicNormalizedRaisingJet_orthonormal f hf hk) (adelicRaisingClosedSpan f) _ n

/-- A vector in the original raising closure orthogonal to all original raising derivatives is zero. -/
theorem adelicRaisingClosedSpan_eq_zero_of_inner (v : AdelicCyclicHilbert f)
    (hv : v ∈ adelicRaisingClosedSpan f) (hi : ∀ n, inner ℂ (adelicRaisingJet f n).val v = 0) :
    v = 0 :=
  @closureSpan_eq_zero_of_inner (AdelicCyclicHilbert f) ℕ inferInstance inferInstance
    (fun n => (adelicRaisingJet f n).val) v hv hi

end
end Dubon2026
