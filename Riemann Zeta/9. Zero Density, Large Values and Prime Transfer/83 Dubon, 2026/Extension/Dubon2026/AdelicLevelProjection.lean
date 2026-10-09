import Dubon2026.AdelicFiniteLowestClosure
import Dubon2026.ClosedRepresentationInvariants
import Dubon2026.InvariantProjectionPreservation

/-! # The genuine finite-level fixed-vector projector in the original full adelic Hilbert space -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Restrict the original full adelic action to its actual finite level subgroup. -/
def adelicFiniteLevelRepresentation : Representation ℂ (finiteAdeleGL2Gamma0 N) (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp
    (rationalAdelicFiniteGL2Embedding.comp (finiteAdeleGL2Gamma0 N).subtype)

/-- The actual full Hilbert subspace fixed by the original finite level subgroup. -/
def adelicLevelFixedSpace : Submodule ℂ (AdelicCyclicHilbert f) :=
  (adelicFiniteLevelRepresentation f).invariants

/-- Original finite-level invariance is precisely the literal fixed-vector equation for each actual level element. -/
theorem mem_adelicLevelFixedSpace (v : AdelicCyclicHilbert f) :
    v ∈ adelicLevelFixedSpace f ↔ ∀ a : finiteAdeleGL2Gamma0 N,
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val) v = v := Iff.rfl

/-- The original finite-level fixed-vector subspace is genuinely closed. -/
theorem adelicLevelFixedSpace_isClosed : IsClosed (adelicLevelFixedSpace f : Set (AdelicCyclicHilbert f)) :=
  @representation_invariants_isClosed (finiteAdeleGL2Gamma0 N) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicFiniteLevelRepresentation f)
    (fun a => adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a.val)) (fun _ _ => rfl)

/-- The original fixed-level subspace is complete in its actual inherited Hilbert norm. -/
instance adelicLevelFixedSpace_complete : CompleteSpace (adelicLevelFixedSpace f) :=
  (adelicLevelFixedSpace_isClosed f).isComplete.completeSpace_coe

/-- The actual orthogonal projector onto the genuine finite-level fixed-vector subspace. -/
def adelicLevelProjection : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  @Submodule.starProjection ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicLevelFixedSpace f) inferInstance

/-- The genuine original cusp generator is fixed by the actual finite-level projector. -/
theorem adelicLevelProjection_generator :
    adelicLevelProjection f (adelicCyclicHilbertGenerator f) = adelicCyclicHilbertGenerator f :=
  (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicLevelFixedSpace f) inferInstance (adelicCyclicHilbertGenerator f)).mpr
      (adelicCyclicHilbertGenerator_finite_level f)

/-- The actual level projector preserves the full original lowest rotation-character space. -/
theorem adelicLevelProjection_mem_rotationWeight (v : AdelicCyclicHilbert f)
    (hv : v ∈ adelicRotationWeightSpace f) : adelicLevelProjection f v ∈ adelicRotationWeightSpace f := by
  have hproj : @Submodule.HasOrthogonalProjection ℂ (AdelicCyclicHilbert f)
      inferInstance inferInstance inferInstance (adelicLevelFixedSpace f) := inferInstance
  exact @invariantProjection_mem_invariant_submodule (AdelicCyclicHilbert f) inferInstance inferInstance
    (finiteAdeleGL2Gamma0 N) inferInstance (adelicFiniteLevelRepresentation f)
    (fun a v w => adelicCyclicHilbertRepresentation_inner f (rationalAdelicFiniteGL2Embedding a.val) v w)
    (adelicRotationWeightSpace f) inferInstance hproj
    (fun a v hv => adelicRotationWeightSpace_finite_invariant f a.val v hv) v hv

end
end Dubon2026
