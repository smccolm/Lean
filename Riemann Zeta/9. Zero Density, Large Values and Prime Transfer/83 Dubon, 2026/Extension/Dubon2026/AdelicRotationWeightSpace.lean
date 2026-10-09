import Dubon2026.AdelicRaisingRotation
import Dubon2026.AdelicRealFiniteCommute
import Dubon2026.UnitaryInvariantProjection
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-! # The actual lowest rotation-character subspace in the full original adelic Hilbert space -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The literal simultaneous eigenspace for every original real rotation and the original cusp weight. -/
def adelicRotationWeightSpace : Submodule ℂ (AdelicCyclicHilbert f) :=
  ⨅ t : ℝ, Module.End.eigenspace (adelicCyclicHilbertOperator f (adelicRealSL2Embedding (realRotationCurve t))).toLinearMap
    (Complex.exp ((t : ℂ) * (Complex.I * (k : ℂ))))

/-- Membership means exactly the original rotation-character equation at every real angle. -/
theorem mem_adelicRotationWeightSpace (v : AdelicCyclicHilbert f) :
    v ∈ adelicRotationWeightSpace f ↔ ∀ t : ℝ,
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t)) v =
        Complex.exp ((t : ℂ) * (Complex.I * (k : ℂ))) • v := by
  simp only [adelicRotationWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  rfl

/-- The genuine simultaneous rotation-character subspace is closed in the actual Hilbert norm. -/
theorem adelicRotationWeightSpace_isClosed :
    IsClosed (adelicRotationWeightSpace f : Set (AdelicCyclicHilbert f)) := by
  unfold adelicRotationWeightSpace
  rw [Submodule.coe_iInf]
  exact isClosed_iInter (fun t => ContinuousLinearMap.isClosed_eigenspace _ _)

/-- The actual closed rotation-character space has its original complete inherited metric. -/
instance adelicRotationWeightSpace_complete : CompleteSpace (adelicRotationWeightSpace f) :=
  (adelicRotationWeightSpace_isClosed f).isComplete.completeSpace_coe

/-- The original cusp generator lies in its literal original compact weight space. -/
theorem adelicCyclicHilbertGenerator_mem_rotationWeight (hf : f ≠ 0) :
    adelicCyclicHilbertGenerator f ∈ adelicRotationWeightSpace f := by
  rw [mem_adelicRotationWeightSpace]
  intro t
  simpa only [Nat.cast_zero, mul_zero, add_zero] using adelicRaisingJet_rotation f hf 0 t

/-- Every original finite-adelic operator preserves the actual full rotation-character subspace. -/
theorem adelicRotationWeightSpace_finite_invariant
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : AdelicCyclicHilbert f)
    (hv : v ∈ adelicRotationWeightSpace f) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) v ∈ adelicRotationWeightSpace f := by
  rw [mem_adelicRotationWeightSpace] at hv ⊢
  intro t
  rw [adelicCyclicHilbert_real_finite_commute, hv, map_smul]

/-- The genuine orthogonal projector onto the original lowest rotation-character subspace. -/
def adelicRotationWeightProjection : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  @Submodule.starProjection ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicRotationWeightSpace f) inferInstance

/-- The actual projector fixes the original cusp generator. -/
theorem adelicRotationWeightProjection_generator (hf : f ≠ 0) :
    adelicRotationWeightProjection f (adelicCyclicHilbertGenerator f) = adelicCyclicHilbertGenerator f :=
  (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicRotationWeightSpace f) inferInstance (adelicCyclicHilbertGenerator f)).mpr
      (adelicCyclicHilbertGenerator_mem_rotationWeight f hf)

/-- The original lowest-weight projector commutes with the genuine full finite-adelic action. -/
theorem adelicRotationWeightProjection_finite
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : AdelicCyclicHilbert f) :
    adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) v) =
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
      (adelicRotationWeightProjection f v) := by
  exact @unitary_invariant_starProjection (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (fun a v w => adelicCyclicHilbertRepresentation_inner f (rationalAdelicFiniteGL2Embedding a) v w)
    (adelicRotationWeightSpace f) inferInstance (adelicRotationWeightSpace_finite_invariant f) a v

end
end Dubon2026
