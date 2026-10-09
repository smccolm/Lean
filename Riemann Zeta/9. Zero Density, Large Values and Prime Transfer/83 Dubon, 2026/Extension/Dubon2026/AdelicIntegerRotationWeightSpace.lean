import Dubon2026.AdelicSignedRaisingFamily

/-! # Actual integer rotation-character spaces and projections in the original full adelic Hilbert space -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The simultaneous eigenspace for the actual integer character at every original rotation angle. -/
def adelicIntegerRotationWeightSpace (m : ℤ) : Submodule ℂ (AdelicCyclicHilbert f) :=
  ⨅ t : ℝ, Module.End.eigenspace
    (adelicCyclicHilbertOperator f (adelicRealSL2Embedding (realRotationCurve t))).toLinearMap
    (Complex.exp ((t : ℂ) * (Complex.I * (m : ℂ))))

/-- Membership means the exact original integer-character equation at every real angle. -/
theorem mem_adelicIntegerRotationWeightSpace (m : ℤ) (x : AdelicCyclicHilbert f) :
    x ∈ adelicIntegerRotationWeightSpace f m ↔ ∀ t : ℝ,
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t)) x =
        Complex.exp ((t : ℂ) * (Complex.I * (m : ℂ))) • x := by
  simp only [adelicIntegerRotationWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  rfl

/-- Every original simultaneous integer-character space is closed in the actual Hilbert norm. -/
theorem adelicIntegerRotationWeightSpace_isClosed (m : ℤ) :
    IsClosed (adelicIntegerRotationWeightSpace f m : Set (AdelicCyclicHilbert f)) := by
  unfold adelicIntegerRotationWeightSpace
  rw [Submodule.coe_iInf]
  exact isClosed_iInter (fun t => ContinuousLinearMap.isClosed_eigenspace _ _)

/-- Every actual integer-character space has its original complete inherited norm. -/
instance adelicIntegerRotationWeightSpace_complete (m : ℤ) : CompleteSpace (adelicIntegerRotationWeightSpace f m) :=
  (adelicIntegerRotationWeightSpace_isClosed f m).isComplete.completeSpace_coe

/-- Each original signed raising vector belongs to its precise original simultaneous character space. -/
theorem adelicSignedRaisingJet_mem_integerWeight (hf : f ≠ 0) (i : ℕ ⊕ ℕ) :
    adelicSignedRaisingJet f i ∈ adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) :=
  (mem_adelicIntegerRotationWeightSpace f _ _).mpr (adelicSignedRaisingJet_rotation_all f hf i)

/-- The genuine full finite-adelic action preserves each original real integer-character space. -/
theorem adelicIntegerRotationWeightSpace_finite_invariant (m : ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : AdelicCyclicHilbert f)
    (hx : x ∈ adelicIntegerRotationWeightSpace f m) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) x ∈
      adelicIntegerRotationWeightSpace f m := by
  rw [mem_adelicIntegerRotationWeightSpace] at hx ⊢
  intro t
  rw [adelicCyclicHilbert_real_finite_commute, hx, map_smul]

/-- The genuine original orthogonal projector onto a full adelic integer-character space. -/
def adelicIntegerRotationWeightProjection (m : ℤ) : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  @Submodule.starProjection ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicIntegerRotationWeightSpace f m) inferInstance

/-- The actual projector fixes the matching original signed raising vector. -/
theorem adelicIntegerRotationWeightProjection_signed (hf : f ≠ 0) (i : ℕ ⊕ ℕ) :
    adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i) (adelicSignedRaisingJet f i) =
      adelicSignedRaisingJet f i :=
  (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicIntegerRotationWeightSpace f _) inferInstance _).mpr (adelicSignedRaisingJet_mem_integerWeight f hf i)

/-- The actual character projector commutes with every genuine finite-adelic operator. -/
theorem adelicIntegerRotationWeightProjection_finite (m : ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : AdelicCyclicHilbert f) :
    adelicIntegerRotationWeightProjection f m
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) x) =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicIntegerRotationWeightProjection f m x) :=
  @unitary_invariant_starProjection (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (fun a x y => adelicCyclicHilbertRepresentation_inner f (rationalAdelicFiniteGL2Embedding a) x y)
    (adelicIntegerRotationWeightSpace f m) inferInstance (adelicIntegerRotationWeightSpace_finite_invariant f m) a x

/-- Distinct original signed weights are annihilated by the genuine global integer-character projector. -/
theorem adelicIntegerRotationWeightProjection_other (hf : f ≠ 0) (m : ℤ) (i : ℕ ⊕ ℕ)
    (hmi : m ≠ adelicSignedRaisingWeight k i) :
    adelicIntegerRotationWeightProjection f m (adelicSignedRaisingJet f i) = 0 := by
  have ho : adelicSignedRaisingJet f i ∈
      (@Submodule.orthogonal ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
        (adelicIntegerRotationWeightSpace f m)) := by
    intro x hx
    have he := (mem_adelicIntegerRotationWeightSpace f m x).mp hx (Real.pi * Real.sqrt 2)
    exact @unitary_distinct_eigen_inner_zero (AdelicCyclicHilbert f) inferInstance inferInstance
      (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))))
      (adelicCyclicHilbertRepresentation_inner f _) x _ _ _ (integerIrrationalCharacter_norm m)
      (integerIrrationalCharacter_injective.ne hmi) he (adelicSignedRaisingJet_rotation f hf i)
  exact congrArg Subtype.val ((@Submodule.orthogonalProjection_eq_zero_iff ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicIntegerRotationWeightSpace f m) inferInstance _).mpr ho)

end
end Dubon2026
