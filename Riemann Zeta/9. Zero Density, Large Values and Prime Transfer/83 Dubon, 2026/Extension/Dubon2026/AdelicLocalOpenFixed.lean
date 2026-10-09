import Dubon2026.AdelicLocalAwayFixed

/-! # Genuine local open-subgroup fixed spaces and their original global sublevel realization -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Actual Hilbert vectors fixed by a specified genuine subgroup of the original local group. -/
def adelicLocalSubgroupFixedSpace (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :
    Submodule ℂ (AdelicCyclicHilbert f) :=
  Representation.invariants ((adelicCyclicLocalRepresentation f v).comp J.subtype)

/-- The literal fixed equations characterize the genuine local subgroup fixed space. -/
theorem mem_adelicLocalSubgroupFixedSpace (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) (x : AdelicCyclicHilbert f) :
    x ∈ adelicLocalSubgroupFixedSpace f v J ↔
      ∀ g : J, adelicCyclicLocalRepresentation f v g.val x = x := Iff.rfl

/-- The genuine local subgroup fixed space is closed in the original Hilbert topology. -/
theorem adelicLocalSubgroupFixedSpace_isClosed (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :
    IsClosed (adelicLocalSubgroupFixedSpace f v J : Set (AdelicCyclicHilbert f)) :=
  @representation_invariants_isClosed J (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance ((adelicCyclicLocalRepresentation f v).comp J.subtype)
    (fun g => adelicCyclicLocalOperator f v g.val) (fun _ _ => rfl)

/-- The actual local subgroup fixed space is complete. -/
instance adelicLocalSubgroupFixedSpace_complete (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :
    CompleteSpace (adelicLocalSubgroupFixedSpace f v J) :=
  (adelicLocalSubgroupFixedSpace_isClosed f v J).isComplete.completeSpace_coe

/-- Every actual locally fixed cyclic vector is an original lowest-weight vector fixed by the genuine pulled-back global sublevel. -/
theorem adelicLocalCyclic_fixed_le_sublevel (hf : f ≠ 0) (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :
    adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v J ≤
      adelicRotationWeightSpace f ⊓ adelicSublevelFixedSpace f (finiteAdelicPlaceSublevel N v J) := by
  rintro x ⟨hx, hJx⟩
  refine ⟨adelicFiniteCyclicClosedSpan_le_weight f hf (adelicLocalCyclicClosedSpan_le_finite f v hx), ?_⟩
  apply (mem_adelicSublevelFixedSpace f _ x).mpr
  intro a
  rw [adelicLocalCyclic_level_action f v a.val x hx]
  exact (mem_adelicLocalSubgroupFixedSpace f v J x).mp hJx
    ⟨GeneralLinearGroup.map (finiteAdelePlace v) a.val.val, a.property⟩

/-- The actual locally fixed part of the genuine cyclic Hilbert space is finite dimensional for every open subgroup of the original local group. -/
theorem adelicLocalCyclic_open_fixed_finiteDimensional (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    FiniteDimensional ℂ ↥(adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v J :
      Submodule ℂ (AdelicCyclicHilbert f)) := by
  letI := adelicSublevelFixedLowest_finiteDimensional f hf hk (finiteAdelicPlaceSublevel N v J)
    (finiteAdelicPlaceSublevel_isOpen N v J hJ)
  have h := adelicLocalCyclic_fixed_le_sublevel f hf v J
  let T : (adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v J :
      Submodule ℂ (AdelicCyclicHilbert f)) →ₗ[ℂ]
      (adelicRotationWeightSpace f ⊓ adelicSublevelFixedSpace f (finiteAdelicPlaceSublevel N v J) :
        Submodule ℂ (AdelicCyclicHilbert f)) := Submodule.inclusion h
  have hT : Function.Injective T := Submodule.inclusion_injective h
  exact FiniteDimensional.of_injective T hT

end
end Dubon2026
