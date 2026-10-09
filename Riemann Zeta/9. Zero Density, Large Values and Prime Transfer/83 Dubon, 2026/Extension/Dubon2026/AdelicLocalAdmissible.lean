import Dubon2026.AdelicLocalSmoothCompletion
import Dubon2026.AdelicLocalSmoothRepresentation

/-! # Admissibility of the actual original smooth local representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Invariants of the genuine restricted smooth local representation are finite dimensional for every actual open subgroup: the admissibility conclusion for the original source representation. -/
theorem adelicLocalSmoothRepresentation_admissible (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    FiniteDimensional ℂ (Representation.invariants ((adelicLocalSmoothRepresentation f v).comp J.subtype)) := by
  letI := adelicLocalCyclic_open_fixed_finiteDimensional f hf hk v J hJ
  let T : Representation.invariants ((adelicLocalSmoothRepresentation f v).comp J.subtype) →ₗ[ℂ]
      (adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v J :
        Submodule ℂ (AdelicCyclicHilbert f)) := {
    toFun := fun x => ⟨x.val.val, ⟨Submodule.le_topologicalClosure _ x.val.property,
      fun g => congrArg Subtype.val (x.property g)⟩⟩
    map_add' := fun _ _ => Subtype.ext rfl
    map_smul' := fun _ _ => Subtype.ext rfl }
  have hT : Function.Injective T := by
    intro x y he
    have h := congrArg Subtype.val he
    exact Subtype.ext (Subtype.ext h)
  exact FiniteDimensional.of_injective T hT

/-- The full genuine local cyclic Hilbert representation has finite-dimensional fixed vectors at every original open local subgroup. -/
theorem adelicLocalCyclicRepresentation_admissible (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    FiniteDimensional ℂ (Representation.invariants ((adelicLocalCyclicRepresentation f v).comp J.subtype)) := by
  letI := adelicLocalCyclic_open_fixed_finiteDimensional f hf hk v J hJ
  let T : Representation.invariants ((adelicLocalCyclicRepresentation f v).comp J.subtype) →ₗ[ℂ]
      (adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v J :
        Submodule ℂ (AdelicCyclicHilbert f)) := {
    toFun := fun x => ⟨x.val.val, ⟨x.val.property, fun g => congrArg Subtype.val (x.property g)⟩⟩
    map_add' := fun _ _ => Subtype.ext rfl
    map_smul' := fun _ _ => Subtype.ext rfl }
  have hT : Function.Injective T := by
    intro x y he
    have h := congrArg Subtype.val he
    exact Subtype.ext (Subtype.ext h)
  exact FiniteDimensional.of_injective T hT

end
end Dubon2026
