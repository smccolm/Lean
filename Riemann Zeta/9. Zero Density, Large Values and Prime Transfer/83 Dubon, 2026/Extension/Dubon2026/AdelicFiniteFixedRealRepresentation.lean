import Dubon2026.AdelicIrrationalRotationSpectrum

/-! # The original full real action on actual open-finite-subgroup fixed vectors -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))

/-- Every genuine real operator preserves the original vectors fixed by the actual finite adelic subgroup. -/
theorem adelicFiniteSubgroupFixedSpace_real_invariant (g : GeneralLinearGroup (Fin 2) ℝ)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicFiniteSubgroupFixedSpace f J) :
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) x ∈ adelicFiniteSubgroupFixedSpace f J := by
  intro a
  have he := congrArg (fun b => adelicCyclicHilbertRepresentation f b x)
    (adelicRealGL2_finite_commute g a.val).eq
  simp only [map_mul, Module.End.mul_apply] at he
  exact he.symm.trans (congrArg (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g)) (hx a))

/-- The full genuine real representation on the original finite-subgroup fixed Hilbert space. -/
def adelicFiniteFixedRealRepresentation :
    Representation ℂ (GeneralLinearGroup (Fin 2) ℝ) (adelicFiniteSubgroupFixedSpace f J) :=
  Representation.subrepresentation ((adelicCyclicHilbertRepresentation f).comp adelicRealGL2Embedding)
    (adelicFiniteSubgroupFixedSpace f J) (adelicFiniteSubgroupFixedSpace_real_invariant f J)

/-- Its separating real rotation has finite-dimensional eigenspaces for every complex scalar, at every actual open finite adelic subgroup. -/
theorem adelicFiniteFixedRealRepresentation_eigenspace_finiteDimensional
    (hf : f ≠ 0) (hk : 0 < k)
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) (c : ℂ) :
    FiniteDimensional ℂ (Module.End.eigenspace
      (adelicFiniteFixedRealRepresentation f J (toGL (realRotationCurve (Real.pi * Real.sqrt 2)))) c) := by
  letI := adelicIrrationalRotation_fixed_eigenspace_finiteDimensional f hf hk J hJ c
  let L : Module.End.eigenspace
      (adelicFiniteFixedRealRepresentation f J (toGL (realRotationCurve (Real.pi * Real.sqrt 2)))) c →ₗ[ℂ]
      (Module.End.eigenspace (adelicIrrationalRotation f) c ⊓ adelicFiniteSubgroupFixedSpace f J :
        Submodule ℂ (AdelicCyclicHilbert f)) :=
    { toFun := fun x => ⟨x.val.val, ⟨Module.End.mem_eigenspace_iff.mpr
          (congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp x.property)), x.val.property⟩⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  apply FiniteDimensional.of_injective L
  intro x y h
  have he := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext he)

end
end Dubon2026
