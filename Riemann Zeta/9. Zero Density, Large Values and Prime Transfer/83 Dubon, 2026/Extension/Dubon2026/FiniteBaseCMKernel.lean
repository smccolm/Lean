import Dubon2026.FiniteBaseCMGroupExtension

/-! The actual component kernel is the original Galois group over the CM
field, with both original Krull topologies. These identifications supply
the genuine domain of the residual representation required in DUB-17. -/

namespace Dubon2026
open NumberField Algebra
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the CM kernel identification. -/
local instance finiteBaseCMKernelUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K]

/-- The arithmetic component kernel is exactly the original CM fixing subgroup. -/
def finiteBaseCMKernelFixingEquiv : FiniteBaseCMKernel a F K ≃* K.fixingSubgroup where
  toFun g := ⟨finiteBaseArithmeticGaloisEquiv a F g.val, by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (finiteBaseQuadraticComponent_eq_one_iff a F K g.val).mp g.property ⟨x, hx⟩⟩
  invFun g := ⟨(finiteBaseArithmeticGaloisEquiv a F).symm g.val, by
    apply (finiteBaseQuadraticComponent_eq_one_iff a F K _).mpr
    intro x
    rw [(finiteBaseArithmeticGaloisEquiv a F).apply_symm_apply]
    have hfix := g.property
    rw [IntermediateField.mem_fixingSubgroup_iff] at hfix
    exact hfix x x.property⟩
  left_inv g := Subtype.ext ((finiteBaseArithmeticGaloisEquiv a F).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((finiteBaseArithmeticGaloisEquiv a F).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((finiteBaseArithmeticGaloisEquiv a F).map_mul g.val h.val)

/-- The original component-kernel identification is continuous. -/
theorem finiteBaseCMKernelFixingEquiv_continuous :
    Continuous (finiteBaseCMKernelFixingEquiv a F K) :=
  ((finiteBaseArithmeticGaloisEquiv_continuous a F).comp continuous_subtype_val).subtype_mk _

/-- Its inverse is continuous in the original arithmetic topology. -/
theorem finiteBaseCMKernelFixingEquiv_symm_continuous :
    Continuous (finiteBaseCMKernelFixingEquiv a F K).symm :=
  ((finiteBaseArithmeticGaloisEquiv_symm_continuous a F).comp continuous_subtype_val).subtype_mk _

/-- The actual arithmetic component kernel is the Galois group over the original CM field. -/
def finiteBaseCMKernelGaloisEquiv :
    FiniteBaseCMKernel a F K ≃* Gal(rationalUnramifiedExtension a / K) :=
  (finiteBaseCMKernelFixingEquiv a F K).trans (IntermediateField.fixingSubgroupEquiv K)

/-- The CM Galois identification preserves the original Krull topology. -/
theorem finiteBaseCMKernelGaloisEquiv_continuous :
    Continuous (finiteBaseCMKernelGaloisEquiv a F K) :=
  (finiteBase_fixingSubgroupEquiv_continuous K).comp
    (finiteBaseCMKernelFixingEquiv_continuous a F K)

/-- The inverse CM Galois identification preserves the original Krull topology. -/
theorem finiteBaseCMKernelGaloisEquiv_symm_continuous :
    Continuous (finiteBaseCMKernelGaloisEquiv a F K).symm := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  exact (finiteBaseCMKernelFixingEquiv_symm_continuous a F K).comp
    (finiteBase_fixingSubgroupEquiv_symm_continuous K)

end
end Dubon2026
