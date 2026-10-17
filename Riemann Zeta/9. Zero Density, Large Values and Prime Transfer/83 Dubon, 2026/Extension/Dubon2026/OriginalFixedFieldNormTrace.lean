import Dubon2026.OriginalFullClassNormQuotientComparison
import Dubon2026.OriginalIdeleClassNormalInvariants
import Dubon2026.OriginalIdeleBaseChangeTower
import Dubon2026.OriginalNormHomologySubgroupTransfer

/-! # The actual fixed-field class norm is the quotient trace

Existing full-class descent and normal-invariant coefficients retain the
literal intermediate-field norm. This supplies the arithmetic side of
DUB-17's subgroup norm/homology comparison for prescribed-support fields.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal] [Fintype (Gal(L/K) ⧸ S)]

/-- Actual base-class inclusion carries the fixed-field norm to the
literal quotient trace in the full original class coefficient. -/
theorem originalFullClass_fixedField_norm_trace
    (c : Additive (OriginalNumberFieldIdeleClassGroup (IntermediateField.fixedField S))) :
    (originalFullClassBaseInvariantEquiv K L
      (originalIdeleClassNormLinear K (IntermediateField.fixedField S) c)).val =
      (((originalIdeleClassRep K L).quotientToInvariants S).ρ.norm
        ((originalIdeleClassNormalInvariantInclusion S).hom c)).val := by
  let F := IntermediateField.fixedField S
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup S
  let e := IsGalois.normalAutEquivQuotient S
  let A := originalIdeleClassRep K F
  let j := originalIdeleClassNormalInvariantInclusion S
  have hn : (Rep.res e.toMonoidHom A).ρ.norm c = A.ρ.norm c := by
    simp only [Representation.norm, LinearMap.sum_apply]
    exact Equiv.sum_comp e.toEquiv (fun g => A.ρ g c)
  have ht := originalCoefficientMorphism_norm j c
  rw [hn] at ht
  have hf := congrArg Subtype.val (originalFullClassBaseInvariant_norm K F c)
  have hj : (j.hom (A.ρ.norm c)).val =
      (originalFullClassBaseInvariantEquiv K L (originalIdeleClassNormLinear K F c)).val := by
    change Additive.ofMul (originalIdeleClassBaseChangeMap K F
      (originalIdeleClassNorm K F c.toMul)) = A.ρ.norm c at hf
    rw [← hf]
    change Additive.ofMul (originalIdeleClassBaseChangeMap F L
      (originalIdeleClassBaseChangeMap K F (originalIdeleClassNorm K F c.toMul))) =
        Additive.ofMul (originalIdeleClassBaseChangeMap K L (originalIdeleClassNorm K F c.toMul))
    exact congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_tower K F L _)
  exact hj.symm.trans (congrArg Subtype.val ht)

end
end Dubon2026
