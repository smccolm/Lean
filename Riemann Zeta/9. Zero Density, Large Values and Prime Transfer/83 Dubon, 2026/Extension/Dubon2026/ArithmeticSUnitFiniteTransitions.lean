import Dubon2026.ArithmeticSUnitFiniteStageInclusion
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Actual transition maps between finite Galois S-unit coefficients

The proved image description uniquely factors each smaller-stage inclusion
through the larger-stage inclusion. This gives the original field transition,
its composition law, and its actual Galois-equivariant coefficient morphism.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (hEF : E ≤ F)

local instance : NumberField E := NumberField.of_module_finite K E
local instance : NumberField F := NumberField.of_module_finite K F

include hEF in
private theorem stage_range_le :
    (arithmeticSUnitFiniteStageUnitMap K Ω a ha E).range ≤
      (arithmeticSUnitFiniteStageUnitMap K Ω a ha F).range := by
  intro u hu
  exact (arithmeticSUnitFiniteStageUnitMap_mem_range_iff K Ω a ha F u).mpr
    (hEF ((arithmeticSUnitFiniteStageUnitMap_mem_range_iff K Ω a ha E u).mp hu))

/-- The unique original coefficient transition between two actual finite Galois stages. -/
def arithmeticSUnitFiniteTransitionMap :
    (↑(arithmeticSUnitFiniteStageSupport K Ω a ha E) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))).unit E →*
    (↑(arithmeticSUnitFiniteStageSupport K Ω a ha F) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F :=
  (MonoidHom.ofInjective (arithmeticSUnitFiniteStageUnitMap_injective K Ω a ha F)).symm.toMonoidHom.comp
    ((arithmeticSUnitFiniteStageUnitMap K Ω a ha E).codRestrict _
      (fun u => stage_range_le K Ω a ha E F hEF ⟨u, rfl⟩))

/-- The actual transition commutes with the original arithmetic coefficient inclusions. -/
theorem arithmeticSUnitFiniteTransitionMap_global
    (u : (↑(arithmeticSUnitFiniteStageSupport K Ω a ha E) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))).unit E) :
    arithmeticSUnitFiniteStageUnitMap K Ω a ha F
      (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF u) =
        arithmeticSUnitFiniteStageUnitMap K Ω a ha E u :=
  MonoidHom.apply_ofInjective_symm (arithmeticSUnitFiniteStageUnitMap_injective K Ω a ha F) _

/-- The transition is exactly the original field embedding on each original S-unit value. -/
theorem arithmeticSUnitFiniteTransitionMap_coe
    (u : (↑(arithmeticSUnitFiniteStageSupport K Ω a ha E) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))).unit E) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF u).val.val =
      algebraMap E F u.val.val := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  apply F.toIntermediateField.val.injective
  have h := congrArg (fun x : (OriginalArithmeticSUnitRing K Ω a ha)ˣ => x.val.val)
    (arithmeticSUnitFiniteTransitionMap_global K Ω a ha E F hEF u)
  exact (arithmeticSUnitFiniteStageUnitMap_coe K Ω a ha F _).symm.trans
    (h.trans (arithmeticSUnitFiniteStageUnitMap_coe K Ω a ha E u))

/-- The actual same-stage transition is the identity on original S-units. -/
theorem arithmeticSUnitFiniteTransitionMap_refl
    (u : (↑(arithmeticSUnitFiniteStageSupport K Ω a ha E) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))).unit E) :
    arithmeticSUnitFiniteTransitionMap K Ω a ha E E le_rfl u = u := by
  apply arithmeticSUnitFiniteStageUnitMap_injective K Ω a ha E
  exact arithmeticSUnitFiniteTransitionMap_global K Ω a ha E E le_rfl u

/-- Inserting an actual intermediate stage leaves the original coefficient transition unchanged. -/
theorem arithmeticSUnitFiniteTransitionMap_trans
    (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hFP : F ≤ P)
    (u : (↑(arithmeticSUnitFiniteStageSupport K Ω a ha E) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))).unit E) :
    arithmeticSUnitFiniteTransitionMap K Ω a ha F P hFP
      (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF u) =
        arithmeticSUnitFiniteTransitionMap K Ω a ha E P (hEF.trans hFP) u := by
  apply arithmeticSUnitFiniteStageUnitMap_injective K Ω a ha P
  rw [arithmeticSUnitFiniteTransitionMap_global, arithmeticSUnitFiniteTransitionMap_global,
    arithmeticSUnitFiniteTransitionMap_global]

/-- The original finite-stage transition intertwines the actual field-automorphism restriction. -/
def arithmeticSUnitFiniteTransitionInclusion :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    restrictedCoefficientRep (arithmeticSUnitFiniteStageRep K Ω a ha E)
      (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K)) ⟶
      arithmeticSUnitFiniteStageRep K Ω a ha F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  refine Rep.ofHom {
    toLinearMap := (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF).toAdditive.toIntLinearMap
    isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF
    ((arithmeticSUnitFiniteStageRep K Ω a ha E).ρ (AlgEquiv.restrictNormalHom E g) x).toMul).val.val =
      g (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF x.toMul).val.val
  rw [arithmeticSUnitFiniteTransitionMap_coe, arithmeticSUnitFiniteTransitionMap_coe]
  exact AlgEquiv.restrictNormal_commutes g E x.toMul.val.val

end
end Dubon2026
