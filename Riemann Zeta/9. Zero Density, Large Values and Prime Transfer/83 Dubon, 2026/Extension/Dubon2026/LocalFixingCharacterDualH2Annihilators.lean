import Dubon2026.ContinuousCharacterDualH2GroupEquiv
import Dubon2026.LocalTrivialCharacterDualH2Perfect
import Dubon2026.GaloisFixingRootCohomology

/-! # The split local H2/H0 endpoint on the genuine fixing subgroup

The original group identifications transport the proved split local endpoint
back to the actual subgroup. This discharges the subgroup endpoint premise
in DUB-17's induced-module local-duality argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul
  fixingRootStageTopology fixingRootStageDiscrete fixingRootUnitTopology fixingRootUnitDiscrete

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  (E : IntermediateField K Ω)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))
  (hE : ∀ g : E.fixingSubgroup, ∀ a : A, A.ρ (g : Gal(Ω/K)) a = a)

/-- The actual algebraic closure remains Galois over the original intermediate field. -/
local instance localFixingCharacterH2IsGalois : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω

include e heρ hE in
/-- The actual subgroup endpoint detects every dual H2 class over the
original local splitting field. -/
theorem localFixingCharacterDualH2InvariantPairing_left_injective :
    Function.Injective (continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A E.fixingSubgroup.subtype)
      (χ.comp E.fixingSubgroup.subtype) (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A E.fixingSubgroup.subtype continuous_subtype_val hA)) := by
  let S := E.fixingSubgroup
  let Aₛ := restrictedCoefficientRep A S.subtype
  let χₛ := χ.comp S.subtype
  let hAₛ := restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA
  let hχₛ := hχ.comp continuous_subtype_val (f := S.subtype)
  let j := E.fixingSubgroupEquiv.symm
  let hj := fixingSubgroupEquiv_symm_continuous K Ω E
  let hji := fixingSubgroupEquiv_continuous K Ω E
  let B := restrictedCoefficientRep Aₛ j.toMonoidHom
  let θ := χₛ.comp j.toMonoidHom
  let hB := restrictedCoefficientAction_continuous Aₛ j.toMonoidHom hj hAₛ
  let hθ := hχₛ.comp hj
  apply continuousCharacterDualH2InvariantPairing_left_injective_of_groupEquiv Aₛ χₛ hχₛ hAₛ j hj hji
  intro x y h
  apply localTrivialCharacterDualH2InvariantScalarPairing_left_injective E Ω q θ hθ e
    (fun g a => heρ (j g) a) B hB (fun g a => hE (j g) a)
  apply LinearMap.ext
  intro w
  exact congrArg (localCharacterLineH2ScalarEquiv E Ω q θ hθ e (fun g a => heρ (j g) a))
    (DFunLike.congr_fun h w)

include e heρ hE in
/-- The actual subgroup endpoint detects every invariant over the same
original local splitting field through the proved local H2 invariant. -/
theorem localFixingCharacterDualH2InvariantPairing_right_injective :
    Function.Injective (continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A E.fixingSubgroup.subtype)
      (χ.comp E.fixingSubgroup.subtype) (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A E.fixingSubgroup.subtype continuous_subtype_val hA)).flip := by
  let S := E.fixingSubgroup
  let Aₛ := restrictedCoefficientRep A S.subtype
  let χₛ := χ.comp S.subtype
  let hAₛ := restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA
  let hχₛ := hχ.comp continuous_subtype_val (f := S.subtype)
  let j := E.fixingSubgroupEquiv.symm
  let hj := fixingSubgroupEquiv_symm_continuous K Ω E
  let hji := fixingSubgroupEquiv_continuous K Ω E
  let B := restrictedCoefficientRep Aₛ j.toMonoidHom
  let θ := χₛ.comp j.toMonoidHom
  let hB := restrictedCoefficientAction_continuous Aₛ j.toMonoidHom hj hAₛ
  let hθ := hχₛ.comp hj
  apply continuousCharacterDualH2InvariantPairing_right_injective_of_groupEquiv Aₛ χₛ hχₛ hAₛ j hj hji
  intro x y h
  apply localTrivialCharacterDualH2InvariantScalarPairing_right_injective E Ω q θ hθ e
    (fun g a => heρ (j g) a) B hB (fun g a => hE (j g) a)
  apply LinearMap.ext
  intro w
  exact congrArg (localCharacterLineH2ScalarEquiv E Ω q θ hθ e (fun g a => heρ (j g) a))
    (DFunLike.congr_fun h w)

end
end Dubon2026
