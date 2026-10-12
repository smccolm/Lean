import Dubon2026.ContinuousCharacterDualCupGroupEquiv
import Dubon2026.LocalTrivialCharacterDualLeft
import Dubon2026.LocalTrivialCharacterDualRight
import Dubon2026.GaloisFixingRootCohomology

/-! # Split local nondegeneracy on the genuine fixing subgroup

The existing local Kummer theorem applies over the actual splitting field.
Original group and coefficient identifications transport both annihilators
back to the actual subgroup, discharging the subgroup-pairing premise in the
DUB-17 induced-module argument.
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
local instance localFixingCharacterIsGalois : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω

include e heρ hE in
/-- The original subgroup cup has zero left annihilator when its actual
fixing field is local and splits the original finite coefficient action. -/
theorem localFixingCharacterDualH1Cup_left_injective :
    Function.Injective (continuousCharacterDualH1Cup (restrictedCoefficientRep A E.fixingSubgroup.subtype)
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
  let D₀ := characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/E) →* ZMod q)) θ
  letI : TopologicalSpace D₀ := ⊥
  letI : DiscreteTopology D₀ := ⟨rfl⟩
  apply continuousCharacterDualH1Cup_left_injective_of_groupEquiv Aₛ χₛ hχₛ hAₛ j hj hji
  exact localTrivialCharacterDualH1Cup_left_injective E Ω q θ hθ e
    (fun g a => heρ (j g) a) B (fun g a => hE (j g) a) hB

include e heρ hE in
/-- The original subgroup cup has zero right annihilator over the same
actual splitting field. Kummer descent supplies the opposite scalar input. -/
theorem localFixingCharacterDualH1Cup_right_injective (hq : (q : E) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup (restrictedCoefficientRep A E.fixingSubgroup.subtype)
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
  let D₀ := characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/E) →* ZMod q)) θ
  letI : TopologicalSpace D₀ := ⊥
  letI : DiscreteTopology D₀ := ⟨rfl⟩
  apply continuousCharacterDualH1Cup_right_injective_of_groupEquiv Aₛ χₛ hχₛ hAₛ j hj hji
  exact localTrivialCharacterDualH1Cup_right_injective E Ω q θ hθ e
    (fun g a => heρ (j g) a) B (fun g a => hE (j g) a) hB hq

end
end Dubon2026
