import Dubon2026.LocalFieldRootCorestrictionInjection
import Dubon2026.ContinuousH2AdditiveCorestriction
import Dubon2026.LocalCharacterDualScalarCup

/-! # The original character-line H2 corestriction is injective

The actual root-H2 corestriction theorem and its original fixing-subgroup
identification remove the corestriction kernel assumption in the induced
annihilator transfer. The prime-field character line is transported by its
actual root identification, preserving the literal coset trace.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul
  rootLocalCorestrictionIsGalois rootLocalCorestrictionStageTopology
  rootLocalCorestrictionStageDiscrete rootLocalCorestrictionUnitTopology rootLocalCorestrictionUnitDiscrete

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [tUnits : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [dUnits : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


/-- The genuine finite fixing subgroup has the original finite coset type. -/
local instance localCharacterLineCorestrictionCosets : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) :=
  Fintype.ofFinite _

include dUnits in
/-- The original root-H2 coset corestriction on the actual fixing subgroup
is injective, by the proved field corestriction and original H2 identification. -/
theorem localFieldRootFixingCorestriction_injective :
    Function.Injective (continuousRepresentationH2Corestriction
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
      (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) q)
      E.fixingSubgroup E.fixingSubgroup_isOpen) := by
  intro x y h
  obtain ⟨x, rfl⟩ := (galoisFixingRootH2Equiv K Ω E q).surjective x
  obtain ⟨y, rfl⟩ := (galoisFixingRootH2Equiv K Ω E q).surjective y
  exact congrArg (galoisFixingRootH2Equiv K Ω E q)
    (localFieldRootContinuousCorestriction_injective K Ω E q h)

variable (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))

include e heρ dUnits in
/-- The actual prime-field character H2 corestriction is injective on the
original finite fixing subgroup. The original local invariant and actual root
coefficient identification discharge this assumption without an index restriction. -/
theorem localCharacterLineFixingCorestriction_injective :
    Function.Injective (continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) E.fixingSubgroup E.fixingSubgroup_isOpen) := by
  let C := coefficientCharacterRep χ
  let R := galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q
  let hC := coefficientCharacterAction_continuous χ hχ
  let hR := discreteGaloisRootAction_continuous (K := K) (Ω := Ω) q
  let e₂ := continuousH2AdditiveCoefficientEquiv C R e continuous_of_discreteTopology
    continuous_of_discreteTopology heρ hC hR
  let e₂S := continuousH2AdditiveCoefficientEquiv (restrictedCoefficientRep C E.fixingSubgroup.subtype)
    (restrictedCoefficientRep R E.fixingSubgroup.subtype) e continuous_of_discreteTopology
    continuous_of_discreteTopology (fun g a => heρ g a)
    (restrictedCoefficientAction_continuous C E.fixingSubgroup.subtype continuous_subtype_val hC)
    (restrictedCoefficientAction_continuous R E.fixingSubgroup.subtype continuous_subtype_val hR)
  intro x y h
  apply e₂S.injective
  apply localFieldRootFixingCorestriction_injective K Ω E q
  exact (continuousH2AdditiveCoefficientEquiv_corestriction C R e heρ E.fixingSubgroup
    continuous_of_discreteTopology continuous_of_discreteTopology hC hR E.fixingSubgroup_isOpen x).symm.trans
      ((congrArg e₂ h).trans
        (continuousH2AdditiveCoefficientEquiv_corestriction C R e heρ E.fixingSubgroup
          continuous_of_discreteTopology continuous_of_discreteTopology hC hR E.fixingSubgroup_isOpen y))

end
end Dubon2026
