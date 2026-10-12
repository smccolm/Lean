import Dubon2026.LocalFixingCharacterDualH2Annihilators
import Dubon2026.LocalCharacterLineCorestrictionInjection
import Dubon2026.ContinuousInducedCharacterDualH2Annihilators
import Dubon2026.LocalTrivialCharacterDualH2Perfect
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # The actual induced local H2/H0 endpoint is perfect

Original subgroup endpoint nondegeneracy and injectivity of scalar
corestriction discharge both induced annihilators. Finiteness of the actual
invariant space suffices for perfectness. This supplies the degree-two
induced base for DUB-17's remaining finite-module local-duality argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]


  (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))]
  [DiscreteTopology (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))]
  [TopologicalSpace (characterDualCoefficientRep
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A)) χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))
  (hE : ∀ g : E.fixingSubgroup, ∀ a : A, A.ρ (g : Gal(Ω/K)) a = a)

/-- The actual induced dual uses its discrete finite coefficient topology. -/
local instance localInducedH2DualTopology : TopologicalSpace
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype (characterDualCoefficientRep A χ))) := ⊥

/-- The chosen original induced-dual topology is discrete. -/
local instance localInducedH2DualDiscrete : DiscreteTopology
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype (characterDualCoefficientRep A χ))) := ⟨rfl⟩

include hE in
/-- The actual normalized induced endpoint detects its left argument,
with the original subgroup and corestriction premises discharged. -/
theorem localInducedCharacterDualH2InvariantScalarPairing_left_injective :
    Function.Injective (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)) := by
  intro x y h
  apply sub_eq_zero.mp
  apply continuousInducedCharacterDualH2InvariantPairing_left_zero A E.fixingSubgroup χ hχ hA E.fixingSubgroup_isOpen
    (localCharacterLineFixingCorestriction_injective K Ω E q χ hχ e heρ)
    (localFixingCharacterDualH2InvariantPairing_left_injective K Ω E q χ hχ e heρ A hA hE)
  intro z
  apply (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ).injective
  change localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
    (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen) (x - y) z =
    (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ) 0
  rw [map_zero, map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h z)

include hE in
/-- The actual normalized induced endpoint detects its right argument,
with the original subgroup and corestriction premises discharged. -/
theorem localInducedCharacterDualH2InvariantScalarPairing_right_injective :
    Function.Injective (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)).flip := by
  intro x y h
  apply sub_eq_zero.mp
  apply continuousInducedCharacterDualH2InvariantPairing_right_zero A E.fixingSubgroup χ hχ hA E.fixingSubgroup_isOpen
    (localCharacterLineFixingCorestriction_injective K Ω E q χ hχ e heρ)
    (localFixingCharacterDualH2InvariantPairing_right_injective K Ω E q χ hχ e heρ A hA hE)
  intro z
  apply (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ).injective
  change localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
    (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen) z (x - y) =
    (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ) 0
  rw [map_zero, map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h z)

include hE in
/-- The original induced H2/H0 endpoint is perfect. Only the actual finite
invariant space is used for finite dimensionality; H2 finiteness is not assumed. -/
theorem localInducedCharacterDualH2InvariantScalarPairing_isPerfPair :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)).IsPerfPair := by
  let B := Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A)
  let hB := finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen
  haveI : Module.Finite (ZMod q) B.ρ.invariants := Module.Finite.of_finite
  exact LinearMap.IsPerfPair.of_injective' (p := localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ B hB)
    (localInducedCharacterDualH2InvariantScalarPairing_left_injective K Ω E q χ hχ e heρ A hA hE)
    (localInducedCharacterDualH2InvariantScalarPairing_right_injective K Ω E q χ hχ e heρ A hA hE)

end
end Dubon2026
