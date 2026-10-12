import Dubon2026.LocalFixingCharacterDualAnnihilators
import Dubon2026.LocalCharacterLineCorestrictionInjection
import Dubon2026.ContinuousInducedCharacterDualAnnihilators
import Dubon2026.LocalCharacterDualScalarCup
import Dubon2026.LocalFieldFiniteScalarCoefficientH1
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # Original induced local character-dual cups are perfect

The actual split-field annihilators and original character-line corestriction
injection supply both inputs to continuous induced nondegeneracy. Local H1
finiteness then proves perfectness of the actual invariant-valued pairing.
This is the induced-module base in the DUB-17 finite-module duality argument.
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
local instance localInducedDualTopology : TopologicalSpace
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype (characterDualCoefficientRep A χ))) := ⊥

/-- The chosen original induced-dual topology is discrete. -/
local instance localInducedDualDiscrete : DiscreteTopology
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype (characterDualCoefficientRep A χ))) := ⟨rfl⟩

include hE in
/-- The original invariant-valued induced cup is injective in its first
argument, with subgroup nondegeneracy and corestriction injectivity derived. -/
theorem localInducedCharacterDualH1ScalarCup_left_injective :
    Function.Injective (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)) := by
  intro x y h
  apply sub_eq_zero.mp
  apply continuousInducedCharacterDualH1Cup_left_zero A E.fixingSubgroup χ hχ hA E.fixingSubgroup_isOpen
    (localCharacterLineFixingCorestriction_injective K Ω E q χ hχ e heρ)
    (localFixingCharacterDualH1Cup_left_injective K Ω E q χ hχ e heρ A hA hE)
  intro z
  apply (localCharacterDualH1ScalarCup_eq_zero_iff K Ω q χ hχ e heρ
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
    (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)
    (x - y) z).mp
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h z)

include hE in
/-- The original invariant-valued induced cup has an injective opposite map,
using the original local Kummer theorem on the actual splitting field. -/
theorem localInducedCharacterDualH1ScalarCup_right_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)).flip := by
  have hqE : (q : E) ≠ 0 := by
    intro hz
    apply hq
    apply (algebraMap K E).injective
    simpa only [map_natCast, map_zero] using hz
  intro x y h
  apply sub_eq_zero.mp
  apply continuousInducedCharacterDualH1Cup_right_zero A E.fixingSubgroup χ hχ hA E.fixingSubgroup_isOpen
    (localCharacterLineFixingCorestriction_injective K Ω E q χ hχ e heρ)
    (localFixingCharacterDualH1Cup_right_injective K Ω E q χ hχ e heρ A hA hE hqE)
  intro z
  apply (localCharacterDualH1ScalarCup_eq_zero_iff K Ω q χ hχ e heρ
    (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
    (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)
    z (x - y)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h z)

include hE in
/-- The actual invariant-valued character-dual cup is perfect on the original
module induced from an actual finite local splitting field. Both annihilators
and finiteness of its original H1 spaces are proved from existing local results. -/
theorem localInducedCharacterDualH1ScalarCup_isPerfPair (hq : (q : K) ≠ 0) :
    (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)).IsPerfPair := by
  let B := Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A)
  let hB := finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen
  haveI := localField_finiteScalarCoefficientH1 q K Ω B hB hq
  haveI : Module.Finite (ZMod q) (ContinuousRepresentationH1 B hB) := Module.Finite.of_finite
  exact LinearMap.IsPerfPair.of_injective (p := localCharacterDualH1ScalarCup K Ω q χ hχ e heρ B hB)
    (localInducedCharacterDualH1ScalarCup_left_injective K Ω E q χ hχ e heρ A hA hE)
    (localInducedCharacterDualH1ScalarCup_right_injective K Ω E q χ hχ e heρ A hA hE hq)

end
end Dubon2026
