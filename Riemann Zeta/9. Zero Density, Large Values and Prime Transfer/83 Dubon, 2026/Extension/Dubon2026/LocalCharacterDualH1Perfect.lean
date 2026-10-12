import Dubon2026.LocalCharacterDualH1Left
import Dubon2026.ContinuousCharacterBidualCup

/-! # Local H1 character-dual perfectness for arbitrary finite prime-field actions

Apply the proved left annihilator to the actual character dual. Original
bidual evaluation and cup skew-symmetry prove the opposite annihilator.
Existing original local H1 finiteness then gives actual perfectness, removing
the arbitrary-action prime-field H1 premise in DUB-17's local Selmer pairing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets finiteCoinducedCoefficientQuotient_finite

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

/-- The actual normalized local H1 cup has zero right annihilator for
arbitrary finite continuous prime-field coefficients, by actual biduality
and the proved left-annihilator theorem applied to the original dual action. -/
theorem localCharacterDualH1ScalarCup_right_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).flip := by
  haveI : Finite (characterDualCoefficientRep A χ) :=
    Finite.of_injective (fun ℓ : characterDualCoefficientRep A χ => (ℓ : A → ZMod q))
      DFunLike.coe_injective
  let D := characterDualCoefficientRep A χ
  let hD := finiteCharacterDualAction_continuous A χ hA hχ
  letI : TopologicalSpace (characterDualCoefficientRep D χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep D χ) := ⟨rfl⟩
  intro x y h
  apply localCharacterDualH1ScalarCup_left_injective K Ω q χ hχ e heρ D hD hq
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (continuousCharacterBidualH1Equiv A χ hχ hA).surjective z
  change (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ)
    (continuousCharacterDualH1Cup D χ hχ hD x (continuousCharacterBidualH1Equiv A χ hχ hA w)) =
    (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ)
      (continuousCharacterDualH1Cup D χ hχ hD y (continuousCharacterBidualH1Equiv A χ hχ hA w))
  rw [continuousCharacterDualH1Cup_bidual, continuousCharacterDualH1Cup_bidual, map_neg, map_neg]
  exact congrArg Neg.neg (DFunLike.congr_fun h w)

/-- The genuine invariant-valued local H1 pairing is perfect for every
finite continuous prime-field coefficient action. Both annihilators and
original H1 finiteness are proved; no split-action, arbitrary duality or
higher-degree vanishing premise remains. -/
theorem localCharacterDualH1ScalarCup_isPerfPair (hq : (q : K) ≠ 0) :
    (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).IsPerfPair := by
  haveI := localField_finiteScalarCoefficientH1 q K Ω A hA hq
  haveI : Module.Finite (ZMod q) (ContinuousRepresentationH1 A hA) := Module.Finite.of_finite
  exact LinearMap.IsPerfPair.of_injective (p := localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA)
    (localCharacterDualH1ScalarCup_left_injective K Ω q χ hχ e heρ A hA hq)
    (localCharacterDualH1ScalarCup_right_injective K Ω q χ hχ e heρ A hA hq)

end
end Dubon2026
