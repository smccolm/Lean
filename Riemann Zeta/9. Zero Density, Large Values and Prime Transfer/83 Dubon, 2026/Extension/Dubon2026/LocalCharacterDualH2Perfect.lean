import Dubon2026.LocalCharacterH2DualInvariantLeft
import Dubon2026.ContinuousCharacterBidualInvariant
import Dubon2026.LocalCharacterDualH2Surjectivity

/-! # Original local H2/H0 perfectness for arbitrary finite actions

Actual finite effacement and proved H1 duality detect every dual H2 class.
Original bidual invariants identify this with the existing endpoint pairing.
Together with its already proved surjectivity, this closes arbitrary-action
prime-field H0/H2 duality for DUB-17's global-duality/Selmer dependency.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

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
  (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

/-- The original dual H2 endpoint has zero left annihilator for arbitrary
finite coefficient actions; no split action or higher vanishing is assumed. -/
theorem localCharacterDualH2InvariantScalarPairing_left_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA) := by
  haveI : Finite (characterDualCoefficientRep A χ) :=
    Finite.of_injective (fun ℓ : characterDualCoefficientRep A χ => (ℓ : A → ZMod q)) DFunLike.coe_injective
  let D := characterDualCoefficientRep A χ
  let hD := finiteCharacterDualAction_continuous A χ hA hχ
  letI : TopologicalSpace (characterDualCoefficientRep D χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep D χ) := ⟨rfl⟩
  intro x y h
  apply sub_eq_zero.mp
  apply localCharacterH2DualInvariant_left_zero K Ω q χ hχ e heρ D hD hq
  intro w
  obtain ⟨w, rfl⟩ := (characterBidualInvariantEquiv A χ).surjective w
  rw [continuousCharacterH2DualInvariantPairing_bidual]
  change localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA (x - y) w = 0
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h w)

/-- The exact existing local dual H2/invariant pairing is perfect for every
finite continuous prime-field action. H2 injectivity is proved by effacement,
and the independent invariant-functional realization supplies surjectivity. -/
theorem localCharacterDualH2InvariantScalarPairing_isPerfPair (hq : (q : K) ≠ 0) :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA).IsPerfPair := by
  haveI : Module.Finite (ZMod q) A.ρ.invariants := Module.Finite.of_finite
  apply LinearMap.IsPerfPair.of_injective'
    (localCharacterDualH2InvariantScalarPairing_left_injective K Ω q χ hχ e heρ A hA hq)
  exact LinearMap.flip_injective_iff₂.mpr
    (localCharacterDualH2InvariantScalarPairing_surjective K Ω q χ hχ e heρ A hA hq)

end
end Dubon2026
