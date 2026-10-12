import Dubon2026.LocalFiniteInducedPerfectEndpoints
import Dubon2026.ContinuousCharacterDualH2Naturality

/-! # Every original invariant functional is represented by a dual H2 class

Embed the actual finite module into its proved induced endpoint. Extend an
original invariant functional by pinned linear duality, represent it in the
induced H2, and pull back through original coefficient precomposition. This
surjectivity removes the endpoint premise in the direct local H1 annihilator
argument serving DUB-17, without higher-degree vanishing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets

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

/-- Every functional on the original invariant space is represented by an
actual character-dual H2 class. The induced module and its perfect endpoint
are constructed, so no arbitrary-module duality or H3 vanishing is assumed. -/
theorem localCharacterDualH2InvariantScalarPairing_surjective (hq : (q : K) ≠ 0) :
    Function.Surjective (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA) := by
  obtain ⟨F, _, hF⟩ := localField_exists_perfect_coinduced_endpoints K Ω q χ hχ e heρ A hA hq
  let B := Rep.coind F.toIntermediateField.fixingSubgroup.subtype
    (Rep.res F.toIntermediateField.fixingSubgroup.subtype A)
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : TopologicalSpace (characterDualCoefficientRep B χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep B χ) := ⟨rfl⟩
  let hB := finiteCoinducedCoefficientAction_continuous A F.toIntermediateField.fixingSubgroup hA
    F.toIntermediateField.fixingSubgroup_isOpen
  rcases hF with ⟨_, hi, _, hp⟩
  let φ := finiteCoinducedCoefficientUnit A F.toIntermediateField.fixingSubgroup
  let hφρ := finiteCoinducedCoefficientUnit_equivariant A F.toIntermediateField.fixingSubgroup
  let i := coefficientInvariantLinearMap A B φ hφρ
  have hii : Function.Injective i := coefficientInvariantLinearMap_injective A B φ hφρ hi
  haveI : (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ B hB).IsPerfPair := hp
  intro ℓ
  obtain ⟨ℓB, hℓ⟩ := LinearMap.dualMap_surjective_of_injective hii ℓ
  obtain ⟨z, hz⟩ := (LinearMap.IsPerfPair.bijective_left
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ B hB)).surjective ℓB
  refine ⟨continuousCoefficientH2Map (characterDualCoefficientRep B χ) (characterDualCoefficientRep A χ)
    (characterDualCoefficientMap A B χ φ) continuous_of_discreteTopology
    (characterDualCoefficientMap_equivariant A B χ φ hφρ)
    (finiteCharacterDualAction_continuous B χ hB hχ)
    (finiteCharacterDualAction_continuous A χ hA hχ) z, ?_⟩
  apply LinearMap.ext
  intro w
  change (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ)
    (continuousCharacterDualH2InvariantPairing A χ hχ hA _ w) = ℓ w
  rw [continuousCharacterDualH2InvariantPairing_naturality A B φ hφρ χ hχ hA hB]
  change localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ B hB z (i w) = ℓ w
  rw [hz]
  exact DFunLike.congr_fun hℓ w

end
end Dubon2026
