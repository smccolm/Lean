import Dubon2026.LocalCharacterDualH2Surjectivity
import Dubon2026.ContinuousCharacterDualLowDegreeDescent
import Dubon2026.FiniteCoinducedCoefficientQuotient

/-! # The actual local H1 left annihilator for arbitrary finite coefficients

Construct the finite induced embedding and literal quotient, then discharge
the low-degree descent inputs with both proved induced pairings and the
original quotient endpoint surjectivity. This removes the arbitrary-action
left nondegeneracy premise for finite prime-field local duality in DUB-17's
Selmer dependency chain, without assuming higher-degree vanishing.
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

/-- The original normalized local H1 cup has zero left annihilator for
any finite continuous prime-field coefficient action. The induced module,
its quotient and every local nondegeneracy premise are constructed or proved. -/
theorem localCharacterDualH1ScalarCup_left_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA) := by
  obtain ⟨F, _, hF⟩ := localField_exists_perfect_coinduced_endpoints K Ω q χ hχ e heρ A hA hq
  let S := F.toIntermediateField.fixingSubgroup
  let B := Rep.coind S.subtype (Rep.res S.subtype A)
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : TopologicalSpace (characterDualCoefficientRep B χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep B χ) := ⟨rfl⟩
  let hB := finiteCoinducedCoefficientAction_continuous A S hA F.toIntermediateField.fixingSubgroup_isOpen
  let C := finiteCoinducedCoefficientQuotient A S
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : TopologicalSpace (characterDualCoefficientRep C χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep C χ) := ⟨rfl⟩
  let hC := finiteCoinducedCoefficientQuotientAction_continuous A S hA F.toIntermediateField.fixingSubgroup_isOpen
  rcases hF with ⟨_, _, hp₁, hp₂⟩
  haveI : (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ B hB).IsPerfPair := hp₁
  haveI : (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ B hB).IsPerfPair := hp₂
  exact continuousCharacterDualH1_left_injective_of_exact A B C χ hχ
    (finiteCoinducedCoefficientUnit A S) (finiteCoinducedCoefficientUnit_injective A S)
    (finiteCoinducedCoefficientUnit_equivariant A S)
    (finiteCoinducedCoefficientProjection A S) (finiteCoinducedCoefficientSequence_exact A S).2.1
    (finiteCoinducedCoefficientProjection_equivariant A S) (finiteCoinducedCoefficientSequence_exact A S).2.2
    hA hB hC (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ)
    (LinearMap.IsPerfPair.bijective_left (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ B hB)).injective
    (LinearMap.IsPerfPair.bijective_left (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ B hB)).injective
    (localCharacterDualH2InvariantScalarPairing_surjective K Ω q χ hχ e heρ C hC hq)

end
end Dubon2026
