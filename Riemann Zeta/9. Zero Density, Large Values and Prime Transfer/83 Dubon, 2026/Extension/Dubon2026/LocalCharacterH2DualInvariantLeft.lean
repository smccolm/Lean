import Dubon2026.ContinuousCharacterH2EffacementDescent
import Dubon2026.ContinuousFiniteCoefficientEffacement
import Dubon2026.LocalCharacterDualH1Perfect
import Dubon2026.FiniteCoinducedCoefficientQuotient

/-! # Original local H2 classes are detected by actual dual invariants

Every original H2 class has a proved finite coinduced effacement. The actual
quotient and the already proved local H1 duality discharge all hypotheses of
the low-degree descent. This supplies the missing H2 injectivity input to
DUB-17's local endpoints for the subsequent global-duality/Selmer sequence.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul
  finiteEffacementCoefficientTopology finiteEffacementCoefficientDiscrete finiteEffacementCosets

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

/-- An original finite-coefficient local H2 class annihilating every original
character-dual invariant is zero; both effacement and local H1 duality are proved. -/
theorem localCharacterH2DualInvariant_left_zero (hq : (q : K) ≠ 0)
    (x : ContinuousRepresentationH2 A hA)
    (hx : ∀ w, localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ
      (continuousCharacterH2DualInvariantPairing A χ hχ hA x w) = 0) : x = 0 := by
  obtain ⟨U, hfin, hι, hz⟩ := continuousH2_exists_finite_coinduced_effacement A hA x
  let S := U.toSubgroup
  let B := Rep.coind S.subtype (Rep.res S.subtype A)
  letI : Finite B := hfin
  letI : TopologicalSpace (characterDualCoefficientRep B χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep B χ) := ⟨rfl⟩
  let hB := finiteCoinducedCoefficientAction_continuous A S hA U.isOpen
  let C := finiteCoinducedCoefficientQuotient A S
  haveI : Finite C := finiteCoinducedCoefficientQuotient_finite A S
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : TopologicalSpace (characterDualCoefficientRep C χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep C χ) := ⟨rfl⟩
  let hC := finiteCoinducedCoefficientQuotientAction_continuous A S hA U.isOpen
  haveI := localCharacterDualH1ScalarCup_isPerfPair K Ω q χ hχ e heρ B hB hq
  haveI := localCharacterDualH1ScalarCup_isPerfPair K Ω q χ hχ e heρ C hC hq
  exact continuousCharacterH2_left_zero_of_effacement A B C χ hχ
    (finiteCoinducedCoefficientUnit A S) hι
    (finiteCoinducedCoefficientUnit_equivariant A S)
    (finiteCoinducedCoefficientProjection A S) (finiteCoinducedCoefficientSequence_exact A S).2.1
    (finiteCoinducedCoefficientProjection_equivariant A S) (finiteCoinducedCoefficientSequence_exact A S).2.2
    hA hB hC (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ)
    (LinearMap.IsPerfPair.bijective_left (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ B hB)).surjective
    (LinearMap.IsPerfPair.bijective_left (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ C hC)).injective x hz hx

end
end Dubon2026
