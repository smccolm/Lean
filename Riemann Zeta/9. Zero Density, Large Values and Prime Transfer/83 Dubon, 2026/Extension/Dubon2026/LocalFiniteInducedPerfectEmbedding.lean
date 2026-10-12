import Dubon2026.LocalInducedCharacterDualPerfect
import Dubon2026.ContinuousFiniteCoefficientSplitting
import Dubon2026.FiniteCoinducedCoefficientUnit
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.SpectralValuationExtension

/-! # An actual finite induced embedding with proved local perfectness

The original finite coefficient action supplies its own finite Galois splitting
field. Its local structure and valuation compatibility are derived, so no
splitting-field or induced-duality certificate is assumed. The actual unit
embedding and its perfect induced cup are the inputs to DUB-17's remaining
finite-module exact-sequence argument, not a claim of full local duality.
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

/-- The actual local coefficient embeds injectively into a genuine finite
coinduced module whose original invariant-valued character-dual cup is proved
perfect. The finite splitting field and its compatible local structure are constructed. -/
theorem localField_exists_perfect_coinduced_embedding (hq : (q : K) ≠ 0) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g : Gal(Ω/K), g ∈ F.toIntermediateField.fixingSubgroup → ∀ a : A, A.ρ g a = a) ∧
      let B := Rep.coind F.toIntermediateField.fixingSubgroup.subtype
        (Rep.res F.toIntermediateField.fixingSubgroup.subtype A)
      letI : TopologicalSpace B := ⊥
      letI : DiscreteTopology B := ⟨rfl⟩
      letI : TopologicalSpace (characterDualCoefficientRep B χ) := ⊥
      letI : DiscreteTopology (characterDualCoefficientRep B χ) := ⟨rfl⟩
      Finite B ∧ Function.Injective (finiteCoinducedCoefficientUnit A F.toIntermediateField.fixingSubgroup) ∧
        (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ B
          (finiteCoinducedCoefficientAction_continuous A F.toIntermediateField.fixingSubgroup hA
            F.toIntermediateField.fixingSubgroup_isOpen)).IsPerfPair := by
  obtain ⟨F, hF⟩ := continuousFiniteCoefficient_exists_splittingField A hA
  refine ⟨F, hF, ?_⟩
  let B := Rep.coind F.toIntermediateField.fixingSubgroup.subtype
    (Rep.res F.toIntermediateField.fixingSubgroup.subtype A)
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : TopologicalSpace (characterDualCoefficientRep B χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep B χ) := ⟨rfl⟩
  refine ⟨coinducedCoefficient_finite A F.toIntermediateField.fixingSubgroup,
    finiteCoinducedCoefficientUnit_injective A F.toIntermediateField.fixingSubgroup, ?_⟩
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  haveI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  exact localInducedCharacterDualH1ScalarCup_isPerfPair K Ω F.toIntermediateField q χ hχ e heρ
    A hA (fun g a => hF g g.property a) hq

end
end Dubon2026
