import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology




noncomputable section
open Matrix CategoryTheory
open scoped NumberField ValuativeRel nonZeroDivisors

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite


/-- Exact original-object consumer of `continuousCoinducedCharacterDualH1Equiv_cup`. -/
theorem actual_induced_perfect_continuousCoinducedCharacterDualH1Equiv_cup_source
    (x : ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS))
    (y : ContinuousRepresentationH1
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)) :
    continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x
      (continuousCoinducedCharacterDualH1Equiv A S χ hχ hA hS y) =
    continuousH1Cup (Rep.coind S.subtype (Rep.res S.subtype A))
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (coefficientCharacterRep χ) (coinducedCharacterPairing A S χ)
      (coinducedCharacterPairing_equivariant A S χ) continuous_of_discreteTopology
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)
      (coefficientCharacterAction_continuous χ hχ) x y :=
  continuousCoinducedCharacterDualH1Equiv_cup A S χ hχ hA hS x y

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
attribute [local instance] coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous

/-- Exact original-object consumer of `continuousCoinducedCharacterDualShapiro_cup`. -/
theorem actual_induced_perfect_continuousCoinducedCharacterDualShapiro_cup_source
    (x : ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA))
    (y : ContinuousRepresentationH1 (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
      (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
        S.subtype continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ))) :
    continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedShapiroH1 A hA S hS x)
      (continuousCoinducedCharacterDualH1Equiv A S χ hχ hA hS
        (continuousCoinducedShapiroH1 (characterDualCoefficientRep A χ)
          (finiteCharacterDualAction_continuous A χ hA hχ) S hS y)) =
    continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) S hS
      (continuousH1Cup (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
        (restrictedCoefficientRep (coefficientCharacterRep χ) S.subtype)
        (characterDualEvaluation A χ) (fun g a ℓ => characterDualEvaluation_equivariant A χ g a ℓ)
        continuous_of_discreteTopology
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
          S.subtype continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ))
        (restrictedCoefficientAction_continuous (coefficientCharacterRep χ)
          S.subtype continuous_subtype_val (coefficientCharacterAction_continuous χ hχ)) x y) :=
  continuousCoinducedCharacterDualShapiro_cup A S χ hχ hA hS x y

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))




attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous


/-- Exact original-object consumer of `continuousInducedCharacterDualH1Cup_right_zero`. -/
theorem actual_induced_perfect_continuousInducedCharacterDualH1Cup_right_zero_source
    (hcor : Function.Injective (continuousRepresentationH2Corestriction
      (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS))
    (hsub : Function.Injective (continuousCharacterDualH1Cup
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)).flip)
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)
      (finiteCharacterDualAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A)) χ
        (finiteCoinducedCoefficientAction_continuous A S hA hS) hχ))
    (hy : ∀ x, continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x y = 0) : y = 0 :=
  continuousInducedCharacterDualH1Cup_right_zero A S χ hχ hA hS hcor hsub y hy

end

section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  (A : Rep.{0} R G) (B : Rep.{0} S G)
  (e : A ≃+ B)
  (heρ : ∀ g a, e (A.ρ g a) = B.ρ g (e a))

  (U : Subgroup G) [Fintype (G ⧸ U)]



variable [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul S B]
  (he : Continuous e) (hei : Continuous e.symm)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2)) (hU : IsOpen (U : Set G))






/-- Exact original-object consumer of `continuousH2AdditiveCoefficientEquiv_corestriction`. -/
theorem actual_induced_perfect_continuousH2AdditiveCoefficientEquiv_corestriction_source
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep A U.subtype)
      (restrictedCoefficientAction_continuous A U.subtype continuous_subtype_val hA)) :
    continuousH2AdditiveCoefficientEquiv A B e he hei heρ hA hB
      (continuousRepresentationH2Corestriction A hA U hU x) =
    continuousRepresentationH2Corestriction B hB U hU
      (continuousH2AdditiveCoefficientEquiv (restrictedCoefficientRep A U.subtype)
        (restrictedCoefficientRep B U.subtype) e he hei (fun g a => heρ g a)
        (restrictedCoefficientAction_continuous A U.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous B U.subtype continuous_subtype_val hB) x) :=
  continuousH2AdditiveCoefficientEquiv_corestriction A B e heρ U he hei hA hB hU x

end

section

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




variable (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))



attribute [local instance] characterDualSequenceContinuousSMul
  rootLocalCorestrictionIsGalois rootLocalCorestrictionStageTopology
  rootLocalCorestrictionStageDiscrete rootLocalCorestrictionUnitTopology rootLocalCorestrictionUnitDiscrete
attribute [local instance] localCharacterLineCorestrictionCosets
include e heρ dUnits

/-- Exact original-object consumer of `localCharacterLineFixingCorestriction_injective`. -/
theorem actual_induced_perfect_localCharacterLineFixingCorestriction_injective_source :
    Function.Injective (continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) E.fixingSubgroup E.fixingSubgroup_isOpen) :=
  localCharacterLineFixingCorestriction_injective K Ω E q χ hχ e heρ

end

section

variable {k G H : Type} [Field k] [Group G] [Group H]



variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H ≃* G) (hj : Continuous j) (hji : Continuous j.symm)



attribute [local instance] characterDualSequenceContinuousSMul
include hji

/-- Exact original-object consumer of `continuousCharacterDualH1Cup_right_injective_of_groupEquiv`. -/
theorem actual_induced_perfect_continuousCharacterDualH1Cup_right_injective_of_groupEquiv_source
    (h : Function.Injective (continuousCharacterDualH1Cup
      (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)).flip) :
    Function.Injective (continuousCharacterDualH1Cup A χ hχ hA).flip :=
  continuousCharacterDualH1Cup_right_injective_of_groupEquiv A χ hχ hA j hj hji h

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul
  fixingRootStageTopology fixingRootStageDiscrete fixingRootUnitTopology fixingRootUnitDiscrete
include e heρ hE

/-- Exact original-object consumer of `localFixingCharacterDualH1Cup_right_injective`. -/
theorem actual_induced_perfect_localFixingCharacterDualH1Cup_right_injective_source (hq : (q : E) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup (restrictedCoefficientRep A E.fixingSubgroup.subtype)
      (χ.comp E.fixingSubgroup.subtype) (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A E.fixingSubgroup.subtype continuous_subtype_val hA)).flip :=
  localFixingCharacterDualH1Cup_right_injective K Ω E q χ hχ e heρ A hA hE hq

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous
include hE

/-- Exact original-object consumer of `localInducedCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_induced_perfect_localInducedCharacterDualH1ScalarCup_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)).IsPerfPair :=
  localInducedCharacterDualH1ScalarCup_isPerfPair K Ω E q χ hχ e heρ A hA hE hq

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets


/-- Exact original-object consumer of `localField_exists_perfect_coinduced_embedding`. -/
theorem actual_induced_perfect_localField_exists_perfect_coinduced_embedding_source (hq : (q : K) ≠ 0) :
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
            F.toIntermediateField.fixingSubgroup_isOpen)).IsPerfPair :=
  localField_exists_perfect_coinduced_embedding K Ω q χ hχ e heρ A hA hq

end

section

variable {k G ι : Type} [Field k] [Group G] [Fintype ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul k A]
  (χ : G →* k) (b : Module.Basis ι k A) (hscalar : ∀ g a, A.ρ g a = χ g • a)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hχ : Continuous χ)






/-- Exact original-object consumer of `continuousScalarH2_eq_zero_of_coordinates`. -/
theorem actual_split_endpoint_continuousScalarH2_eq_zero_of_coordinates_source (x : ContinuousRepresentationH2 A hA)
    (hx : ∀ i, continuousCoefficientH2Map A (coefficientCharacterRep χ) (b.coord i)
      continuous_of_discreteTopology (scalarCoefficientCoordinate_equivariant A χ b hscalar i)
      hA (coefficientCharacterAction_continuous χ hχ) x = 0) : x = 0 :=
  continuousScalarH2_eq_zero_of_coordinates A χ b hscalar hA hχ x hx

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterDualH2InvariantPairing_apply`. -/
theorem actual_split_endpoint_continuousCharacterDualH2InvariantPairing_apply_source
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : A.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing A χ hχ hA x w =
    continuousInvariantRightH2Map (characterDualCoefficientRep A χ) A
      (coefficientCharacterRep χ) (characterDualEvaluation A χ).flip
      (fun g ℓ a => characterDualEvaluation_equivariant A χ g a ℓ)
      continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ)
      (coefficientCharacterAction_continuous χ hχ) w x :=
  continuousCharacterDualH2InvariantPairing_apply A χ hχ hA x w

end

section

variable {k G ι : Type} [Field k] [Group G] [Fintype ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)



attribute [local instance] characterDualSequenceContinuousSMul
include b htrivial

/-- Exact original-object consumer of `continuousTrivialCharacterDualH2InvariantPairing_left_injective`. -/
theorem actual_split_endpoint_continuousTrivialCharacterDualH2InvariantPairing_left_injective_source :
    Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA) :=
  continuousTrivialCharacterDualH2InvariantPairing_left_injective A χ hχ hA b htrivial

end

section

variable {k G ι : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)




attribute [local instance] characterDualSequenceContinuousSMul
include b htrivial

/-- Exact original-object consumer of `continuousTrivialCharacterDualH2InvariantPairing_right_injective`. -/
theorem actual_split_endpoint_continuousTrivialCharacterDualH2InvariantPairing_right_injective_source
    (c : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ))
    (hc : c ≠ 0) : Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA).flip :=
  continuousTrivialCharacterDualH2InvariantPairing_right_injective A χ hχ hA b htrivial c hc

end

section

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



variable (htrivial : ∀ g a, A.ρ g a = a)



attribute [local instance] characterDualSequenceContinuousSMul
include htrivial

/-- Exact original-object consumer of `localTrivialCharacterDualH2InvariantScalarPairing_isPerfPair`. -/
theorem actual_split_endpoint_localTrivialCharacterDualH2InvariantScalarPairing_isPerfPair_source :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localTrivialCharacterDualH2InvariantScalarPairing_isPerfPair K Ω q χ hχ e heρ A hA htrivial

end

section

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)






/-- Exact original-object consumer of `coinducedShapiroZero_invariant`. -/
theorem actual_finite_duality_coinducedShapiroZero_invariant_source
    (w : (restrictedCoefficientRep A S.subtype).ρ.invariants) :
    coinducedShapiroZero A S w.val = (coinducedInvariantEquiv A S w).val :=
  coinducedShapiroZero_invariant A S w

end

section

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G)
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k)






/-- Exact original-object consumer of `coinducedShapiroTwoZero_pairing`. -/
theorem actual_finite_duality_coinducedShapiroTwoZero_pairing_source (c : S × S → characterDualCoefficientRep A χ)
    (w : A) (g h : G) :
    coinducedCharacterPairing A S χ (coinducedShapiroZero A S w)
      (coinducedShapiroTwo (characterDualCoefficientRep A χ) S c (g, h)) =
      cosetTraceTwo (coefficientCharacterRep χ) S
        (fun z => characterDualEvaluation A χ w (c z)) (g, h) :=
  coinducedShapiroTwoZero_pairing A S χ c w g h

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))




attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite


/-- Exact original-object consumer of `continuousCoinducedCharacterDualH2Equiv_pairing`. -/
theorem actual_finite_duality_continuousCoinducedCharacterDualH2Equiv_pairing_source
    (y : ContinuousRepresentationH2
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS))
    (w : (Rep.coind S.subtype (Rep.res S.subtype A)).ρ.invariants) :
    continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedCharacterDualH2Equiv A S χ hχ hA hS y) w =
    continuousInvariantRightH2Map
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (Rep.coind S.subtype (Rep.res S.subtype A)) (coefficientCharacterRep χ)
      (coinducedCharacterPairing A S χ).flip
      (fun g ℓ a => coinducedCharacterPairing_equivariant A S χ g a ℓ)
      continuous_of_discreteTopology
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)
      (coefficientCharacterAction_continuous χ hχ) w y :=
  continuousCoinducedCharacterDualH2Equiv_pairing A S χ hχ hA hS y w

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))




attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous


/-- Exact original-object consumer of `continuousCoinducedShapiroH2Invariant_pairing`. -/
theorem actual_finite_duality_continuousCoinducedShapiroH2Invariant_pairing_source
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
      (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ) S.subtype
        continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ)))
    (w : (restrictedCoefficientRep A S.subtype).ρ.invariants) :
    continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedCharacterDualH2Equiv A S χ hχ hA hS
        (continuousCoinducedShapiroH2 (characterDualCoefficientRep A χ)
          (finiteCharacterDualAction_continuous A χ hA hχ) S hS x))
      (coinducedInvariantEquiv A S w) =
    continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) S hS
      (continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A S.subtype)
        (χ.comp S.subtype) (hχ.comp continuous_subtype_val)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) x w) :=
  continuousCoinducedShapiroH2Invariant_pairing A S χ hχ hA hS x w

end

section

variable {k G H : Type} [Field k] [Group G] [Group H]



variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H ≃* G) (hj : Continuous j) (hji : Continuous j.symm)




attribute [local instance] characterDualSequenceContinuousSMul
include hji

/-- Exact original-object consumer of `continuousCharacterDualH2InvariantPairing_right_injective_of_groupEquiv`. -/
theorem actual_finite_duality_continuousCharacterDualH2InvariantPairing_right_injective_of_groupEquiv_source
    (h : Function.Injective (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)).flip) :
    Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA).flip :=
  continuousCharacterDualH2InvariantPairing_right_injective_of_groupEquiv A χ hχ hA j hj hji h

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul
  fixingRootStageTopology fixingRootStageDiscrete fixingRootUnitTopology fixingRootUnitDiscrete
include e heρ hE

/-- Exact original-object consumer of `localFixingCharacterDualH2InvariantPairing_right_injective`. -/
theorem actual_finite_duality_localFixingCharacterDualH2InvariantPairing_right_injective_source :
    Function.Injective (continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A E.fixingSubgroup.subtype)
      (χ.comp E.fixingSubgroup.subtype) (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A E.fixingSubgroup.subtype continuous_subtype_val hA)).flip :=
  localFixingCharacterDualH2InvariantPairing_right_injective K Ω E q χ hχ e heρ A hA hE

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))




attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous


/-- Exact original-object consumer of `continuousInducedCharacterDualH2InvariantPairing_right_zero`. -/
theorem actual_finite_duality_continuousInducedCharacterDualH2InvariantPairing_right_zero_source
    (hcor : Function.Injective (continuousRepresentationH2Corestriction
      (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS))
    (hsub : Function.Injective (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)).flip)
    (w : (Rep.coind S.subtype (Rep.res S.subtype A)).ρ.invariants)
    (hw : ∀ x, continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x w = 0) : w = 0 :=
  continuousInducedCharacterDualH2InvariantPairing_right_zero A S χ hχ hA hS hcor hsub w hw

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous
include hE

/-- Exact original-object consumer of `localInducedCharacterDualH2InvariantScalarPairing_isPerfPair`. -/
theorem actual_finite_duality_localInducedCharacterDualH2InvariantScalarPairing_isPerfPair_source :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ
      (Rep.coind E.fixingSubgroup.subtype (Rep.res E.fixingSubgroup.subtype A))
      (finiteCoinducedCoefficientAction_continuous A E.fixingSubgroup hA E.fixingSubgroup_isOpen)).IsPerfPair :=
  localInducedCharacterDualH2InvariantScalarPairing_isPerfPair K Ω E q χ hχ e heρ A hA hE

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets


/-- Exact original-object consumer of `localField_exists_perfect_coinduced_endpoints`. -/
theorem actual_finite_duality_localField_exists_perfect_coinduced_endpoints_source (hq : (q : K) ≠ 0) :
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
            F.toIntermediateField.fixingSubgroup_isOpen)).IsPerfPair ∧
        (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ B
          (finiteCoinducedCoefficientAction_continuous A F.toIntermediateField.fixingSubgroup hA
            F.toIntermediateField.fixingSubgroup_isOpen)).IsPerfPair :=
  localField_exists_perfect_coinduced_endpoints K Ω q χ hχ e heρ A hA hq

end

section

variable {k G : Type} [Field k] [Group G]
  (A B : Rep.{0} k G) (φ : A →ₗ[k] B)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))



variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterDualH2InvariantPairing_naturality`. -/
theorem actual_finite_duality_continuousCharacterDualH2InvariantPairing_naturality_source
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep B χ)
      (finiteCharacterDualAction_continuous B χ hB hχ)) (w : A.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing A χ hχ hA
      (continuousCoefficientH2Map (characterDualCoefficientRep B χ) (characterDualCoefficientRep A χ)
        (characterDualCoefficientMap A B χ φ) continuous_of_discreteTopology
        (characterDualCoefficientMap_equivariant A B χ φ hφρ)
        (finiteCharacterDualAction_continuous B χ hB hχ)
        (finiteCharacterDualAction_continuous A χ hA hχ) x) w =
      continuousCharacterDualH2InvariantPairing B χ hχ hB x
        (coefficientInvariantLinearMap A B φ hφρ w) :=
  continuousCharacterDualH2InvariantPairing_naturality A B φ hφρ χ hχ hA hB x w

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets


/-- Exact original-object consumer of `localCharacterDualH2InvariantScalarPairing_surjective`. -/
theorem actual_finite_duality_localCharacterDualH2InvariantScalarPairing_surjective_source (hq : (q : K) ≠ 0) :
    Function.Surjective (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA) :=
  localCharacterDualH2InvariantScalarPairing_surjective K Ω q χ hχ e heρ A hA hq

end

section

variable {k A₁ AD₁ B₁ BD₁ B₀ C₀ CD₂ BD₂ : Type} [Field k]
  [AddCommGroup A₁] [Module k A₁] [AddCommGroup AD₁] [Module k AD₁]
  [AddCommGroup B₁] [Module k B₁] [AddCommGroup BD₁] [Module k BD₁]
  [AddCommGroup B₀] [Module k B₀] [AddCommGroup C₀] [Module k C₀]
  [AddCommGroup CD₂] [Module k CD₂] [AddCommGroup BD₂] [Module k BD₂]
  (P : A₁ →ₗ[k] AD₁ →ₗ[k] k) (Q : B₁ →ₗ[k] BD₁ →ₗ[k] k)
  (R : CD₂ →ₗ[k] C₀ →ₗ[k] k) (T : BD₂ →ₗ[k] B₀ →ₗ[k] k)
  (i : A₁ →ₗ[k] B₁) (iD : BD₁ →ₗ[k] AD₁)
  (δ : C₀ →ₗ[k] A₁) (j : B₀ →ₗ[k] C₀)
  (δD : AD₁ →ₗ[k] CD₂) (jD : CD₂ →ₗ[k] BD₂)
  (hex₁ : LinearMap.range δ = LinearMap.ker i)
  (hex₀ : LinearMap.range j = LinearMap.ker δ)
  (hexD : LinearMap.range δD = LinearMap.ker jD)
  (hnat : ∀ x y, Q (i x) y = P x (iD y))
  (hend : ∀ z b, T (jD z) b = R z (j b))
  (hadj : ∀ y w, R (δD y) w = -P (δ w) y)
  (hQ : Function.Injective Q) (hT : Function.Injective T)
  (hR : Function.Surjective R)




include hex₁ hex₀ hexD hnat hend hadj hQ hT hR

/-- Exact original-object consumer of `lowDegreeDuality_left_injective`. -/
theorem actual_finite_duality_lowDegreeDuality_left_injective_source : Function.Injective P :=
  lowDegreeDuality_left_injective P Q R T i iD δ j δD jD hex₁ hex₀ hexD hnat hend hadj hQ hT hR

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]



variable (A B C : Rep.{0} k G)
  [Finite A] [Finite B] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  [TopologicalSpace (characterDualCoefficientRep C χ)]
  [DiscreteTopology (characterDualCoefficientRep C χ)]
  (φ : A →ₗ[k] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[k] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteCharacterDualInvariantConnecting_adjunction`. -/
theorem actual_finite_duality_finiteCharacterDualInvariantConnecting_adjunction_source
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : C.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing C χ hχ hC
      (continuousCoefficientConnectingMap
        (characterDualCoefficientRep C χ) (characterDualCoefficientRep B χ)
        (characterDualCoefficientRep A χ)
        (characterDualCoefficientMap B C χ ψ)
        (characterDualCoefficientMap_injective B C χ ψ hψ)
        (characterDualCoefficientMap_equivariant B C χ ψ hψρ)
        (characterDualCoefficientMap A B χ φ)
        (characterDualCoefficientMap_surjective A B χ φ hφ)
        (characterDualCoefficientMap_equivariant A B χ φ hφρ)
        (characterDualCoefficientSequence_exact A B C χ φ ψ hExact)
        (finiteCharacterDualAction_continuous C χ hC hχ)
        (finiteCharacterDualAction_continuous B χ hB hχ)
        (finiteCharacterDualAction_continuous A χ hA hχ) y) w =
      -continuousCharacterDualH1Cup A χ hχ hA
        (continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB w) y :=
  finiteCharacterDualInvariantConnecting_adjunction A B C χ hχ φ hφ hφρ ψ hψ hψρ hExact hA hB hC y w

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]



variable (A B C : Rep.{0} k G)
  [Finite A] [Finite B] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  [TopologicalSpace (characterDualCoefficientRep C χ)]
  [DiscreteTopology (characterDualCoefficientRep C χ)]
  (φ : A →ₗ[k] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[k] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))



variable (e₂ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
  (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)



attribute [local instance] characterDualSequenceContinuousSMul
include hφ hψ hφρ hψρ hExact

/-- Exact original-object consumer of `continuousCharacterDualH1_left_injective_of_exact`. -/
theorem actual_finite_duality_continuousCharacterDualH1_left_injective_of_exact_source
    (h₁ : Function.Injective ((continuousCharacterDualH1Cup B χ hχ hB).compr₂ e₂.toLinearMap))
    (h₂ : Function.Injective ((continuousCharacterDualH2InvariantPairing B χ hχ hB).compr₂ e₂.toLinearMap))
    (h₃ : Function.Surjective ((continuousCharacterDualH2InvariantPairing C χ hχ hC).compr₂ e₂.toLinearMap)) :
    Function.Injective ((continuousCharacterDualH1Cup A χ hχ hA).compr₂ e₂.toLinearMap) :=
  continuousCharacterDualH1_left_injective_of_exact A B C χ hχ φ hφ hφρ ψ hψ hψρ hExact hA hB hC e₂ h₁ h₂ h₃

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets finiteCoinducedCoefficientQuotient_finite


/-- Exact original-object consumer of `localCharacterDualH1ScalarCup_left_injective`. -/
theorem actual_finite_duality_localCharacterDualH1ScalarCup_left_injective_source (hq : (q : K) ≠ 0) :
    Function.Injective (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA) :=
  localCharacterDualH1ScalarCup_left_injective K Ω q χ hχ e heρ A hA hq

end

section

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) [Finite A]
  (χ : G →* k)



variable [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]
  (hχ : Continuous χ)
  [Finite (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterDualH1Cup_bidual`. -/
theorem actual_finite_duality_continuousCharacterDualH1Cup_bidual_source
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) :
    continuousCharacterDualH1Cup (characterDualCoefficientRep A χ) χ hχ
      (finiteCharacterDualAction_continuous A χ hA hχ) y (continuousCharacterBidualH1Equiv A χ hχ hA x) =
      -continuousCharacterDualH1Cup A χ hχ hA x y :=
  continuousCharacterDualH1Cup_bidual A χ hχ hA x y

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  localCharacterLineCorestrictionCosets finiteCoinducedCoefficientQuotient_finite


/-- Exact original-object consumer of `localCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_finite_duality_localCharacterDualH1ScalarCup_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localCharacterDualH1ScalarCup_isPerfPair K Ω q χ hχ e heρ A hA hq

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero


/-- Exact original-object consumer of `rationalPrimeCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_finite_duality_rationalPrimeCharacterDualH1ScalarCup_isPerfPair_source :
    (rationalPrimeCharacterDualH1ScalarCup p hp q A hA).IsPerfPair :=
  rationalPrimeCharacterDualH1ScalarCup_isPerfPair p hp q A hA

end

section

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  (A : Rep.{0} k G) (χ : G →* ZMod q)



variable [Finite A]



attribute [local instance] finiteScalarPrimeModule


/-- Exact original-object consumer of `finiteScalarTraceDualMap_surjective`. -/
theorem actual_extension_field_finiteScalarTraceDualMap_surjective_source : Function.Surjective (finiteScalarTraceDualMap q A χ) :=
  finiteScalarTraceDualMap_surjective q A χ

end

section

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



variable (χ : G →* ZMod q) (hχ : Continuous χ)



variable
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]



attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul
omit [Finite k] [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Exact original-object consumer of `finiteScalarTraceCharacter_equivariant`. -/
theorem actual_extension_field_finiteScalarTraceCharacter_equivariant_source (g : G) (a : k) :
    Algebra.trace (ZMod q) k
      ((finiteScalarPrimeRep q (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))).ρ g a) =
      (coefficientCharacterRep χ).ρ g (Algebra.trace (ZMod q) k a) :=
  finiteScalarTraceCharacter_equivariant q χ g a

end

section

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



variable (χ : G →* ZMod q) (hχ : Continuous χ)



variable
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]



attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteScalarTraceCharacterH2Map_cup`. -/
theorem actual_extension_field_finiteScalarTraceCharacterH2Map_cup_source
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ))) :
    finiteScalarTraceCharacterH2Map q χ hχ
      (continuousCharacterDualH1Cup A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        (finiteScalarCharacter_continuous q χ hχ) hA x y) =
      continuousCharacterDualH1Cup (finiteScalarPrimeRep q A) χ hχ hA
        (finiteScalarPrimeH1Equiv q A hA x) (finiteScalarTraceDualH1Equiv q A hA χ hχ y) :=
  finiteScalarTraceCharacterH2Map_cup q A hA χ hχ x y

end

section

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]



variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule
include e heρ

/-- Exact original-object consumer of `localFiniteScalarCharacterDualH1Cup_right_injective`. -/
theorem actual_extension_field_localFiniteScalarCharacterDualH1Cup_right_injective_source (hq : (q : K) ≠ 0) :
    Function.Injective (continuousCharacterDualH1Cup A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
      (finiteScalarCharacter_continuous q χ hχ) hA).flip :=
  localFiniteScalarCharacterDualH1Cup_right_injective K Ω q χ hχ e heρ A hA hq

end

section

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)



variable {ι : Type}
  (b : @Module.Basis ι (ZMod q) k _ _ (finiteScalarCharacterPrimeRep q χ (k := k)).hV2)



attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul
attribute [local instance 1100] Rep.hV2
attribute [local instance 1100] finiteScalarLinePrimeModule


/-- Exact original-object consumer of `finiteScalarCharacterH2Extend_coordinate`. -/
theorem actual_extension_field_finiteScalarCharacterH2Extend_coordinate_source (i : ι) (a : k)
    (u : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ)) :
    continuousCoefficientH2Map
      (finiteScalarCharacterPrimeRep q χ (k := k))
      (coefficientCharacterRep χ) (b.coord i) continuous_of_discreteTopology
      (scalarCoefficientCoordinate_equivariant
        (finiteScalarCharacterPrimeRep q χ (k := k)) χ b (finiteScalarCharacterPrime_action q χ) i)
      (coefficientCharacterAction_continuous
        ((algebraMap (ZMod q) k).toMonoidHom.comp χ) (finiteScalarCharacter_continuous q χ hχ))
      (coefficientCharacterAction_continuous χ hχ)
      (finiteScalarCharacterPrimeH2Equiv q χ hχ (a • finiteScalarCharacterH2Extend q χ hχ u)) =
      b.coord i a • u :=
  finiteScalarCharacterH2Extend_coordinate q χ hχ b i a u

end

section

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[ZMod q] ZMod q)



variable [Finite k]



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteScalarCharacterH2Span_bijective`. -/
theorem actual_extension_field_finiteScalarCharacterH2Span_bijective_source :
    Function.Bijective (finiteScalarCharacterH2Span q χ hχ σ (k := k)) :=
  finiteScalarCharacterH2Span_bijective q χ hχ σ

end

section

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)


variable [Finite k]
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[ZMod q] ZMod q)



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteScalarCharacterH2ScalarEquiv_trace`. -/
theorem actual_extension_field_finiteScalarCharacterH2ScalarEquiv_trace_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (coefficientCharacterAction_continuous _ (finiteScalarCharacter_continuous q χ hχ))) :
    σ (finiteScalarTraceCharacterH2Map q χ hχ (k := k) x) =
      Algebra.trace (ZMod q) k (finiteScalarCharacterH2ScalarEquiv q χ hχ σ x) :=
  finiteScalarCharacterH2ScalarEquiv_trace q χ hχ σ x

end

section

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]



variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



variable (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule


/-- Exact original-object consumer of `localFiniteScalarCharacterDualH1ScalarCup_isPerfPair`. -/
theorem actual_extension_field_localFiniteScalarCharacterDualH1ScalarCup_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localFiniteScalarCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localFiniteScalarCharacterDualH1ScalarCup_isPerfPair K Ω q χ hχ e heρ A hA hq

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (k : Type) [Field k] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k]



variable [Finite k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]






/-- Exact original-object consumer of `rationalPrimeFiniteScalarCyclotomicH2Equiv_eq_zero_iff`. -/
theorem actual_extension_field_rationalPrimeFiniteScalarCyclotomicH2Equiv_eq_zero_iff_source
    (x : ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous)) :
    rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k x = 0 ↔ x = 0 :=
  rationalPrimeFiniteScalarCyclotomicH2Equiv_eq_zero_iff p hp q k x

end

section

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (hn : (Fintype.card ι : k) ≠ 0)
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `matrixTraceZeroCharacterH1Cup_dual`. -/
theorem actual_extension_field_matrixTraceZeroCharacterH1Cup_dual_source
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    matrixTraceZeroCharacterH1Cup ρ hρ χ hχ x y =
      -continuousCharacterDualH1Cup (matrixTraceZeroAdjointRep ρ) χ hχ
        (matrixTraceZeroAdjointAction_continuous ρ hρ)
        (continuousTraceZeroH1GeneralEquiv ρ hρ y)
        (matrixTraceZeroCharacterDualH1Equiv hn ρ hρ χ hχ x) :=
  matrixTraceZeroCharacterH1Cup_dual hn ρ hρ χ hχ x y

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {k : Type} [Field k] [Finite k] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} k Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero


/-- Exact original-object consumer of `rationalPrimeFiniteScalarCharacterDualH1Cup_isPerfPair`. -/
theorem actual_extension_field_rationalPrimeFiniteScalarCharacterDualH1Cup_isPerfPair_source :
    (rationalPrimeFiniteScalarCharacterDualH1Cup p hp q A hA).IsPerfPair :=
  rationalPrimeFiniteScalarCharacterDualH1Cup_isPerfPair p hp q A hA

end

section

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)



variable (hn : (Fintype.card ι : k) ≠ 0)
  [TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]



variable [Module.Finite k (ContinuousTraceZeroAdjointH1 ρ hρ)]



attribute [local instance] characterDualSequenceContinuousSMul
include hn

/-- Exact original-object consumer of `matrixTraceZeroNormalizedH1Cup_isPerfPair`. -/
theorem actual_extension_field_matrixTraceZeroNormalizedH1Cup_isPerfPair_source
    (hdual : ((continuousCharacterDualH1Cup (matrixTraceZeroAdjointRep ρ) χ hχ
      (matrixTraceZeroAdjointAction_continuous ρ hρ)).compr₂ σ.toLinearMap).IsPerfPair) :
    (matrixTraceZeroNormalizedH1Cup ρ hρ χ hχ σ).IsPerfPair :=
  matrixTraceZeroNormalizedH1Cup_isPerfPair ρ hρ χ hχ σ hn hdual

end

section

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι k) (hρ : Continuous ρ)



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `rationalPrimeFiniteScalarTraceH1Cup_isPerfPair`. -/
theorem actual_extension_field_rationalPrimeFiniteScalarTraceH1Cup_isPerfPair_source
    (hn : (Fintype.card ι : k) ≠ 0) :
    (rationalPrimeFiniteScalarTraceH1Cup p hp q ρ hρ).IsPerfPair :=
  rationalPrimeFiniteScalarTraceH1Cup_isPerfPair p hp q ρ hρ hn

end

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ)



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `rationalPrimeTraceH1ScalarCup_isPerfPair`. -/
theorem actual_extension_field_rationalPrimeTraceH1ScalarCup_isPerfPair_source
    (hn : (Fintype.card ι : ZMod q) ≠ 0) :
    (rationalPrimeTraceH1ScalarCup p hp q ρ hρ).IsPerfPair :=
  rationalPrimeTraceH1ScalarCup_isPerfPair p hp q ρ hρ hn

end

section

variable {k A₂ AD₀ B₁ BD₁ C₁ CD₁ : Type} [Field k]
  [AddCommGroup A₂] [Module k A₂] [AddCommGroup AD₀] [Module k AD₀]
  [AddCommGroup B₁] [Module k B₁] [AddCommGroup BD₁] [Module k BD₁]
  [AddCommGroup C₁] [Module k C₁] [AddCommGroup CD₁] [Module k CD₁]
  (P : A₂ →ₗ[k] AD₀ →ₗ[k] k) (Q : B₁ →ₗ[k] BD₁ →ₗ[k] k)
  (R : C₁ →ₗ[k] CD₁ →ₗ[k] k)
  (j : B₁ →ₗ[k] C₁) (δ : C₁ →ₗ[k] A₂)
  (jD : CD₁ →ₗ[k] BD₁) (δD : AD₀ →ₗ[k] CD₁)
  (hex : LinearMap.range j = LinearMap.ker δ)
  (hexD : LinearMap.range δD = LinearMap.ker jD)
  (hnat : ∀ b z, Q b (jD z) = R (j b) z)
  (hadj : ∀ u w, P (δ u) w = R u (δD w))
  (hQ : Function.Surjective Q) (hR : Function.Injective R)




include hex hexD hnat hadj hQ hR

/-- Exact original-object consumer of `lowDegreeH2_connecting_left_zero`. -/
theorem actual_local_h2_endpoint_lowDegreeH2_connecting_left_zero_source (u : C₁) (hu : ∀ w, P (δ u) w = 0) :
    δ u = 0 :=
  lowDegreeH2_connecting_left_zero P Q R j δ jD δD hex hexD hnat hadj hQ hR u hu

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterH2DualInvariantPairing_apply`. -/
theorem actual_local_h2_endpoint_continuousCharacterH2DualInvariantPairing_apply_source
    (x : ContinuousRepresentationH2 A hA) (w : (characterDualCoefficientRep A χ).ρ.invariants) :
    continuousCharacterH2DualInvariantPairing A χ hχ hA x w =
    continuousInvariantRightH2Map A (characterDualCoefficientRep A χ)
      (coefficientCharacterRep χ) (characterDualEvaluation A χ)
      (characterDualEvaluation_equivariant A χ)
      continuous_of_discreteTopology hA
      (coefficientCharacterAction_continuous χ hχ) w x :=
  continuousCharacterH2DualInvariantPairing_apply A χ hχ hA x w

end

section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep.{0} k G) [Finite B] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  [TopologicalSpace (characterDualCoefficientRep C χ)]
  [DiscreteTopology (characterDualCoefficientRep C χ)]
  (φ : A →ₗ[k] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[k] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (e₂ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)



attribute [local instance] characterDualSequenceContinuousSMul
include hφ hψ hψρ hExact

/-- Exact original-object consumer of `continuousCharacterH2_left_zero_of_effacement`. -/
theorem actual_local_h2_endpoint_continuousCharacterH2_left_zero_of_effacement_source
    (hQ : Function.Surjective ((continuousCharacterDualH1Cup B χ hχ hB).compr₂ e₂.toLinearMap))
    (hR : Function.Injective ((continuousCharacterDualH1Cup C χ hχ hC).compr₂ e₂.toLinearMap))
    (x : ContinuousRepresentationH2 A hA)
    (hx : continuousCoefficientH2Map A B φ continuous_of_discreteTopology hφρ hA hB x = 0)
    (hann : ∀ w, e₂ (continuousCharacterH2DualInvariantPairing A χ hχ hA x w) = 0) : x = 0 :=
  continuousCharacterH2_left_zero_of_effacement A B C χ hχ φ hφ hφρ ψ hψ hψρ hExact hA hB hC e₂ hQ hR x hx hann

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul
  finiteEffacementCoefficientTopology finiteEffacementCoefficientDiscrete finiteEffacementCosets


/-- Exact original-object consumer of `localCharacterH2DualInvariant_left_zero`. -/
theorem actual_local_h2_endpoint_localCharacterH2DualInvariant_left_zero_source (hq : (q : K) ≠ 0)
    (x : ContinuousRepresentationH2 A hA)
    (hx : ∀ w, localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ
      (continuousCharacterH2DualInvariantPairing A χ hχ hA x w) = 0) : x = 0 :=
  localCharacterH2DualInvariant_left_zero K Ω q χ hχ e heρ A hA hq x hx

end

section

variable {k G : Type} [Field k] [Group G]
  (A : Rep.{0} k G) [Finite A] (χ : G →* k)



variable [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  (hχ : Continuous χ) (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `continuousCharacterH2DualInvariantPairing_bidual`. -/
theorem actual_local_h2_endpoint_continuousCharacterH2DualInvariantPairing_bidual_source
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : A.ρ.invariants) :
    continuousCharacterH2DualInvariantPairing (characterDualCoefficientRep A χ) χ hχ
      (finiteCharacterDualAction_continuous A χ hA hχ) x (characterBidualInvariantEquiv A χ w) =
      continuousCharacterDualH2InvariantPairing A χ hχ hA x w :=
  continuousCharacterH2DualInvariantPairing_bidual A χ hχ hA x w

end

section

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



attribute [local instance] characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `localCharacterDualH2InvariantScalarPairing_isPerfPair`. -/
theorem actual_local_h2_endpoint_localCharacterDualH2InvariantScalarPairing_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localCharacterDualH2InvariantScalarPairing_isPerfPair K Ω q χ hχ e heρ A hA hq

end

section

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (χ : G →* ZMod q) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]



attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul


/-- Exact original-object consumer of `finiteScalarTraceCharacterH2Map_invariantPairing`. -/
theorem actual_local_h2_endpoint_finiteScalarTraceCharacterH2Map_invariantPairing_source
    (x : ContinuousRepresentationH2
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ))) (w : A.ρ.invariants) :
    finiteScalarTraceCharacterH2Map q χ hχ
      (continuousCharacterDualH2InvariantPairing A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        (finiteScalarCharacter_continuous q χ hχ) hA x w) =
      continuousCharacterDualH2InvariantPairing (finiteScalarPrimeRep q A) χ hχ hA
        (finiteScalarTraceDualH2Equiv q A hA χ hχ x) (finiteScalarPrimeInvariantEquiv q A w) :=
  finiteScalarTraceCharacterH2Map_invariantPairing q A hA χ hχ x w

end

section

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule


/-- Exact original-object consumer of `localFiniteScalarCharacterDualH2InvariantPairing_isPerfPair`. -/
theorem actual_local_h2_endpoint_localFiniteScalarCharacterDualH2InvariantPairing_isPerfPair_source (hq : (q : K) ≠ 0) :
    (localFiniteScalarCharacterDualH2InvariantPairing K Ω q χ hχ e heρ A hA).IsPerfPair :=
  localFiniteScalarCharacterDualH2InvariantPairing_isPerfPair K Ω q χ hχ e heρ A hA hq

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {k : Type} [Field k] [Finite k] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} k Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero


/-- Exact original-object consumer of `rationalPrimeFiniteScalarCharacterDualH2Pairing_isPerfPair`. -/
theorem actual_local_h2_endpoint_rationalPrimeFiniteScalarCharacterDualH2Pairing_isPerfPair_source :
    (rationalPrimeFiniteScalarCharacterDualH2Pairing p hp q A hA).IsPerfPair :=
  rationalPrimeFiniteScalarCharacterDualH2Pairing_isPerfPair p hp q A hA

end

section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {ζ : rationalPrimeLocalClosure p hp} (hζ : IsPrimitiveRoot ζ q)







/-- Exact original-object consumer of `rationalPrimePrimitiveRootCoefficientEquiv_equivariant`. -/
theorem actual_arithmetic_root_rationalPrimePrimitiveRootCoefficientEquiv_equivariant_source
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) (x : ZMod q) :
    rationalPrimePrimitiveRootCoefficientEquiv p hp q hζ
      ((coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).ρ g x) =
      (galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).ρ g
        (rationalPrimePrimitiveRootCoefficientEquiv p hp q hζ x) :=
  rationalPrimePrimitiveRootCoefficientEquiv_equivariant p hp q hζ g x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)



variable (p : ℕ) (hp : p.Prime)







/-- Exact original-object consumer of `rationalArithmeticLocalRootCoefficientEquiv_compatible`. -/
theorem actual_arithmetic_root_rationalArithmeticLocalRootCoefficientEquiv_compatible_source (x : ZMod q) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    (((Additive.toMul (Rep.toAdditive
      (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp x)) :
        rootsOfUnity q (rationalPrimeLocalClosure p hp)) : (rationalPrimeLocalClosure p hp)ˣ) :
        rationalPrimeLocalClosure p hp) =
      rationalArithmeticLocalEmbedding a ((rationalArithmeticPrimitiveRoot a q hqa) ^ x.val) :=
  rationalArithmeticLocalRootCoefficientEquiv_compatible a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)





/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rootsOfUnity q (rationalUnramifiedExtension a)) :=
  galoisRootOfUnityMulDistribMulAction (K := ℚ) (Ω := rationalUnramifiedExtension a) q



/-- Exact original-object consumer of `rationalArithmeticRootCoefficientEquiv_local`. -/
theorem actual_arithmetic_root_rationalArithmeticRootCoefficientEquiv_local_source
    (p : ℕ) (hp : p.Prime) (x : ZMod q) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    rationalArithmeticLocalEmbedding a
      (((Additive.toMul (Rep.toAdditive
        (rationalArithmeticRootCoefficientEquiv a q hqa x)) : rootsOfUnity q U) : Uˣ) : U) =
      (((Additive.toMul (Rep.toAdditive
        (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp x)) :
          rootsOfUnity q (rationalPrimeLocalClosure p hp)) :
            (rationalPrimeLocalClosure p hp)ˣ) : rationalPrimeLocalClosure p hp) :=
  rationalArithmeticRootCoefficientEquiv_local a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)





/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootMapAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootMapAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rootsOfUnity q (rationalUnramifiedExtension a)) :=
  galoisRootOfUnityMulDistribMulAction (K := ℚ) (Ω := rationalUnramifiedExtension a) q



/-- Exact original-object consumer of `rationalArithmeticRootLocalEquiv_equivariant`. -/
theorem actual_arithmetic_root_rationalArithmeticRootLocalEquiv_equivariant_source
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (x : rationalArithmeticRootRepresentation a q) :
    rationalArithmeticRootLocalEquiv a q hqa p hp
      ((rationalArithmeticRootRepresentation a q).ρ
        (rationalPrimeArithmeticRestriction a p hp g) x) =
      (galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).ρ g
        (rationalArithmeticRootLocalEquiv a q hqa p hp x) :=
  rationalArithmeticRootLocalEquiv_equivariant a q hqa p hp g x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)



variable [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]





/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticRootH2Algebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticGlobalRootContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootRepresentation a q).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩



/-- Exact original-object consumer of `rationalArithmeticRootH2Restriction_compatible`. -/
theorem actual_arithmetic_root_rationalArithmeticRootH2Restriction_compatible_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticRootH2Restriction a q hqa p hp
      (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) =
      rationalArithmeticLocalCyclotomicH2RootEquiv a q hqa p hp
        (rationalPrimeCyclotomicH2Restriction a q hqa p hp x) :=
  rationalArithmeticRootH2Restriction_compatible a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)



variable (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)





/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticUnitMapAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticUnitMapAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rationalUnramifiedExtension a)ˣ :=
  inferInstanceAs (MulDistribMulAction
    Gal(rationalUnramifiedExtension a / ℚ) (rationalUnramifiedExtension a)ˣ)



/-- Exact original-object consumer of `rationalArithmeticUnitLocalMap_kummer`. -/
theorem actual_arithmetic_root_rationalArithmeticUnitLocalMap_kummer_source
    (x : rationalArithmeticRootRepresentation a q) :
    rationalArithmeticUnitLocalMap a p hp (rationalArithmeticKummerInclusion a q x) =
      (galoisKummerInclusion (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q).hom.toLinearMap
        (rationalArithmeticRootLocalEquiv a q hqa p hp x) :=
  rationalArithmeticUnitLocalMap_kummer a p hp q hqa x

end

section

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)



variable [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



variable (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]



attribute [local instance] arithmeticGlobalRootContinuousSMul

/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticUnitH2Algebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'



/-- The exact original coefficient structure used by this consumer. -/
local instance arithmeticGlobalUnitContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitRepresentation a).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩



/-- Exact original-object consumer of `rationalArithmeticUnitH2Restriction_kummer`. -/
theorem actual_arithmetic_root_rationalArithmeticUnitH2Restriction_kummer_source
    (x : ContinuousRepresentationH2 (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootAction_continuous a q)) :
    rationalArithmeticUnitH2Restriction a p hp (rationalArithmeticKummerH2Inclusion a q x) =
      galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q
        (rationalArithmeticRootH2Restriction a q hqa p hp x) :=
  rationalArithmeticUnitH2Restriction_kummer a p hp q hqa x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



variable [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]



attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `rationalArithmeticLocalH2ScalarEquiv_global_invariant`. -/
theorem actual_arithmetic_root_rationalArithmeticLocalH2ScalarEquiv_global_invariant_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp
      (rationalPrimeCyclotomicH2Restriction a q hqa p hp x)) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalArithmeticUnitH2Restriction a p hp
          (rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x))) :=
  rationalArithmeticLocalH2ScalarEquiv_global_invariant a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]







/-- Exact original-object consumer of `rationalArithmeticLocalH2ScalarEquiv_comparison`. -/
theorem actual_arithmetic_root_rationalArithmeticLocalH2ScalarEquiv_comparison_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous)) :
    rationalArithmeticLocalH2ScalarEquiv a q hqa p hp x =
      rationalArithmeticLocalNormalizationScalar a q hqa p hp *
        rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q x :=
  rationalArithmeticLocalH2ScalarEquiv_comparison a q hqa p hp x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))



attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero



/-- Exact original-object consumer of `rationalArithmeticLocalH1ScalarCup_isPerfPair`. -/
theorem actual_arithmetic_root_rationalArithmeticLocalH1ScalarCup_isPerfPair_source :
    (rationalArithmeticLocalH1ScalarCup a q hqa p hp A hA).IsPerfPair :=
  rationalArithmeticLocalH1ScalarCup_isPerfPair a q hqa p hp A hA

end

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q)) (hσ : Continuous σ)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]



attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul



/-- Exact original-object consumer of `rationalArithmeticCoherentTraceCup_global_invariant`. -/
theorem actual_arithmetic_root_rationalArithmeticCoherentTraceCup_global_invariant_source
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    let χP := rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)
    let j := rationalPrimeArithmeticRestriction a p hp
    rationalCyclicInvariant q (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp
      (matrixTraceZeroCharacterH1Cup (σ.comp j.toMonoidHom) (hσ.comp j.continuous)
        χP.toMonoidHom χP.continuous
        (rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ j.toMonoidHom j.continuous y))) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalArithmeticUnitH2Restriction a p hp
          (rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa
              (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)))) :=
  rationalArithmeticCoherentTraceCup_global_invariant a q hqa σ hσ p hp x y

end

section

variable {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
  [TopologicalSpace R] [TopologicalSpace G] [DiscreteTopology G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)







/-- Exact original-object consumer of `finiteCyclicH2PeriodNormMap_mk`. -/
theorem actual_unramified_h2_finiteCyclicH2PeriodNormMap_mk_source (c : continuousRepresentationCocyclesTwo A) :
    finiteCyclicH2PeriodNormMap A hA g hg (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteCyclicTwoCocycleInvariantPeriod A g c) :=
  finiteCyclicH2PeriodNormMap_mk A hA g hg c

end

section

variable {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
  [TopologicalSpace R] [TopologicalSpace G] [DiscreteTopology G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)





include hg

/-- Exact original-object consumer of `finiteCyclicH2_eq_zero_of_period_zero`. -/
theorem actual_unramified_h2_finiteCyclicH2_eq_zero_of_period_zero_source [Finite A] (hn : 1 < orderOf g)
    (c : continuousRepresentationCocyclesTwo A)
    (hc : representationCyclicTwoCochainPeriodSum A g (orderOf g) c.val = 0) :
    (Submodule.Quotient.mk c : ContinuousRepresentationH2 A hA) = 0 :=
  finiteCyclicH2_eq_zero_of_period_zero A hA g hg hn c hc

end

section

variable (q : ℕ) [Fact q.Prime]
  {G H : Type} [Group G] [CommGroup H] [Fintype H]
  [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace H] [DiscreteTopology H]
  (A : Rep (ZMod q) G) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (φ : H →* G) (g : G) (h : H) (hh : ∀ x, x ∈ Subgroup.zpowers h)
  (hφ : φ h = g) (n : ℕ) (hn : g ^ n = 1) (hnpos : 0 < n)
  (horder : orderOf h = n * q)





include hh hφ hn hnpos horder

/-- Exact original-object consumer of `finiteCyclicCharacteristicH2Inflation_eq_zero`. -/
theorem actual_unramified_h2_finiteCyclicCharacteristicH2Inflation_eq_zero_source
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA φ continuous_of_discreteTopology x = 0 :=
  finiteCyclicCharacteristicH2Inflation_eq_zero q A hA φ g h hh hφ n hn hnpos horder x

end

section

variable (K F E : Type) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
  [FiniteDimensional K E] [IsGalois K F] [IsGalois K E] [IsCyclic Gal(E/K)]
  (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) Gal(F/K)) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(F/K) × A => A.ρ z.1 z.2))



attribute [local instance] IsCyclic.commGroup



/-- Exact original-object consumer of `cyclicGaloisCharacteristicH2Inflation_eq_zero`. -/
theorem actual_unramified_h2_cyclicGaloisCharacteristicH2Inflation_eq_zero_source
    (hdegree : Module.finrank F E = q) (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (AlgEquiv.restrictNormalHom F : Gal(E/K) →* Gal(F/K))
      continuous_of_discreteTopology x = 0 :=
  cyclicGaloisCharacteristicH2Inflation_eq_zero K F E q A hA hdegree x

end

section

variable (K F E : Type) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
  [IsGalois K F] [IsGalois K E]
  [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[E]]
  (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) Gal(F/K)) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(F/K) × A => A.ρ z.1 z.2))







/-- Exact original-object consumer of `unramifiedCharacteristicH2Inflation_eq_zero`. -/
theorem actual_unramified_h2_unramifiedCharacteristicH2Inflation_eq_zero_source
    (hdegree : Module.finrank F E = q) (x : ContinuousRepresentationH2 A hA) :
    letI : FiniteDimensional K E := localField_field_module_finite
    continuousRepresentationH2Restriction A hA
      (AlgEquiv.restrictNormalHom F : Gal(E/K) →* Gal(F/K))
      continuous_of_discreteTopology x = 0 :=
  unramifiedCharacteristicH2Inflation_eq_zero K F E q A hA hdegree x

end

section

variable {G : Type} [Group G] [Finite G] [IsCyclic G]







/-- Exact original-object consumer of `finiteCyclicSubgroup_le_of_index_dvd`. -/
theorem actual_unramified_h2_finiteCyclicSubgroup_le_of_index_dvd_source (S T : Subgroup G)
    (h : T.index ∣ S.index) : S ≤ T :=
  finiteCyclicSubgroup_le_of_index_dvd S T h

end

section

variable {K E : Type} [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [IsCyclic Gal(E/K)]







/-- Exact original-object consumer of `cyclicGaloisIntermediateField_le_of_finrank_dvd`. -/
theorem actual_unramified_h2_cyclicGaloisIntermediateField_le_of_finrank_dvd_source
    (F L : IntermediateField K E) (h : Module.finrank K F ∣ Module.finrank K L) : F ≤ L :=
  cyclicGaloisIntermediateField_le_of_finrank_dvd F L h

end

section

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]







/-- Exact original-object consumer of `spectralUnramifiedStage_le_of_finrank_dvd`. -/
theorem actual_unramified_h2_spectralUnramifiedStage_le_of_finrank_dvd_source
    (E F : FiniteGaloisIntermediateField K Ω)
    (hE : SpectralStageUnramified K Ω E) (hF : SpectralStageUnramified K Ω F)
    (hdegree : Module.finrank K E ∣ Module.finrank K F) : E ≤ F :=
  spectralUnramifiedStage_le_of_finrank_dvd E F hE hF hdegree

end

section

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]







/-- Exact original-object consumer of `spectralUnramifiedStage_exists_prime_extension`. -/
theorem actual_unramified_h2_spectralUnramifiedStage_exists_prime_extension_source
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    (q : ℕ) [Fact q.Prime] :
    ∃ E : FiniteGaloisIntermediateField K Ω, ∃ hFE : F ≤ E,
      SpectralStageUnramified K Ω E ∧
        letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
        Module.finrank F E = q :=
  spectralUnramifiedStage_exists_prime_extension F hF q

end

section

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
  (q : ℕ) [Fact q.Prime] (A : Rep (ZMod q) Gal(F/K)) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(F/K) × A => A.ρ z.1 z.2))





include hF

/-- Exact original-object consumer of `spectralUnramifiedH2_exists_zero_inflation`. -/
theorem actual_unramified_h2_spectralUnramifiedH2_exists_zero_inflation_source :
    ∃ E : FiniteGaloisIntermediateField K Ω, ∃ hFE : F ≤ E,
      SpectralStageUnramified K Ω E ∧
        letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
        letI : IsScalarTower K F E := IsScalarTower.of_algHom (IntermediateField.inclusion hFE)
        ∀ x : ContinuousRepresentationH2 A hA,
          continuousRepresentationH2Restriction A hA
            (AlgEquiv.restrictNormalHom F : Gal(E/K) →* Gal(F/K))
            continuous_of_discreteTopology x = 0 :=
  spectralUnramifiedH2_exists_zero_inflation F hF q A hA

end

section

variable {R G H L : Type} [CommRing R] [Group G] [Group H] [Group L]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace L]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup L]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j) (k : L →* H) (hk : Continuous k)







/-- Exact original-object consumer of `continuousRepresentationH2Restriction_comp`. -/
theorem actual_unramified_h2_continuousRepresentationH2Restriction_comp_source
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA (j.comp k) (hj.comp hk) x =
      continuousRepresentationH2Restriction (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA) k hk
        (continuousRepresentationH2Restriction A hA j hj x) :=
  continuousRepresentationH2Restriction_comp A hA j hj k hk x

end

section

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
  (q : ℕ) [Fact q.Prime] (A : Rep (ZMod q) Gal(F/K)) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(F/K) × A => A.ρ z.1 z.2))





include hF

/-- Exact original-object consumer of `spectralUnramifiedH2_absolute_inflation_eq_zero`. -/
theorem actual_unramified_h2_spectralUnramifiedH2_absolute_inflation_eq_zero_source
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K))
      (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) x = 0 :=
  spectralUnramifiedH2_absolute_inflation_eq_zero F hF q A hA x

end

section

variable {R K Ω : Type} [CommRing R] [TopologicalSpace R]
  [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousSMul R A] (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))





include hA

/-- Exact original-object consumer of `continuousFiniteCoefficientTwoCocycle_exists_finiteField`. -/
theorem actual_unramified_h2_continuousFiniteCoefficientTwoCocycle_exists_finiteField_source
    (c : continuousRepresentationCocyclesTwo A) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → ∀ a : A, A.ρ u a = a) ∧
      (∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
        AlgEquiv.restrictNormalHom F v = 1 → c.val (g * u, h * v) = c.val (g, h)) :=
  continuousFiniteCoefficientTwoCocycle_exists_finiteField A hA c

end

section

variable {R K Ω : Type} [CommRing R] [Field K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) (F : FiniteGaloisIntermediateField K Ω)
  (hker : ∀ u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → ∀ a : A, A.ρ u a = a)







/-- Exact original-object consumer of `finiteStageCoefficientRepresentation_apply`. -/
theorem actual_unramified_h2_finiteStageCoefficientRepresentation_apply_source (g : Gal(Ω/K)) (a : A) :
    finiteStageCoefficientRepresentation A F hker (AlgEquiv.restrictNormalHom F g) a =
      A.ρ g a :=
  finiteStageCoefficientRepresentation_apply A F hker g a

end

section

variable {R K Ω : Type} [CommRing R] [TopologicalSpace R]
  [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (F : FiniteGaloisIntermediateField K Ω)
  (hker : ∀ u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → ∀ a : A, A.ρ u a = a)
  (c : continuousRepresentationCocyclesTwo A)
  (hperiod : ∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
    AlgEquiv.restrictNormalHom F v = 1 → c.val (g * u, h * v) = c.val (g, h))







/-- Exact original-object consumer of `continuousFiniteCoefficientTwoCocycle_exists_finite_descent`. -/
theorem actual_unramified_h2_continuousFiniteCoefficientTwoCocycle_exists_finite_descent_source [Finite A]
    (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2)) :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      ∃ ρ : Representation R Gal(E/K) A,
        ∃ d : continuousRepresentationCocyclesTwo (Rep.of ρ),
          (∀ g : Gal(Ω/K), ∀ a : A, ρ (AlgEquiv.restrictNormalHom E g) a = A.ρ g a) ∧
          (∀ g h : Gal(Ω/K), d.val (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h) =
            c.val (g, h)) :=
  continuousFiniteCoefficientTwoCocycle_exists_finite_descent A c hA

end

section

variable {R K Ω : Type} [CommRing R] [TopologicalSpace R]
  [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))







/-- Exact original-object consumer of `continuousFiniteCoefficientH2_exists_finite_stage`. -/
theorem actual_unramified_h2_continuousFiniteCoefficientH2_exists_finite_stage_source [Finite A]
    (x : ContinuousRepresentationH2 A hA) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ρ : Representation R Gal(F/K) A,
        ∃ hρ : ∀ g : Gal(Ω/K), ∀ a : A, ρ (AlgEquiv.restrictNormalHom F g) a = A.ρ g a,
          ∃ y : ContinuousRepresentationH2 (Rep.of ρ) continuous_of_discreteTopology,
            finiteCoefficientGaloisH2Inflation A hA F ρ hρ y = x :=
  continuousFiniteCoefficientH2_exists_finite_stage A hA x

end

section

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)







/-- Exact original-object consumer of `rationalArithmeticCyclotomicH2_exists_unramified_finite_stage`. -/
theorem actual_unramified_h2_rationalArithmeticCyclotomicH2_exists_unramified_finite_stage_source (ha : a ≠ 0)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    let A := coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
    let hA := coefficientCharacterAction_continuous _
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous
    ∃ F : FiniteGaloisIntermediateField ℚ U,
      letI : IsGalois ℚ F := F.isGalois
      (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        algebraMap (𝓞 ℚ) (𝓞 F) a ∉ w.asIdeal →
          (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1) ∧
      ∃ ρ : Representation (ZMod q) Gal(F/ℚ) A,
        ∃ hρ : ∀ g : Gal(U/ℚ), ∀ b : A, ρ ((AlgEquiv.restrictNormalHom F : Gal(U/ℚ) →* Gal(F/ℚ)) g) b = A.ρ g b,
          ∃ y : ContinuousRepresentationH2 (Rep.of ρ) continuous_of_discreteTopology,
            finiteCoefficientGaloisH2Inflation A hA F ρ hρ y = x :=
  rationalArithmeticCyclotomicH2_exists_unramified_finite_stage a q hqa ha x

end

section



variable (K E : Type) [Field K] [Field E] [Algebra K E] [ValuativeRel E]





/-- Exact original-object consumer of `originalIntegerToValuationIntegerMap_coe`. -/
theorem actual_arithmetic_support_originalIntegerToValuationIntegerMap_coe_source (x : 𝓞 K) :
    (originalIntegerToValuationIntegerMap K E x : E) = algebraMap K E (x : K) :=
  originalIntegerToValuationIntegerMap_coe K E x

end

section



variable (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E] [ValuativeRel E]
  (a : 𝓞 K) (ha : a ≠ 0) (hu : IsUnit (originalIntegerToValuationIntegerMap K E a))





/-- Exact original-object consumer of `originalLocalizedIntegerToValuationIntegerMap_coe`. -/
theorem actual_arithmetic_support_originalLocalizedIntegerToValuationIntegerMap_coe_source (x : originalLocalizedIntegers K a ha) :
    (originalLocalizedIntegerToValuationIntegerMap K E a ha hu x : E) = algebraMap K E (x : K) :=
  originalLocalizedIntegerToValuationIntegerMap_coe K E a ha hu x

end

section



variable (p : ℕ) (hp : p.Prime)





/-- Exact original-object consumer of `rationalPrimeOriginalInteger_isUnit`. -/
theorem actual_arithmetic_support_rationalPrimeOriginalInteger_isUnit_source (a : 𝓞 ℚ) (ha : ¬(p : 𝓞 ℚ) ∣ a) :
    IsUnit (originalIntegerToValuationIntegerMap ℚ (rationalPrimeLocalField p hp) a) :=
  rationalPrimeOriginalInteger_isUnit p hp a ha

end

section



variable (L M : Type) [Field L] [NumberField L] [Field M] [Algebra ℚ L]
  (p : ℕ) (hp : p.Prime)
  [Algebra (rationalPrimeLocalField p hp) M] [Algebra ℚ M] [Algebra L M]
  [IsScalarTower ℚ (rationalPrimeLocalField p hp) M] [IsScalarTower ℚ L M]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation M)]





/-- Exact original-object consumer of `rationalUnramifiedLocalCompositum_integer_unramified`. -/
theorem actual_arithmetic_support_rationalUnramifiedLocalCompositum_integer_unramified_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (hL : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 ℚ) (𝓞 L) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1)
    (htop : (algebraMap (rationalPrimeLocalField p hp) M).fieldRange ⊔
      (algebraMap L M).fieldRange = ⊤) :
    Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp] 𝒪[M] :=
  rationalUnramifiedLocalCompositum_integer_unramified L M p hp a ha hpa hL htop

end

section



variable {R K L Ω : Type} [Field R] [Field K] [Field L] [Field Ω]
  [Algebra R K] [Algebra R L] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [FiniteDimensional R L] [IsGalois R L]





/-- Exact original-object consumer of `embeddedFiniteGaloisCompositum_splitting_polynomial`. -/
theorem actual_arithmetic_support_embeddedFiniteGaloisCompositum_splitting_polynomial_source (i : L →ₐ[R] Ω) :
    ∃ q : Polynomial K, q.Separable ∧
      q.IsSplittingField K (IntermediateField.adjoin K (Set.range i)) :=
  embeddedFiniteGaloisCompositum_splitting_polynomial (K := K) i

end

section



variable {R K L Ω : Type} [Field R] [Field K] [Field L] [Field Ω]
  [Algebra R K] [Algebra R L] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [FiniteDimensional R L] [IsGalois R L] (i : L →ₐ[R] Ω)





/-- Exact original-object consumer of `embeddedFiniteGaloisCompositum_ranges`. -/
theorem actual_arithmetic_support_embeddedFiniteGaloisCompositum_ranges_source :
    (algebraMap K (embeddedFiniteGaloisCompositum (K := K) i)).fieldRange ⊔
      (embeddedFiniteGaloisCompositumInclusion (K := K) i).toRingHom.fieldRange = ⊤ :=
  embeddedFiniteGaloisCompositum_ranges (K := K) i

end

section


attribute [local instance] Dubon2026.arithmeticFiniteLocalStageAlgebra Dubon2026.arithmeticFiniteLocalStageGalois Dubon2026.arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)



variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)





/-- Exact original-object consumer of `rationalArithmeticFiniteLocalStage_ranges`. -/
theorem actual_arithmetic_support_rationalArithmeticFiniteLocalStage_ranges_source :
    (algebraMap (rationalPrimeLocalField p hp) (rationalArithmeticFiniteLocalStage a F p hp)).fieldRange ⊔
      (rationalArithmeticFiniteLocalStageInclusion a F p hp).toRingHom.fieldRange = ⊤ :=
  rationalArithmeticFiniteLocalStage_ranges a F p hp

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)
  [ValuativeRel (rationalArithmeticFiniteLocalStage a F p hp)]
  [TopologicalSpace (rationalArithmeticFiniteLocalStage a F p hp)]
  [IsNonarchimedeanLocalField (rationalArithmeticFiniteLocalStage a F p hp)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
    (ValuativeRel.valuation (rationalArithmeticFiniteLocalStage a F p hp))]





/-- Exact original-object consumer of `arithmeticFiniteLocalStage_integer_unramified`. -/
theorem actual_arithmetic_support_arithmeticFiniteLocalStage_integer_unramified_source (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a) :
    Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
      𝒪[rationalArithmeticFiniteLocalStage a F p hp] :=
  arithmeticFiniteLocalStage_integer_unramified a F p hp ha hpa

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))





/-- Exact original-object consumer of `arithmeticFiniteLocalStageH2_absolute_inflation_eq_zero`. -/
theorem actual_arithmetic_support_arithmeticFiniteLocalStageH2_absolute_inflation_eq_zero_source
    (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a) (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (AlgEquiv.restrictNormalHom (rationalArithmeticFiniteLocalStage a F p hp) :
        Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
          Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp))
      (InfiniteGalois.restrictNormalHom_continuous
        (rationalArithmeticFiniteLocalStage a F p hp).toIntermediateField) x = 0 :=
  arithmeticFiniteLocalStageH2_absolute_inflation_eq_zero a F p hp q A hA ha hpa x

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)





/-- Exact original-object consumer of `rationalArithmeticFiniteLocalRestriction_square`. -/
theorem actual_arithmetic_support_rationalArithmeticFiniteLocalRestriction_square_source :
    (AlgEquiv.restrictNormalHom F).comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom =
      (rationalArithmeticFiniteLocalRestriction a F p hp).comp
        (AlgEquiv.restrictNormalHom (rationalArithmeticFiniteLocalStage a F p hp) :
          Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
            Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp)) :=
  rationalArithmeticFiniteLocalRestriction_square a F p hp

end

section



variable {R G Q H L : Type} [CommRing R]
  [Group G] [Group Q] [Group H] [Group L]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace Q]
  [TopologicalSpace H] [TopologicalSpace L]
  [IsTopologicalGroup G] [IsTopologicalGroup Q]
  [IsTopologicalGroup H] [IsTopologicalGroup L]
  (A : Rep R G) (B : Rep R Q)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : Q × B => B.ρ z.1 z.2))
  (π : G →* Q) (hπ : Continuous π) (j : H →* G) (hj : Continuous j)
  (k : L →* Q) (hk : Continuous k) (r : H →* L) (hr : Continuous r)
  (hsq : π.comp j = k.comp r)
  (φ : B →ₗ[R] A) (hφ : Continuous φ)
  (hφρ : ∀ g b, φ (B.ρ (π g) b) = A.ρ g (φ b))



include hsq

/-- Exact original-object consumer of `continuousH2RestrictionSquare_eq_zero`. -/
theorem actual_arithmetic_support_continuousH2RestrictionSquare_eq_zero_source
    (x : ContinuousRepresentationH2 B hB)
    (hx : continuousRepresentationH2Restriction (restrictedCoefficientRep B k)
      (restrictedCoefficientAction_continuous B k hk hB) r hr
      (continuousRepresentationH2Restriction B hB k hk x) = 0) :
    continuousRepresentationH2Restriction A hA j hj
      (continuousCoefficientH2Map (restrictedCoefficientRep B π) A φ hφ hφρ
        (restrictedCoefficientAction_continuous B π hπ hB) hA
        (continuousRepresentationH2Restriction B hB π hπ x)) = 0 :=
  continuousH2RestrictionSquare_eq_zero A B hA hB π hπ j hj k hk r hr hsq φ hφ hφρ x hx

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra
attribute [local instance] Dubon2026.arithmeticFiniteStageH2Galois

variable (a : 𝓞 ℚ)



variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (A : Rep.{0} (ZMod q) Gal(rationalUnramifiedExtension a / ℚ))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(rationalUnramifiedExtension a / ℚ) × A => A.ρ z.1 z.2))
  (ρ : Representation (ZMod q) Gal(F/ℚ) A)
  (hρ : ∀ g : Gal(rationalUnramifiedExtension a / ℚ), ∀ b : A,
    ρ (AlgEquiv.restrictNormalHom F g) b = A.ρ g b)





/-- Exact original-object consumer of `arithmeticFiniteStageH2Restriction_eq_zero`. -/
theorem actual_arithmetic_support_arithmeticFiniteStageH2Restriction_eq_zero_source (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (y : ContinuousRepresentationH2 (Rep.of ρ) continuous_of_discreteTopology) :
    continuousRepresentationH2Restriction A hA
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalPrimeArithmeticRestriction a p hp).continuous
      (finiteCoefficientGaloisH2Inflation A hA F ρ hρ y) = 0 :=
  arithmeticFiniteStageH2Restriction_eq_zero a F p hp q A hA ρ hρ ha hpa y

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra arithmeticFiniteStageH2Galois

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (A : Rep.{0} (ZMod q) Gal(rationalUnramifiedExtension a / ℚ))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(rationalUnramifiedExtension a / ℚ) × A => A.ρ z.1 z.2))





/-- Exact original-object consumer of `arithmeticH2Restriction_eq_zero`. -/
theorem actual_arithmetic_support_arithmeticH2Restriction_eq_zero_source (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalPrimeArithmeticRestriction a p hp).continuous x = 0 :=
  arithmeticH2Restriction_eq_zero a p hp q A hA ha hpa x

end

section

attribute [local instance] arithmeticFiniteLocalStageAlgebra arithmeticFiniteStageH2Galois

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)





/-- Exact original-object consumer of `rationalPrimeCyclotomicH2Restriction_eq_zero`. -/
theorem actual_arithmetic_support_rationalPrimeCyclotomicH2Restriction_eq_zero_source (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalPrimeCyclotomicH2Restriction a q hqa p hp x = 0 :=
  rationalPrimeCyclotomicH2Restriction_eq_zero a q hqa p hp ha hpa x

end

section







/-- Exact original-object consumer of `rationalExceptionalPrimeSet_finite`. -/
theorem actual_arithmetic_support_rationalExceptionalPrimeSet_finite_source (a : 𝓞 ℚ) (ha : a ≠ 0) :
    {p : Nat.Primes | (p.val : 𝓞 ℚ) ∣ a}.Finite :=
  rationalExceptionalPrimeSet_finite a ha

end

section



variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)





/-- Exact original-object consumer of `rationalArithmeticCyclotomicH2_finite_support`. -/
theorem actual_arithmetic_support_rationalArithmeticCyclotomicH2_finite_support_source (ha : a ≠ 0)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    {p : Nat.Primes | rationalPrimeCyclotomicH2Restriction a q hqa p.val p.property x ≠ 0}.Finite :=
  rationalArithmeticCyclotomicH2_finite_support a q hqa ha x

end

end
noncomputable section
open Classical IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section



variable (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) Gal(ℂ/ℝ))
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(ℂ/ℝ) × A => A.ρ z.1 z.2))





/-- Exact original-object consumer of `realPlaceFiniteCoefficientH2_eq_zero`. -/
theorem actual_global_norm_input_realPlaceFiniteCoefficientH2_eq_zero_source (hq : 2 < q)
    (x : ContinuousRepresentationH2 A hA) : x = 0 :=
  realPlaceFiniteCoefficientH2_eq_zero q A hA hq x

end

section



variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) (rationalArithmeticGaloisGroup a))
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))





/-- Exact original-object consumer of `rationalRealArithmeticH2Restriction_eq_zero`. -/
theorem actual_global_norm_input_rationalRealArithmeticH2Restriction_eq_zero_source (hq : 2 < q)
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (rationalRealArithmeticRestriction a).toMonoidHom
      (rationalRealArithmeticRestriction a).continuous x = 0 :=
  rationalRealArithmeticH2Restriction_eq_zero a q A hA hq x

end

section


attribute [local instance] Dubon2026.arithmeticPrimeInvariantRootTopology Dubon2026.arithmeticPrimeInvariantRootDiscrete Dubon2026.arithmeticPrimeInvariantUnitTopology Dubon2026.arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)





/-- Exact original-object consumer of `rationalArithmeticPrimeH2Invariant_finite_support`. -/
theorem actual_global_norm_input_rationalArithmeticPrimeH2Invariant_finite_support_source (ha : a ≠ 0)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    (Function.support (fun p : Nat.Primes => rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x)).Finite :=
  rationalArithmeticPrimeH2Invariant_finite_support a q hqa ha x

end

section



variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)





/-- Exact original-object consumer of `rationalArithmeticFiniteH2InvariantSum_apply`. -/
theorem actual_global_norm_input_rationalArithmeticFiniteH2InvariantSum_apply_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticFiniteH2InvariantSum a q hqa ha x =
      ∑ p ∈ (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x).support,
        rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x :=
  rationalArithmeticFiniteH2InvariantSum_apply a q hqa ha x

end

section

attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  arithmeticPrimeInvariantRootTopology arithmeticPrimeInvariantRootDiscrete
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]





/-- Exact original-object consumer of `rationalArithmeticFiniteH2InvariantSum_unit_invariants`. -/
theorem actual_global_norm_input_rationalArithmeticFiniteH2InvariantSum_unit_invariants_source
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalArithmeticFiniteH2InvariantSum a q hqa ha x) =
      ∑ p ∈ (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x).support,
        rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x :=
  rationalArithmeticFiniteH2InvariantSum_unit_invariants a q hqa ha x

end

section







/-- Exact original-object consumer of `numberField_prime_classNumber_power_principal`. -/
theorem actual_global_norm_input_numberField_prime_classNumber_power_principal_source
    (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (v.asIdeal ^ NumberField.classNumber K).IsPrincipal :=
  numberField_prime_classNumber_power_principal K v

end

section







/-- Exact original-object consumer of `numberFieldPrimePowerGenerator_intValuation`. -/
theorem actual_global_norm_input_numberFieldPrimePowerGenerator_intValuation_source
    (K : Type*) [Field K] [NumberField K] (v w : HeightOneSpectrum (𝓞 K)) :
    w.intValuation (numberFieldPrimePowerGenerator K v) =
      WithZero.exp (if w = v then -(NumberField.classNumber K : ℤ) else 0) :=
  numberFieldPrimePowerGenerator_intValuation K v w

end

section







/-- Exact original-object consumer of `numberFieldPrimePowerSUnit_coordinate`. -/
theorem actual_global_norm_input_numberFieldPrimePowerSUnit_coordinate_source (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (v w : S) :
    sUnitValuationLinearMap S (Additive.ofMul (numberFieldPrimePowerSUnit K S v)) w =
      if w = v then -(NumberField.classNumber K : ℤ) else 0 :=
  numberFieldPrimePowerSUnit_coordinate K S v w

end

section







/-- Exact original-object consumer of `numberField_unit_finrank`. -/
theorem actual_global_norm_input_numberField_unit_finrank_source (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℤ (Additive (𝓞 K)ˣ) = NumberField.Units.rank K :=
  numberField_unit_finrank K

end

section



variable (K : Type*) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))





/-- Exact original-object consumer of `numberField_sUnit_finrank`. -/
theorem actual_global_norm_input_numberField_sUnit_finrank_source (hS : S.Finite) :
    Module.finrank ℤ (Additive (S.unit K)) = NumberField.Units.rank K + S.ncard :=
  numberField_sUnit_finrank K S hS

end

section







/-- Exact original-object consumer of `finiteGeneratedAbelian_exists_rank_decomposition`. -/
theorem actual_global_norm_input_finiteGeneratedAbelian_exists_rank_decomposition_source
    (G : Type*) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (d : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (G ≃+ (Fin d → ℤ) × T) ∧ Module.finrank ℤ G = d :=
  finiteGeneratedAbelian_exists_rank_decomposition G

end

section







/-- Exact original-object consumer of `finiteGeneratedAbelian_nsmul_index`. -/
theorem actual_global_norm_input_finiteGeneratedAbelian_nsmul_index_source
    (G : Type*) [AddCommGroup G] [AddGroup.FG G] (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ Module.finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) n).ker :=
  finiteGeneratedAbelian_nsmul_index G n hn

end

section



variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]





/-- Exact original-object consumer of `sUnitPowerKernel_card`. -/
theorem actual_global_norm_input_sUnitPowerKernel_card_source (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (powMonoidHom (α := S.unit K) n).ker = n :=
  sUnitPowerKernel_card S n hn ζ hζ

end

section







/-- Exact original-object consumer of `numberField_sUnit_powerQuotient_card`. -/
theorem actual_global_norm_input_numberField_sUnit_powerQuotient_card_source
    (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range) =
      n ^ (Fintype.card (NumberField.InfinitePlace K) + S.ncard) :=
  numberField_sUnit_powerQuotient_card K S hS n hn ζ hζ

end


open Classical IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]



/-- Exact original-object consumer of `sUnit_mem_power_range_iff`. -/
theorem actual_sunit_kummer_sUnit_mem_power_range_iff_source (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) (x : S.unit K) :
    x ∈ (powMonoidHom (α := S.unit K) n).range ↔
      x.val ∈ (powMonoidHom (α := Kˣ) n).range :=
  sUnit_mem_power_range_iff S n hn x

end

section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]



/-- Exact original-object consumer of `sUnitPowerQuotientToField_injective`. -/
theorem actual_sunit_kummer_sUnitPowerQuotientToField_injective_source (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) : Function.Injective (sUnitPowerQuotientToField (K := K) S n) :=
  sUnitPowerQuotientToField_injective S n hn

end

section



/-- Exact original-object consumer of `numberField_sUnit_radicalQuotient_card`. -/
theorem actual_sunit_kummer_numberField_sUnit_radicalQuotient_card_source
    (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card ((S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range : Subgroup Kˣ) ⧸
      ((powMonoidHom (α := Kˣ) n).range).subgroupOf
        (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range)) =
      n ^ (Fintype.card (NumberField.InfinitePlace K) + S.ncard) :=
  numberField_sUnit_radicalQuotient_card K S hS n hn ζ hζ

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `originalKummerRadicalField_isGalois`. -/
theorem actual_sunit_kummer_originalKummerRadicalField_isGalois_source [IsGalois K Ω]
    (n : ℕ) (Δ : Subgroup Kˣ) :
    IsGalois K (originalKummerRadicalField (Ω := Ω) n Δ) :=
  originalKummerRadicalField_isGalois (Ω := Ω) n Δ

end

section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `galoisRadicalRatio_pow_fixes`. -/
theorem actual_sunit_kummer_galoisRadicalRatio_pow_fixes_source (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) (a : Kˣ) (β : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) (g : Gal(L/K)) :
    (g ^ n) • β = β :=
  galoisRadicalRatio_pow_fixes n hζ a β hβ g

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `originalKummerRadicalField_galois_pow_eq_one`. -/
theorem actual_sunit_kummer_originalKummerRadicalField_galois_pow_eq_one_source
    (n : ℕ) [NeZero n] (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    (σ : Gal(originalKummerRadicalField (Ω := Ω) n Δ/K)) : σ ^ n = 1 :=
  originalKummerRadicalField_galois_pow_eq_one n hζ Δ σ

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `originalKummerClassRoot_pow`. -/
theorem actual_sunit_kummer_originalKummerClassRoot_pow_source [IsAlgClosed Ω] (n : ℕ) (hn : 0 < n)
    (Δ : Subgroup Kˣ) (c : originalKummerClassSubgroup n Δ) :
    originalKummerClassRoot (Ω := Ω) n hn Δ c ^ n =
      Units.map (algebraMap K (originalKummerRadicalField (Ω := Ω) n Δ)).toMonoidHom
        (originalKummerClassRepresentative n Δ c).val :=
  originalKummerClassRoot_pow (Ω := Ω) n hn Δ c

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]



/-- Exact original-object consumer of `originalKummerRadicalField_finiteDimensional`. -/
theorem actual_sunit_kummer_originalKummerRadicalField_finiteDimensional_source [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    FiniteDimensional K (originalKummerRadicalField (Ω := Ω) n Δ) :=
  originalKummerRadicalField_finiteDimensional (Ω := Ω) n hn hζ Δ

end

section

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `numberField_sUnit_kummerField_finiteDimensional`. -/
theorem actual_sunit_kummer_numberField_sUnit_kummerField_finiteDimensional_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) :
    FiniteDimensional K (originalKummerRadicalField (Ω := Ω) n
      (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range)) :=
  numberField_sUnit_kummerField_finiteDimensional K Ω S hS n hn hζ

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]



/-- Exact original-object consumer of `originalKummerClassCharacter_mul`. -/
theorem actual_sunit_kummer_originalKummerClassCharacter_mul_source (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    (c d : originalKummerClassSubgroup n Δ) :
    originalKummerClassCharacter (Ω := Ω) n hn hζ Δ (c * d) =
      originalKummerClassCharacter n hn hζ Δ c *
        originalKummerClassCharacter n hn hζ Δ d :=
  originalKummerClassCharacter_mul (Ω := Ω) n hn hζ Δ c d

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]



/-- Exact original-object consumer of `originalKummerClassPairing_injective`. -/
theorem actual_sunit_kummer_originalKummerClassPairing_injective_source [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ) :
    Function.Injective (originalKummerClassPairing (Ω := Ω) n hn hζ Δ) :=
  originalKummerClassPairing_injective (Ω := Ω) n hn hζ Δ

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]



/-- Exact original-object consumer of `originalKummerRadicalField_finrank`. -/
theorem actual_sunit_kummer_originalKummerRadicalField_finrank_source [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    Module.finrank K (originalKummerRadicalField (Ω := Ω) n Δ) =
      Nat.card (originalKummerClassSubgroup n Δ) :=
  originalKummerRadicalField_finrank (Ω := Ω) n hn hζ Δ

end

section

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `numberField_sUnit_kummerField_finrank`. -/
theorem actual_sunit_kummer_numberField_sUnit_kummerField_finrank_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank K (originalKummerRadicalField (Ω := Ω) n
      (S.unit K ⊔ (powMonoidHom (α := Kˣ) n).range)) =
      n ^ (Fintype.card (NumberField.InfinitePlace K) + S.ncard) :=
  numberField_sUnit_kummerField_finrank K Ω S hS n hn ζ hζ

end


end
noncomputable section
open Classical IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]



/-- Exact original-object consumer of `exists_finite_sUnit_support`. -/
theorem actual_kummer_containment_exists_finite_sUnit_support_source (s : Finset Kˣ) :
    ∃ S : Finset (HeightOneSpectrum R), ∀ x ∈ s, x ∈ (S : Set (HeightOneSpectrum R)).unit K :=
  exists_finite_sUnit_support (R := R) s

end

section

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]



/-- Exact original-object consumer of `finiteAbelianGalois_exists_generating_radicals`. -/
theorem actual_kummer_containment_finiteAbelianGalois_exists_generating_radicals_source
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (hexp : ∀ g : Gal(L/K), g ^ n = 1) :
    ∃ (a : (Gal(L/K) →* Kˣ) → Kˣ) (β : (Gal(L/K) →* Kˣ) → Lˣ),
      (∀ χ, β χ ^ n = Units.map (algebraMap K L).toMonoidHom (a χ)) ∧
      (∀ χ g, g • β χ / β χ = Units.map (algebraMap K L).toMonoidHom (χ g)) ∧
      IntermediateField.adjoin K (Set.range fun χ => (β χ).val) = ⊤ :=
  finiteAbelianGalois_exists_generating_radicals n hn hζ hexp

end

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `finiteAbelian_exists_sUnit_kummer_containment`. -/
theorem actual_kummer_containment_finiteAbelian_exists_sUnit_kummer_containment_source
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (hexp : ∀ g : Gal(E/K), g ^ n = 1)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      E ≤ originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range) :=
  finiteAbelian_exists_sUnit_kummer_containment E n hn hζ hexp S₀

end

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `numberField_exists_sUnit_kummer_restriction`. -/
theorem actual_kummer_containment_numberField_exists_sUnit_kummer_restriction_source
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ) (hn : 1 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ g : Gal(E/K), g ^ n = 1)
    (r : ℕ) (hcard : Nat.card Gal(E/K) = n ^ r)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (hE : E ≤ originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)),
      S₀ ⊆ S ∧
      let N := originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)
      letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
      letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
      let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
      Function.Surjective f ∧
        r ≤ Fintype.card (NumberField.InfinitePlace K) + S.card ∧
        Nat.card f.ker = n ^ (Fintype.card (NumberField.InfinitePlace K) + S.card - r) :=
  numberField_exists_sUnit_kummer_restriction E n hn ζ hζ hexp r hcard S₀

end


open Classical NumberField IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldPrincipalIdele_mem_supported_iff`. -/
theorem actual_supported_idele_numberFieldPrincipalIdele_mem_supported_iff_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    numberFieldPrincipalIdele K x ∈ numberFieldSupportedIdeles K S ↔ x ∈ S.unit K :=
  numberFieldPrincipalIdele_mem_supported_iff K S x

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldSupportedIdeleClassMap_ker`. -/
theorem actual_supported_idele_numberFieldSupportedIdeleClassMap_ker_source
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    (numberFieldSupportedIdeleClassMap K S).ker =
      (numberFieldSupportedPrincipalIdele K S).range :=
  numberFieldSupportedIdeleClassMap_ker K S

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldIdeleOrder_principal`. -/
theorem actual_supported_idele_numberFieldIdeleOrder_principal_source (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldIdeleOrder K (numberFieldPrincipalIdele K x) v =
      FractionalIdeal.count K v (toPrincipalIdeal (𝓞 K) K x).val :=
  numberFieldIdeleOrder_principal K x v

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldIdeleIdeal_principal`. -/
theorem actual_supported_idele_numberFieldIdeleIdeal_principal_source (x : Kˣ) :
    numberFieldIdeleIdeal K (numberFieldPrincipalIdele K x) = toPrincipalIdeal (𝓞 K) K x :=
  numberFieldIdeleIdeal_principal K x

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberField_exists_finite_principal_idele_support`. -/
theorem actual_supported_idele_numberField_exists_finite_principal_idele_support_source
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ∃ x : Kˣ,
        a / numberFieldPrincipalIdele K x ∈ numberFieldSupportedIdeles K S :=
  numberField_exists_finite_principal_idele_support K S₀

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberField_exists_supportedIdeleQuotientEquiv`. -/
theorem actual_supported_idele_numberField_exists_supportedIdeleQuotientEquiv_source
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      Nonempty (numberFieldSupportedIdeles K S ⧸
        (numberFieldSupportedPrincipalIdele K S).range ≃* OriginalNumberFieldIdeleClassGroup K) :=
  numberField_exists_supportedIdeleQuotientEquiv K S₀

end



open Classical NumberField IsDedekindDomain
open scoped NumberField ValuativeRel nonZeroDivisors
section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisPlaceEquiv_mul`. -/
theorem actual_galois_support_numberFieldGaloisPlaceEquiv_mul_source (σ τ : Gal(L/K)) (v : HeightOneSpectrum (𝓞 L)) :
    numberFieldGaloisPlaceEquiv K L (σ * τ) v =
      numberFieldGaloisPlaceEquiv K L σ (numberFieldGaloisPlaceEquiv K L τ v) :=
  numberFieldGaloisPlaceEquiv_mul K L σ τ v

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisPlace_valuation`. -/
theorem actual_galois_support_numberFieldGaloisPlace_valuation_source (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    (numberFieldGaloisPlaceEquiv K L σ v).valuation L (σ x) = v.valuation L x :=
  numberFieldGaloisPlace_valuation K L σ v x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberField_exists_finite_galoisStable_support`. -/
theorem actual_galois_support_numberField_exists_finite_galoisStable_support_source [FiniteDimensional K L]
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S :=
  numberField_exists_finite_galoisStable_support K L S₀

end

section



/-- Exact original-object consumer of `numberField_exists_galoisStable_idele_support`. -/
theorem actual_galois_support_numberField_exists_galoisStable_idele_support_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      (∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap L S) :=
  numberField_exists_galoisStable_idele_support K L S₀

end


open NumberField IsDedekindDomain UniformSpace
open scoped NumberField Topology
section

variable {A B Γ : Type*} [Field A] [Field B] [LinearOrderedCommGroupWithZero Γ]
  [Valued A Γ] [Valued B Γ]



/-- Exact original-object consumer of `valuationPreservingRingEquiv_uniformContinuous`. -/
theorem actual_equivariant_idele_valuationPreservingRingEquiv_uniformContinuous_source (f : A ≃+* B)
    (h : ∀ x : A, Valued.v (f x) = (Valued.v x : Γ)) : UniformContinuous f :=
  valuationPreservingRingEquiv_uniformContinuous f h

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisCompletion_algebraMap`. -/
theorem actual_equivariant_idele_numberFieldGaloisCompletion_algebraMap_source (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    numberFieldGaloisCompletion K L σ v (algebraMap L (v.adicCompletion L) x) =
      algebraMap L ((numberFieldGaloisPlaceEquiv K L σ v).adicCompletion L) (σ x) :=
  numberFieldGaloisCompletion_algebraMap K L σ v x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisCompletion_valuation`. -/
theorem actual_equivariant_idele_numberFieldGaloisCompletion_valuation_source (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) :
    Valued.v (numberFieldGaloisCompletion K L σ v x) =
      (Valued.v x : WithZero (Multiplicative ℤ)) :=
  numberFieldGaloisCompletion_valuation K L σ v x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisLocalTransport_mul`. -/
theorem actual_equivariant_idele_numberFieldGaloisLocalTransport_mul_source (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L))
    (hτ : numberFieldGaloisPlaceEquiv K L τ v = u)
    (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)
    (hστ : numberFieldGaloisPlaceEquiv K L (σ * τ) v = w)
    (x : v.adicCompletion L) :
    numberFieldGaloisLocalTransport K L (σ * τ) v w hστ x =
      numberFieldGaloisLocalTransport K L σ u w hσ
        (numberFieldGaloisLocalTransport K L τ v u hτ x) :=
  numberFieldGaloisLocalTransport_mul K L σ τ v u w hτ hσ hστ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldFiniteAdeleGaloisMap_algebraMap`. -/
theorem actual_equivariant_idele_numberFieldFiniteAdeleGaloisMap_algebraMap_source (σ : Gal(L/K)) (x : L) :
    numberFieldFiniteAdeleGaloisMap K L σ
      (algebraMap L (FiniteAdeleRing (𝓞 L) L) x) =
        algebraMap L (FiniteAdeleRing (𝓞 L) L) (σ x) :=
  numberFieldFiniteAdeleGaloisMap_algebraMap K L σ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldFiniteAdeleGaloisMap_mul`. -/
theorem actual_equivariant_idele_numberFieldFiniteAdeleGaloisMap_mul_source (σ τ : Gal(L/K))
    (a : FiniteAdeleRing (𝓞 L) L) :
    numberFieldFiniteAdeleGaloisMap K L (σ * τ) a =
      numberFieldFiniteAdeleGaloisMap K L σ (numberFieldFiniteAdeleGaloisMap K L τ a) :=
  numberFieldFiniteAdeleGaloisMap_mul K L σ τ a

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisArchimedeanTransport_algebraMap`. -/
theorem actual_equivariant_idele_numberFieldGaloisArchimedeanTransport_algebraMap_source (σ : Gal(L/K))
    (v w : InfinitePlace L) (h : σ • v = w) (x : L) :
    numberFieldGaloisArchimedeanTransport K L σ v w h (algebraMap L v.Completion x) =
      algebraMap L w.Completion (σ x) :=
  numberFieldGaloisArchimedeanTransport_algebraMap K L σ v w h x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisArchimedeanTransport_mul`. -/
theorem actual_equivariant_idele_numberFieldGaloisArchimedeanTransport_mul_source (σ τ : Gal(L/K))
    (v u w : InfinitePlace L) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : v.Completion) :
    numberFieldGaloisArchimedeanTransport K L (σ * τ) v w hστ x =
      numberFieldGaloisArchimedeanTransport K L σ u w hσ
        (numberFieldGaloisArchimedeanTransport K L τ v u hτ x) :=
  numberFieldGaloisArchimedeanTransport_mul K L σ τ v u w hτ hσ hστ x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldInfiniteAdeleGaloisMap_mul`. -/
theorem actual_equivariant_idele_numberFieldInfiniteAdeleGaloisMap_mul_source (σ τ : Gal(L/K)) (a : InfiniteAdeleRing L) :
    numberFieldInfiniteAdeleGaloisMap K L (σ * τ) a =
      numberFieldInfiniteAdeleGaloisMap K L σ (numberFieldInfiniteAdeleGaloisMap K L τ a) :=
  numberFieldInfiniteAdeleGaloisMap_mul K L σ τ a

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldPrincipalIdele_galois`. -/
theorem actual_equivariant_idele_numberFieldPrincipalIdele_galois_source (σ : Gal(L/K)) (x : Lˣ) :
    numberFieldIdeleGaloisMap K L σ (numberFieldPrincipalIdele L x) =
      numberFieldPrincipalIdele L (σ • x) :=
  numberFieldPrincipalIdele_galois K L σ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldIdeleClassGaloisMap_mul`. -/
theorem actual_equivariant_idele_numberFieldIdeleClassGaloisMap_mul_source (σ τ : Gal(L/K))
    (a : OriginalNumberFieldIdeleClassGroup L) :
    numberFieldIdeleClassGaloisMap K L (σ * τ) a =
      numberFieldIdeleClassGaloisMap K L σ (numberFieldIdeleClassGaloisMap K L τ a) :=
  numberFieldIdeleClassGaloisMap_mul K L σ τ a

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]


variable (S : Set (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)


/-- Exact original-object consumer of `numberFieldSupportedIdeleClassMap_galois`. -/
theorem actual_equivariant_idele_numberFieldSupportedIdeleClassMap_galois_source :
    letI := numberFieldSupportedIdeleGaloisAction K L S hS
    letI := numberFieldIdeleClassGaloisAction K L
    ∀ (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S),
      numberFieldSupportedIdeleClassMap L S (σ • a) =
        σ • numberFieldSupportedIdeleClassMap L S a :=
  numberFieldSupportedIdeleClassMap_galois K L S hS

end

section



/-- Exact original-object consumer of `numberField_exists_equivariant_supported_idele_sequence`. -/
theorem actual_equivariant_idele_numberField_exists_equivariant_supported_idele_sequence_source
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∃ hS : ∀ (σ : Gal(L/K)) v,
        v ∈ (S : Set (HeightOneSpectrum (𝓞 L))) ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S,
      Function.Injective (numberFieldSupportedPrincipalIdele L S) ∧
      (numberFieldSupportedIdeleClassMap L S).ker =
        (numberFieldSupportedPrincipalIdele L S).range ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap L S) ∧
      (letI := numberFieldSUnitGaloisAction K L S hS
       letI := numberFieldSupportedIdeleGaloisAction K L S hS
       ∀ (σ : Gal(L/K)) (x : (S : Set (HeightOneSpectrum (𝓞 L))).unit L),
         numberFieldSupportedPrincipalIdele L S (σ • x) =
           σ • numberFieldSupportedPrincipalIdele L S x) ∧
      (letI := numberFieldSupportedIdeleGaloisAction K L S hS
       letI := numberFieldIdeleClassGaloisAction K L
       ∀ (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S),
         numberFieldSupportedIdeleClassMap L S (σ • a) =
           σ • numberFieldSupportedIdeleClassMap L S a) :=
  numberField_exists_equivariant_supported_idele_sequence K L S₀

end


end
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical Topology
section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]



/-- Exact original-object consumer of `sUnitOrdinaryUnitEmbedding_range`. -/
theorem actual_reduced_log_sUnitOrdinaryUnitEmbedding_range_source (S : Set (HeightOneSpectrum R)) :
    (sUnitOrdinaryUnitEmbedding (K := K) S).range = (sUnitValuations (K := K) S).ker :=
  sUnitOrdinaryUnitEmbedding_range (R := R) (K := K) S

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitReducedLog_finite_zero_ordinary`. -/
theorem actual_reduced_log_sUnitReducedLog_finite_zero_ordinary_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (hx : (sUnitReducedLog K S x).2 = 0) :
    ∃ u : (𝓞 K)ˣ, sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u = x.toMul :=
  sUnitReducedLog_finite_zero_ordinary K S x hx

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitReducedLog_eq_zero_iff`. -/
theorem actual_reduced_log_sUnitReducedLog_eq_zero_iff_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitReducedLog K S x = 0 ↔
      ∃ u : (𝓞 K)ˣ, u ∈ Units.torsion K ∧
        sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u = x.toMul :=
  sUnitReducedLog_eq_zero_iff K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitReducedLogLattice_discrete`. -/
theorem actual_reduced_log_sUnitReducedLogLattice_discrete_source : DiscreteTopology (sUnitReducedLogLattice K S) :=
  sUnitReducedLogLattice_discrete K S

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitReducedLogLattice_isZLattice`. -/
theorem actual_reduced_log_sUnitReducedLogLattice_isZLattice_source :
    letI := sUnitReducedLogLattice_discrete K S
    IsZLattice ℝ (sUnitReducedLogLattice K S) :=
  sUnitReducedLogLattice_isZLattice K S

end


open scoped BigOperators
section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnit_sum_log_absoluteValues_eq_zero`. -/
theorem actual_full_log_sUnit_sum_log_absoluteValues_eq_zero_source
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    (∑ w : InfinitePlace K, w.mult * Real.log (w x.val.val)) +
      ∑ v : S, Real.log (NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val) = 0 :=
  sUnit_sum_log_absoluteValues_eq_zero K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnit_log_adicAbv_eq_coordinate`. -/
theorem actual_full_log_sUnit_log_adicAbv_eq_coordinate_source
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (v : S) :
    Real.log (NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val) =
      (sUnitValuationLinearMap (R := 𝓞 K) (K := K) S (Additive.ofMul x) v : ℝ) *
        Real.log (Ideal.absNorm v.val.asIdeal : ℝ) :=
  sUnit_log_adicAbv_eq_coordinate K S x v

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitFullLogAmbient_mem_hyperplane`. -/
theorem actual_full_log_sUnitFullLogAmbient_mem_hyperplane_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitFullLogAmbient K S x ∈ SUnitLogHyperplane K S :=
  sUnitFullLogAmbient_mem_hyperplane K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitLogHyperplaneReduction_fullLog`. -/
theorem actual_full_log_sUnitLogHyperplaneReduction_fullLog_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitLogHyperplaneReduction K S (sUnitFullLog K S x) = sUnitReducedLog K S x :=
  sUnitLogHyperplaneReduction_fullLog K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitLogHyperplaneEquiv_fullLog`. -/
theorem actual_full_log_sUnitLogHyperplaneEquiv_fullLog_source
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitLogHyperplaneEquiv K S (sUnitFullLog K S x) = sUnitReducedLog K S x :=
  sUnitLogHyperplaneEquiv_fullLog K S x

end

section

variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `sUnitFullLogLattice_isZLattice`. -/
theorem actual_full_log_sUnitFullLogLattice_isZLattice_source :
    letI := sUnitFullLogLattice_discrete K S
    IsZLattice ℝ (sUnitFullLogLattice K S) :=
  sUnitFullLogLattice_isZLattice K S

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `numberFieldGaloisPlace_adicAbv`. -/
theorem actual_full_log_numberFieldGaloisPlace_adicAbv_source (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L (numberFieldGaloisPlaceEquiv K L σ v) (σ x) =
      NumberField.HeightOneSpectrum.adicAbv L v x :=
  numberFieldGaloisPlace_adicAbv K L σ v x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogCoordinateSum_galois`. -/
theorem actual_full_log_sUnitLogCoordinateSum_galois_source (σ : Gal(L/K)) (z : SUnitFullLogSpace L S) :
    letI := sUnitFullLogSpaceAction K L S hS
    sUnitLogCoordinateSum L S (σ • z) = sUnitLogCoordinateSum L S z :=
  sUnitLogCoordinateSum_galois K L S hS σ z

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitFullLog_galois`. -/
theorem actual_full_log_sUnitFullLog_galois_source (σ : Gal(L/K))
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    letI := sUnitAdditiveGaloisAction K L S hS
    letI := sUnitLogHyperplaneAction K L S hS
    sUnitFullLog L S (σ • x) = σ • sUnitFullLog L S x :=
  sUnitFullLog_galois K L S hS σ x

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



variable (K : Type) [Field K] [Algebra K L]
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogToLattice_galois`. -/
theorem actual_full_log_sUnitLogToLattice_galois_source (σ : Gal(L/K))
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    letI := sUnitAdditiveGaloisAction K L S hS
    letI := sUnitFullLogLatticeAction L S K hS
    sUnitLogToLattice L S (σ • x) = σ • sUnitLogToLattice L S x :=
  sUnitLogToLattice_galois L S K hS σ x

end


open Module Submodule
section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `sUnitLogDiagonalSplit_surjective`. -/
theorem actual_sunit_permutation_sUnitLogDiagonalSplit_surjective_source : Function.Surjective (sUnitLogDiagonalSplit L S) :=
  sUnitLogDiagonalSplit_surjective L S

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `sUnitLogProductLattice_mem`. -/
theorem actual_sunit_permutation_sUnitLogProductLattice_mem_source (z : SUnitLogHyperplane L S × ℝ) :
    z ∈ sUnitLogProductLattice L S ↔ z.1 ∈ sUnitFullLogLattice L S ∧ ∃ n : ℤ, (n : ℝ) = z.2 :=
  sUnitLogProductLattice_mem L S z

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



variable (K : Type) [Field K] [Algebra K L]
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitExtendedLogLattice_galois_mem`. -/
theorem actual_sunit_permutation_sUnitExtendedLogLattice_galois_mem_source (σ : Gal(L/K)) (z : SUnitFullLogSpace L S)
    (hz : z ∈ sUnitExtendedLogLattice L S) :
    letI := sUnitFullLogSpaceAction K L S hS
    σ • z ∈ sUnitExtendedLogLattice L S :=
  sUnitExtendedLogLattice_galois_mem L S K hS σ z hz

end

section

variable {ι : Type*} [Fintype ι]

/-- Exact original-object consumer of `norm_sub_latticeApproximation_le`. -/
theorem actual_sunit_permutation_norm_sub_latticeApproximation_le_source
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) :
    ‖x - (latticeApproximation L x : ι → ℝ)‖ ≤
      latticeApproximationRadius L :=
  norm_sub_latticeApproximation_le L x

end

section

variable {G : Type*} {ι : Type*}
variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `averagedLatticeVector_offDiagonal_bound`. -/
theorem actual_sunit_permutation_averagedLatticeVector_offDiagonal_bound_source
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) {i j : ι} (hji : j ≠ i) :
    |(averagedLatticeVector ρ L hL t i : ι → ℝ) j| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L :=
  averagedLatticeVector_offDiagonal_bound ρ L hL t hji

end

section

variable {G : Type*} {ι : Type*}
variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `averagedLatticeVector_linearIndependent`. -/
theorem actual_sunit_permutation_averagedLatticeVector_linearIndependent_source
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    LinearIndependent ℝ
      (fun i ↦
        (averagedLatticeVector ρ L hL
          (permutationLatticeScale L) i :
            ι → ℝ)) :=
  averagedLatticeVector_linearIndependent ρ L hL

end

section

variable {G : Type*} {ι : Type*}
variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `permutationSublattice_finite_quotient`. -/
theorem actual_sunit_permutation_permutationSublattice_finite_quotient_source
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Finite
      (L ⧸
        (permutationSublattice ρ L hL).comap
          L.subtype) :=
  permutationSublattice_finite_quotient ρ L hL

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnit_exists_finiteIndex_permutation_sublattice`. -/
theorem actual_sunit_permutation_sUnit_exists_finiteIndex_permutation_sublattice_source :
    letI := sUnitLogPlaceAction K L S hS
    letI := sUnitFullLogSpaceAction K L S hS
    ∃ T : Submodule ℤ (SUnitFullLogSpace L S),
      T ≤ sUnitExtendedLogLattice L S ∧ DiscreteTopology T ∧
      Submodule.span ℝ (T : Set (SUnitFullLogSpace L S)) = ⊤ ∧
      Finite (sUnitExtendedLogLattice L S ⧸ T.comap (sUnitExtendedLogLattice L S).subtype) ∧
      ∃ b : Module.Basis (SUnitLogPlace L S) ℤ T,
        ∀ (σ : Gal(L/K)) (p : SUnitLogPlace L S),
          σ • (b p : SUnitFullLogSpace L S) = (b (σ • p) : SUnitFullLogSpace L S) :=
  sUnit_exists_finiteIndex_permutation_sublattice K L S hS

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogRepHom_surjective`. -/
theorem actual_original_sunit_herbrand_sUnitLogRepHom_surjective_source : Function.Surjective (sUnitLogRepHom K L S hS).hom :=
  sUnitLogRepHom_surjective K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogarithmicShortComplex_shortExact`. -/
theorem actual_original_sunit_herbrand_sUnitLogarithmicShortComplex_shortExact_source :
    (sUnitLogarithmicShortComplex K L S hS).ShortExact :=
  sUnitLogarithmicShortComplex_shortExact K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogarithmicKernel_first_second_card_eq`. -/
theorem actual_original_sunit_herbrand_sUnitLogarithmicKernel_first_second_card_eq_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nat.card (groupCohomology (sUnitLogarithmicShortComplex K L S hS).X₁ 1) =
      Nat.card (groupCohomology (sUnitLogarithmicShortComplex K L S hS).X₁ 2) :=
  sUnitLogarithmicKernel_first_second_card_eq K L S hS σ hgen

end

section



/-- Exact original-object consumer of `bounded_positive_cardinality_recurrence`. -/
theorem actual_original_sunit_herbrand_bounded_positive_cardinality_recurrence_source
    (d : ℕ → ℕ) (a b bound : ℕ) (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, d n ≤ bound) (hrec : ∀ n, d (n + 1) * a = d n * b) : a = b :=
  bounded_positive_cardinality_recurrence d a b bound hpos hbound hrec

end

section



/-- Exact original-object consumer of `exact_cohomology_connecting_cardinality`. -/
theorem actual_original_sunit_herbrand_exact_cohomology_connecting_cardinality_source
    {R G : Type} [CommRing R] [Group G]
    (X : ShortComplex (Rep R G)) (hX : X.ShortExact) (n : ℕ) :
    Nat.card (groupCohomology X.X₂ (n + 1)) *
        Nat.card (groupCohomology.δ hX n (n + 1) rfl).hom.range *
        Nat.card (groupCohomology.δ hX (n + 1) (n + 1 + 1) rfl).hom.range =
      Nat.card (groupCohomology X.X₁ (n + 1)) * Nat.card (groupCohomology X.X₃ (n + 1)) :=
  exact_cohomology_connecting_cardinality X hX n

end

section

variable {G : Type} [CommGroup G] [Fintype G]
  (A : Rep ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)


include hg


/-- Exact original-object consumer of `cyclic_cohomology_positive_finite`. -/
theorem actual_original_sunit_herbrand_cyclic_cohomology_positive_finite_source [Finite (groupCohomology A 1)]
    [Finite (groupCohomology A 2)] (n : ℕ) : Finite (groupCohomology A (n + 1)) :=
  cyclic_cohomology_positive_finite A g hg n

end

section



/-- Exact original-object consumer of `cyclic_cohomology_herbrand_cardinality`. -/
theorem actual_original_sunit_herbrand_cyclic_cohomology_herbrand_cardinality_source
    {G : Type} [CommGroup G] [Fintype G]
    (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology X.X₁ 1)] [Finite (groupCohomology X.X₁ 2)]
    [Finite (groupCohomology X.X₃ 1)] [Finite (groupCohomology X.X₃ 2)] :
    Finite (groupCohomology X.X₂ 1) ∧ Finite (groupCohomology X.X₂ 2) ∧
      Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₁ 1) *
          Nat.card (groupCohomology X.X₃ 1) =
        Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₁ 2) *
          Nat.card (groupCohomology X.X₃ 2) :=
  cyclic_cohomology_herbrand_cardinality X hX g hg

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnit_logarithmic_herbrand_comparison`. -/
theorem actual_original_sunit_herbrand_sUnit_logarithmic_herbrand_comparison_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    [Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1)]
    [Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2)] :
    Finite (groupCohomology (sUnitOriginalRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitOriginalRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 2) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 1) =
        Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 1) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 2) :=
  sUnit_logarithmic_herbrand_comparison K L S hS σ hgen

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `sUnitLatticeProdIntToExtended_bijective`. -/
theorem actual_original_sunit_herbrand_sUnitLatticeProdIntToExtended_bijective_source : Function.Bijective (sUnitLatticeProdIntToExtended L S) :=
  sUnitLatticeProdIntToExtended_bijective L S

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLatticeProdIntToExtended_galois`. -/
theorem actual_original_sunit_herbrand_sUnitLatticeProdIntToExtended_galois_source (σ : Gal(L/K)) (x : sUnitFullLogLattice L S × ℤ) :
    letI : SMul Gal(L/K) (sUnitFullLogLattice L S × ℤ) :=
      (sUnitLatticeProdIntAction K L S hS).toMulAction.toSMul
    letI : SMul Gal(L/K) (sUnitExtendedLogLattice L S) :=
      (sUnitExtendedLogLatticeAction K L S hS).toMulAction.toSMul
    sUnitLatticeProdIntToExtended L S (σ • x) = σ • sUnitLatticeProdIntToExtended L S x :=
  sUnitLatticeProdIntToExtended_galois K L S hS σ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitExtendedProductRepIso_hom_apply`. -/
theorem actual_original_sunit_herbrand_sUnitExtendedProductRepIso_hom_apply_source (x : sUnitFullLogLattice L S × ℤ) :
    (sUnitExtendedProductRepIso K L S hS).hom.hom x = sUnitLatticeProdIntToExtended L S x :=
  sUnitExtendedProductRepIso_hom_apply K L S hS x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitLogLattice_cohomology_finite_of_extended`. -/
theorem actual_original_sunit_herbrand_sUnitLogLattice_cohomology_finite_of_extended_source (n : ℕ)
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) n)] :
    Finite (groupCohomology (sUnitLogLatticeRep K L S hS) n) :=
  sUnitLogLattice_cohomology_finite_of_extended K L S hS n

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnit_diagonal_herbrand_factor`. -/
theorem actual_original_sunit_herbrand_sUnit_diagonal_herbrand_factor_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 1)]
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 2)] :
    Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 2) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 1) =
        Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 1) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 2) * Nat.card Gal(L/K) :=
  sUnit_diagonal_herbrand_factor K L S hS σ hgen

end

section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (W : Submodule R A)
  (hW : ∀ g, W ≤ W.comap (A.ρ g))



/-- Exact original-object consumer of `stableSubmoduleShortComplex_shortExact`. -/
theorem actual_original_sunit_herbrand_stableSubmoduleShortComplex_shortExact_source :
    (stableSubmoduleShortComplex A W hW).ShortExact :=
  stableSubmoduleShortComplex_shortExact A W hW

end

section

variable {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G)
  (W : Submodule ℤ A) (hW : ∀ g, W ≤ W.comap (A.ρ g))



/-- Exact original-object consumer of `finiteIndex_herbrand_comparison`. -/
theorem actual_original_sunit_herbrand_finiteIndex_herbrand_comparison_source
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (A ⧸ W)]
    [Finite (groupCohomology (A.subrepresentation W hW) 1)]
    [Finite (groupCohomology (A.subrepresentation W hW) 2)] :
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 2) *
          Nat.card (groupCohomology (A.subrepresentation W hW) 1) =
        Nat.card (groupCohomology A 1) *
          Nat.card (groupCohomology (A.subrepresentation W hW) 2) :=
  finiteIndex_herbrand_comparison A W hW g hg

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitExtended_exists_permutation_subrepresentation`. -/
theorem actual_original_sunit_herbrand_sUnitExtended_exists_permutation_subrepresentation_source :
    letI := sUnitLogPlaceAction K L S hS
    ∃ W : Submodule ℤ (sUnitExtendedLogRep K L S hS),
      ∃ hW : ∀ σ, W ≤ W.comap ((sUnitExtendedLogRep K L S hS).ρ σ),
        Finite ((sUnitExtendedLogRep K L S hS) ⧸ W) ∧
        ∃ b : Module.Basis (SUnitLogPlace L S) ℤ W,
          ∀ (σ : Gal(L/K)) p,
            ((sUnitExtendedLogRep K L S hS).subrepresentation W hW).ρ σ (b p) =
              b (σ • p) :=
  sUnitExtended_exists_permutation_subrepresentation K L S hS

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]



/-- Exact original-object consumer of `permutationCoordinateRep_apply`. -/
theorem actual_original_sunit_herbrand_permutationCoordinateRep_apply_source (g : G) (x : ι → R) (i : ι) :
    (permutationCoordinateRep R G ι).ρ g x i = x (g⁻¹ • i) :=
  permutationCoordinateRep_apply R G ι g x i

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  [MulAction.IsPretransitive G ι] (i : ι)



/-- Exact original-object consumer of `transitivePermutationCoindIso_hom_apply`. -/
theorem actual_original_sunit_herbrand_transitivePermutationCoindIso_hom_apply_source (x : ι → R) (g : G) :
    ((transitivePermutationCoindIso R G ι i).hom.hom x).val g = x (g⁻¹ • i) :=
  transitivePermutationCoindIso_hom_apply R G ι i x g

end

section

variable (G ι : Type) [CommGroup G] [Fintype G] [IsCyclic G]
  [MulAction G ι] [MulAction.IsPretransitive G ι] (i : ι)

include i


/-- Exact original-object consumer of `transitivePermutation_second_cohomology_order`. -/
theorem actual_original_sunit_herbrand_transitivePermutation_second_cohomology_order_source :
    Finite (groupCohomology (permutationCoordinateRep ℤ G ι) 2) ∧
      Nat.card (groupCohomology (permutationCoordinateRep ℤ G ι) 2) =
        Nat.card (MulAction.stabilizer G i) :=
  transitivePermutation_second_cohomology_order G ι i

end

section

variable {R G ι : Type} [CommRing R] [Group G] (A : ι → Rep R G)



variable [Fintype ι]



/-- Exact original-object consumer of `originalFinitePi_cohomology_card`. -/
theorem actual_original_sunit_herbrand_originalFinitePi_cohomology_card_source (n : ℕ) :
    Nat.card (groupCohomology (originalPiRep A) n) =
      ∏ i, Nat.card (groupCohomology (A i) n) :=
  originalFinitePi_cohomology_card A n

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]



/-- Exact original-object consumer of `permutationOrbitRepIso_hom_apply`. -/
theorem actual_original_sunit_herbrand_permutationOrbitRepIso_hom_apply_source (x : ι → R)
    (ω : MulAction.orbitRel.Quotient G ι) (j : ω.orbit) :
    (permutationOrbitRepIso R G ι).hom.hom x ω j = x j.val :=
  permutationOrbitRepIso_hom_apply R G ι x ω j

end

section

variable (G ι : Type) [CommGroup G] [MulAction G ι]



variable [Fintype G] [IsCyclic G] [Fintype ι]



/-- Exact original-object consumer of `permutationCoordinate_second_cohomology_order`. -/
theorem actual_original_sunit_herbrand_permutationCoordinate_second_cohomology_order_source :
    Finite (groupCohomology (permutationCoordinateRep ℤ G ι) 2) ∧
      Nat.card (groupCohomology (permutationCoordinateRep ℤ G ι) 2) =
        ∏ ω : MulAction.orbitRel.Quotient G ι, Nat.card (MulAction.stabilizer G ω.out) :=
  permutationCoordinate_second_cohomology_order G ι

end

section

variable (G ι : Type) [CommGroup G] [Fintype G] [IsCyclic G]
  [MulAction G ι] [Fintype ι] (A : Rep ℤ G) (b : Module.Basis ι ℤ A)
  (hb : ∀ g i, A.ρ g (b i) = b (g • i))

include hb


/-- Exact original-object consumer of `permutedBasis_cohomology_orders`. -/
theorem actual_original_sunit_herbrand_permutedBasis_cohomology_orders_source :
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 1) = 1 ∧
      Nat.card (groupCohomology A 2) =
        ∏ ω : MulAction.orbitRel.Quotient G ι, Nat.card (MulAction.stabilizer G ω.out) :=
  permutedBasis_cohomology_orders G ι A b hb

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `sUnitExtended_log_lattice_herbrand`. -/
theorem actual_original_sunit_herbrand_sUnitExtended_log_lattice_herbrand_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 2) =
        Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  sUnitExtended_log_lattice_herbrand K L S hS σ hgen

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_sUnit_herbrand_cardinality`. -/
theorem actual_original_sunit_herbrand_original_sUnit_herbrand_cardinality_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (sUnitOriginalRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitOriginalRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 2) * Nat.card Gal(L/K) =
        Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  original_sUnit_herbrand_cardinality K L S hS σ hgen

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField ValuativeRel Classical
attribute [local instance 1100] Rep.hV2
attribute [local instance] numberFieldGaloisPlaceAction
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalSupportedClassRepHom_apply`. -/
theorem actual_supported_local_originalSupportedClassRepHom_apply_source (x : Additive (numberFieldSupportedIdeles L S)) :
    (originalSupportedClassRepHom K L S hS).hom x =
      Additive.ofMul (numberFieldSupportedIdeleClassMap L S x.toMul) :=
  originalSupportedClassRepHom_apply K L S hS x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_exists_supportedIdele_shortExact`. -/
theorem actual_supported_local_original_exists_supportedIdele_shortExact_source [FiniteDimensional K L]
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∃ hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S,
        (originalSupportedIdeleShortComplex K L S hS).ShortExact :=
  original_exists_supportedIdele_shortExact K L S₀

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_supported`. -/
theorem actual_supported_local_original_ideleClass_herbrand_of_supported_source
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    [Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 1)]
    [Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 2)]
    (hfactor : letI := sUnitLogPlaceAction K L S hS
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 2) =
        Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_supported K L S hS σ hgen hsurj hfactor

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



/-- Exact original-object consumer of `unramified_integer_unit_norm_preimages`. -/
theorem actual_supported_local_unramified_integer_unit_norm_preimages_source :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x :=
  unramified_integer_unit_norm_preimages K L

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [IsCyclic Gal(L/K)]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



/-- Exact original-object consumer of `unramified_integer_unit_positive_cohomology_zero`. -/
theorem actual_supported_local_unramified_integer_unit_positive_cohomology_zero_source (n : ℕ) (hn : 0 < n) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) n) :=
  unramified_integer_unit_positive_cohomology_zero K L n hn

end

section

variable {R G ι : Type} [CommRing R] [CommGroup G] [Fintype G]
  (A : ι → Rep R G)



/-- Exact original-object consumer of `cyclic_originalPi_cohomology_zero`. -/
theorem actual_supported_local_cyclic_originalPi_cohomology_zero_source
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) (hn : 0 < n)
    (hzero : ∀ i, Limits.IsZero (groupCohomology (A i) n)) :
    Limits.IsZero (groupCohomology (originalPiRep A) n) :=
  cyclic_originalPi_cohomology_zero A g hg n hn hzero

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `numberFieldSupportedIdeleCoordinateEquiv_finite`. -/
theorem actual_supported_local_numberFieldSupportedIdeleCoordinateEquiv_finite_source
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : numberFieldSupportedIdeles K S)
    (v : HeightOneSpectrum (𝓞 K)) :
    (numberFieldSupportedIdeleCoordinateEquiv K S a).2.val v =
      numberFieldIdeleFiniteComponent K v a.val :=
  numberFieldSupportedIdeleCoordinateEquiv_finite K S a v

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `numberFieldSupportedIdeleCoordinate_finite_galois`. -/
theorem actual_supported_local_numberFieldSupportedIdeleCoordinate_finite_galois_source
    (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S)
    (v w : HeightOneSpectrum (𝓞 L)) (h : numberFieldGaloisPlaceEquiv K L σ v = w) :
    (numberFieldSupportedIdeleCoordinateEquiv L S
      (numberFieldSupportedIdeleGaloisMap K L S hS σ a)).2.val w =
      Units.map (numberFieldGaloisLocalTransport K L σ v w h).toMonoidHom
        ((numberFieldSupportedIdeleCoordinateEquiv L S a).2.val v) :=
  numberFieldSupportedIdeleCoordinate_finite_galois K L S hS σ a v w h

end

section

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))



/-- Exact original-object consumer of `numberFieldSupportedFiniteFactorEquiv_outside`. -/
theorem actual_supported_local_numberFieldSupportedFiniteFactorEquiv_outside_source
    (x : numberFieldSupportedFiniteCoordinates K S)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    (((numberFieldSupportedFiniteFactorEquiv K S x).2 v).val : v.val.adicCompletion K) =
      (x.val v.val).val :=
  numberFieldSupportedFiniteFactorEquiv_outside K S x v

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)



/-- Exact original-object consumer of `transportedPiMap_apply`. -/
theorem actual_supported_local_transportedPiMap_apply_source (g : G) (x : ∀ i, M i) (i j : ι) (h : g • i = j) :
    transportedPiMap R G ι M T g x j = T g i j h (x i) :=
  transportedPiMap_apply R G ι M T g x i j h

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))
  [MulAction.IsPretransitive G ι] (i : ι)



/-- Exact original-object consumer of `transportedCoindHom_bijective`. -/
theorem actual_supported_local_transportedCoindHom_bijective_source :
    Function.Bijective (transportedCoindHom R G ι M T T_one T_mul i).hom :=
  transportedCoindHom_bijective R G ι M T T_one T_mul i

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]


/-- Exact original-object consumer of `numberFieldFiniteUnitTransport_mul`. -/
theorem actual_supported_local_numberFieldFiniteUnitTransport_mul_source (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L)) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : Additive (v.adicCompletion L)ˣ) :
    numberFieldFiniteUnitTransport K L (σ * τ) v w hστ x =
      numberFieldFiniteUnitTransport K L σ u w hσ
        (numberFieldFiniteUnitTransport K L τ v u hτ x) :=
  numberFieldFiniteUnitTransport_mul K L σ τ v u w hτ hσ hστ x

end

section

variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))



/-- Exact original-object consumer of `transportedOrbitProductIso_hom_apply`. -/
theorem actual_supported_local_transportedOrbitProductIso_hom_apply_source (x : ∀ i, M i)
    (ω : MulAction.orbitRel.Quotient G ι) (j : ω.orbit) :
    (transportedOrbitProductIso R G ι M T T_one T_mul).hom.hom x ω j = x j.val :=
  transportedOrbitProductIso_hom_apply R G ι M T T_one T_mul x ω j

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedUnitTransport_mul`. -/
theorem actual_supported_local_supportedUnrestrictedUnitTransport_mul_source :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ τ : Gal(L/K)) (p q r : SUnitLogPlace L S) (hτ : τ • p = q) (hσ : σ • q = r)
      (hστ : (σ * τ) • p = r) (x : supportedUnrestrictedUnitModule L S p),
      supportedUnrestrictedUnitTransport K L S hS (σ * τ) p r hστ x =
        supportedUnrestrictedUnitTransport K L S hS σ q r hσ
          (supportedUnrestrictedUnitTransport K L S hS τ p q hτ x) :=
  supportedUnrestrictedUnitTransport_mul K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]


/-- Exact original-object consumer of `numberFieldIntegerUnitTransport_mul`. -/
theorem actual_supported_local_numberFieldIntegerUnitTransport_mul_source (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L)) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : Additive (v.adicCompletionIntegers L)ˣ) :
    numberFieldIntegerUnitTransport K L (σ * τ) v w hστ x =
      numberFieldIntegerUnitTransport K L σ u w hσ
        (numberFieldIntegerUnitTransport K L τ v u hτ x) :=
  numberFieldIntegerUnitTransport_mul K L σ τ v u w hτ hσ hστ x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedOutsideUnitTransport_mul`. -/
theorem actual_supported_local_supportedOutsideUnitTransport_mul_source :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ (σ τ : Gal(L/K)) (v u w : {v : HeightOneSpectrum (𝓞 L) // v ∉ S})
      (hτ : τ • v = u) (hσ : σ • u = w) (hστ : (σ * τ) • v = w)
      (x : Additive (v.val.adicCompletionIntegers L)ˣ),
      supportedOutsideUnitTransport K L S hS (σ * τ) v w hστ x =
        supportedOutsideUnitTransport K L S hS σ u w hσ
          (supportedOutsideUnitTransport K L S hS τ v u hτ x) :=
  supportedOutsideUnitTransport_mul K L S hS

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `supportedIdeleLocalFactorLinearEquiv_outside`. -/
theorem actual_supported_local_supportedIdeleLocalFactorLinearEquiv_outside_source
    (a : Additive (numberFieldSupportedIdeles L S))
    (v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S}) :
    (((supportedIdeleLocalFactorLinearEquiv L S a).2 v).toMul.val : v.val.adicCompletion L) =
      (numberFieldIdeleFiniteComponent L v.val a.toMul.val).val :=
  supportedIdeleLocalFactorLinearEquiv_outside L S a v

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedIdeleLocalFactorRepIso_hom_apply`. -/
theorem actual_supported_local_supportedIdeleLocalFactorRepIso_hom_apply_source
    (a : Additive (numberFieldSupportedIdeles L S)) :
    (supportedIdeleLocalFactorRepIso K L S hS).hom.hom a =
      supportedIdeleLocalFactorLinearEquiv L S a :=
  supportedIdeleLocalFactorRepIso_hom_apply K L S hS a

end

section

variable (R G ι : Type) [CommRing R] [CommGroup G] [MulAction G ι] [Fintype ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))



/-- Exact original-object consumer of `transportedFiniteOrbit_cohomology_card`. -/
theorem actual_supported_local_transportedFiniteOrbit_cohomology_card_source (n : ℕ) :
    Nat.card (groupCohomology (transportedPiRep R G ι M T T_one T_mul) n) =
      ∏ ω : MulAction.orbitRel.Quotient G ι,
        Nat.card (groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
          (permutationOrbitPoint G ι ω)) n) :=
  transportedFiniteOrbit_cohomology_card R G ι M T T_one T_mul n

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedUnit_cohomology_card`. -/
theorem actual_supported_local_supportedUnrestrictedUnit_cohomology_card_source (n : ℕ) :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    Nat.card (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n) =
      ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) n) :=
  supportedUnrestrictedUnit_cohomology_card K L S hS n

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedOutsideUnit_cohomology_zero_of_local`. -/
theorem actual_supported_local_supportedOutsideUnit_cohomology_zero_of_local_source (n : ℕ) (hn : 0 < n) :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    (∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) n)) →
    Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) n) :=
  supportedOutsideUnit_cohomology_zero_of_local K L S hS n hn

end

section

variable {R G : Type} [CommRing R] [Group G] (A B : Rep R G)



/-- Exact original-object consumer of `originalBinaryProduct_cohomology_card`. -/
theorem actual_supported_local_originalBinaryProduct_cohomology_card_source (n : ℕ) :
    Nat.card (groupCohomology (Rep.of (A.ρ.prod B.ρ)) n) =
      Nat.card (groupCohomology A n) * Nat.card (groupCohomology B n) :=
  originalBinaryProduct_cohomology_card A B n

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `originalSupportedIdele_cohomology_of_outside_zero`. -/
theorem actual_supported_local_originalSupportedIdele_cohomology_of_outside_zero_source (n : ℕ)
    [Finite (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n)]
    (hout : Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) n)) :
    Finite (groupCohomology (originalSupportedIdeleRep K L S hS) n) ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) n) =
        Nat.card (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n) :=
  originalSupportedIdele_cohomology_of_outside_zero K L S hS n hout

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_supportedIdele_cohomology_of_local`. -/
theorem actual_supported_local_original_supportedIdele_cohomology_of_local_source
    (hlocal : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Limits.IsZero (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) ∧
        Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 1) ∧
      Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 2) ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 1) = 1 ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 2) =
        ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  original_supportedIdele_cohomology_of_local K L S hS hlocal houtside

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_local`. -/
theorem actual_supported_local_original_ideleClass_herbrand_of_local_source
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (hlocal : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Limits.IsZero (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) ∧
        Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_local K L S hS hsurj hlocal houtside

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField ValuativeRel Classical
attribute [local instance 1100] Rep.hV2
attribute [local instance] Units.mulDistribMulActionRight
section

variable (G F : Type) [Group G] [Finite G] [Field F]
  [MulSemiringAction G F] [FaithfulSMul G F]



/-- Exact original-object consumer of `faithfulFieldUnit_first_cohomology_zero`. -/
theorem actual_unrestricted_local_cohomology_faithfulFieldUnit_first_cohomology_zero_source :
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 1) :=
  faithfulFieldUnit_first_cohomology_zero G F

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedFieldTransport_algebraMap`. -/
theorem actual_unrestricted_local_cohomology_supportedUnrestrictedFieldTransport_algebraMap_source :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p q : SUnitLogPlace L S) (h : σ • p = q) (x : L),
      supportedUnrestrictedFieldTransport K L S hS σ p q h
        (algebraMap L (supportedUnrestrictedCompletion L S p) x) =
      algebraMap L (supportedUnrestrictedCompletion L S q) (σ x) :=
  supportedUnrestrictedFieldTransport_algebraMap K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedOrbitField_faithful`. -/
theorem actual_unrestricted_local_cohomology_supportedUnrestrictedOrbitField_faithful_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      letI := supportedUnrestrictedOrbitFieldAction K L S hS ω
      FaithfulSMul
        (MulAction.stabilizer Gal(L/K) (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω))
        (supportedUnrestrictedCompletion L S ω.out) :=
  supportedUnrestrictedOrbitField_faithful K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedUnitFieldEquiv_transport`. -/
theorem actual_unrestricted_local_cohomology_supportedUnrestrictedUnitFieldEquiv_transport_source :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p q : SUnitLogPlace L S) (h : σ • p = q)
      (x : supportedUnrestrictedUnitModule L S p),
      supportedUnrestrictedUnitFieldEquiv L S q (supportedUnrestrictedUnitTransport K L S hS σ p q h x) =
        Additive.ofMul (Units.map (supportedUnrestrictedFieldTransport K L S hS σ p q h).toMonoidHom
          (supportedUnrestrictedUnitFieldEquiv L S p x).toMul) :=
  supportedUnrestrictedUnitFieldEquiv_transport K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `supportedUnrestrictedUnit_first_cohomology_zero`. -/
theorem actual_unrestricted_local_cohomology_supportedUnrestrictedUnit_first_cohomology_zero_source :
    Limits.IsZero (groupCohomology (supportedUnrestrictedUnitRep K L S hS) 1) :=
  supportedUnrestrictedUnit_first_cohomology_zero K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_local_second`. -/
theorem actual_unrestricted_local_cohomology_original_ideleClass_herbrand_of_local_second_source
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (hsecond : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_local_second K L S hS hsurj hsecond houtside

end

section

variable (K : Type*) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_exists_ringOfIntegers_approximation`. -/
theorem actual_unrestricted_local_cohomology_original_exists_ringOfIntegers_approximation_source
    (v : HeightOneSpectrum (𝓞 K)) (y : K)
    (hy : v.valuation K y ≤ 1) :
    ∃ r : 𝓞 K, v.valuation K (y - algebraMap (𝓞 K) K r) < 1 :=
  original_exists_ringOfIntegers_approximation K v y hy

end

section

variable (K : Type*) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_finite_adicCompletion_residueField`. -/
theorem actual_unrestricted_local_cohomology_original_finite_adicCompletion_residueField_source
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite (Valued.ResidueField (v.adicCompletion K)) :=
  original_finite_adicCompletion_residueField K v

end

section

variable (G F : Type) [Group G] [Finite G] [NontriviallyNormedField F]
  [MulSemiringAction G F]
  (hnorm : ∀ (g : G) (x : F), ‖g • x‖ = ‖x‖)



include hnorm in
/-- Exact original-object consumer of `normPreserving_fixedField_exists_norm_gt_one`. -/
theorem actual_unrestricted_local_cohomology_normPreserving_fixedField_exists_norm_gt_one_source :
    ∃ x : FixedPoints.subfield G F, 1 < ‖x‖ :=
  normPreserving_fixedField_exists_norm_gt_one G F hnorm

end

section

variable (G F : Type) [Group G] [Finite G] [IsCyclic G]
  [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
  [MulSemiringAction G F] [FaithfulSMul G F]



/-- Exact original-object consumer of `faithfulLocalField_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_faithfulLocalField_second_cohomology_order_source
    (hnorm : ∀ (g : G) (x : F), ‖g • x‖ = ‖x‖) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G :=
  faithfulLocalField_second_cohomology_order G F hnorm

end

section

variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))



/-- Exact original-object consumer of `supportedFiniteCompletion_isUltrametric`. -/
theorem actual_unrestricted_local_cohomology_supportedFiniteCompletion_isUltrametric_source (p : SUnitLogPlace L S)
    (h : p.isRight) : IsUltrametricDist (supportedUnrestrictedCompletion L S p) :=
  supportedFiniteCompletion_isUltrametric L S p h

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



variable [FiniteDimensional K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `supportedFiniteOrbitPoint_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_supportedFiniteOrbitPoint_second_cohomology_order_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      ω.out.isRight →
      Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
      Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
        Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  supportedFiniteOrbitPoint_second_cohomology_order K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_archimedean_second`. -/
theorem actual_unrestricted_local_cohomology_original_ideleClass_herbrand_of_archimedean_second_source
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (harch : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        ω.out.isLeft →
        Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_archimedean_second K L S hS hsurj harch houtside

end

section



/-- Exact original-object consumer of `originalRealComplexNormQuotient_card`. -/
theorem actual_unrestricted_local_cohomology_originalRealComplexNormQuotient_card_source :
    Finite (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) ∧
    Nat.card (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) = 2 :=
  originalRealComplexNormQuotient_card 

end

section



/-- Exact original-object consumer of `originalRealComplex_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_originalRealComplex_second_cohomology_order_source :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2) = 2 :=
  originalRealComplex_second_cohomology_order 

end

section

variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F] [FaithfulSMul G F]



/-- Exact original-object consumer of `faithfulRealField_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_faithfulRealField_second_cohomology_order_source (e : F ≃+* ℝ) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G :=
  faithfulRealField_second_cohomology_order G F e

end

section

variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F]
  (e : F ≃+* ℂ)
  (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))



variable [FaithfulSMul G F]



/-- Exact original-object consumer of `faithfulComplexActionHom_injective`. -/
theorem actual_unrestricted_local_cohomology_faithfulComplexActionHom_injective_source :
    Function.Injective (faithfulComplexActionHom G F e hc) :=
  faithfulComplexActionHom_injective G F e hc

end

section

variable (G F : Type) [Group G] [Finite G] [Nontrivial G] [Field F]
  [MulSemiringAction G F] [FaithfulSMul G F]
  (e : F ≃+* ℂ) (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))



/-- Exact original-object consumer of `faithfulComplexActionHom_bijective`. -/
theorem actual_unrestricted_local_cohomology_faithfulComplexActionHom_bijective_source :
    Function.Bijective (faithfulComplexActionHom G F e hc) :=
  faithfulComplexActionHom_bijective G F e hc

end

section

variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F]
  (e : F ≃+* ℂ) (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))



variable [Finite G] [FaithfulSMul G F]



include e hc in
/-- Exact original-object consumer of `faithfulComplexField_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_faithfulComplexField_second_cohomology_order_source :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G :=
  faithfulComplexField_second_cohomology_order G F e hc

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



variable [FiniteDimensional K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `supportedArchimedeanOrbitPoint_second_cohomology_order`. -/
theorem actual_unrestricted_local_cohomology_supportedArchimedeanOrbitPoint_second_cohomology_order_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      ω.out.isLeft →
      Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
      Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
        Nat.card (MulAction.stabilizer Gal(L/K) ω.out) :=
  supportedArchimedeanOrbitPoint_second_cohomology_order K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



/-- Exact original-object consumer of `original_ideleClass_herbrand_of_outside`. -/
theorem actual_unrestricted_local_cohomology_original_ideleClass_herbrand_of_outside_source
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand_of_outside K L S hS hsurj houtside

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] Rep.hV2
section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)



/-- Exact original-object consumer of `localFieldFixedUniformizerSection_comp`. -/
theorem actual_original_idele_herbrand_localFieldFixedUniformizerSection_comp_source
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    localFieldFixedUniformizerSection K L π hfixed ≫
        (localFieldUnitValuationShortComplex K L).g = 𝟙 (Rep.trivial ℤ Gal(L/K) ℤ) :=
  localFieldFixedUniformizerSection_comp K L π hfixed hπ

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]



/-- Exact original-object consumer of `localIntegerUnit_first_second_zero_of_fixed_uniformizer`. -/
theorem actual_original_idele_herbrand_localIntegerUnit_first_second_zero_of_fixed_uniformizer_source
    [IsCyclic Gal(L/K)] (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) 1) ∧
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) 2) :=
  localIntegerUnit_first_second_zero_of_fixed_uniformizer K L π hfixed hπ

end

section



/-- Exact original-object consumer of `original_finite_absolutely_ramified_places`. -/
theorem actual_original_idele_herbrand_original_finite_absolutely_ramified_places_source
    (L : Type) [Field L] [NumberField L] :
    {w : HeightOneSpectrum (𝓞 L) | ¬ Algebra.IsUnramifiedAt ℤ w.asIdeal}.Finite :=
  original_finite_absolutely_ramified_places L

end

section

variable (L : Type) [Field L] [NumberField L]



/-- Exact original-object consumer of `original_unramified_exists_completion_integer_uniformizer`. -/
theorem actual_original_idele_herbrand_original_unramified_exists_completion_integer_uniformizer_source
    (w : HeightOneSpectrum (𝓞 L)) [Algebra.IsUnramifiedAt ℤ w.asIdeal] :
    ∃ r : ℤ, Valued.v (r : w.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
  original_unramified_exists_completion_integer_uniformizer L w

end

section

variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))



/-- Exact original-object consumer of `originalAdicIntegerNormEquiv_val`. -/
theorem actual_original_idele_herbrand_originalAdicIntegerNormEquiv_val_source (x : w.adicCompletionIntegers L) :
    (originalAdicIntegerNormEquiv L w x).val = x.val :=
  originalAdicIntegerNormEquiv_val L w x

end

section

variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))



/-- Exact original-object consumer of `originalAdicUnitOrder_of_uniformizer`. -/
theorem actual_original_idele_herbrand_originalAdicUnitOrder_of_uniformizer_source
    (π : (w.adicCompletion L)ˣ) (hπ : Valued.v π.val = WithZero.exp (-1 : ℤ)) :
    letI : ProperSpace (w.adicCompletion L) := original_adicCompletion_properSpace L w
    letI : NontriviallyNormedField (w.adicCompletion L) :=
      Valued.toNontriviallyNormedField (w.adicCompletion L) ℤᵐ⁰
    letI : ValuativeRel (w.adicCompletion L) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
    letI : IsNonarchimedeanLocalField (w.adicCompletion L) :=
      normValuation_isNonarchimedeanLocalField (w.adicCompletion L)
    localFieldUnitOrder (w.adicCompletion L) (Additive.ofMul π) = 1 :=
  originalAdicUnitOrder_of_uniformizer L w π hπ

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `supportedOutsideOrbitField_norm`. -/
theorem actual_original_idele_herbrand_supportedOutsideOrbitField_norm_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      letI := supportedOutsideOrbitFieldAction K L S hS ω
      ∀ (σ : MulAction.stabilizer Gal(L/K)
          (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (x : ω.out.val.adicCompletion L), ‖σ • x‖ = ‖x‖ :=
  supportedOutsideOrbitField_norm K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `supportedOutsideOrbitPoint_first_second_zero_of_unramified`. -/
theorem actual_original_idele_herbrand_supportedOutsideOrbitPoint_first_second_zero_of_unramified_source :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Algebra.IsUnramifiedAt ℤ ω.out.val.asIdeal →
      Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2) :=
  supportedOutsideOrbitPoint_first_second_zero_of_unramified K L S hS

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]



/-- Exact original-object consumer of `original_exists_unramified_galoisStable_idele_support`. -/
theorem actual_original_idele_herbrand_original_exists_unramified_galoisStable_idele_support_source
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      (∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) ∧
        Function.Surjective (numberFieldSupportedIdeleClassMap L S) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal :=
  original_exists_unramified_galoisStable_idele_support K L S₀

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]



/-- Exact original-object consumer of `original_ideleClass_herbrand`. -/
theorem actual_original_idele_herbrand_original_ideleClass_herbrand_source :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) :=
  original_ideleClass_herbrand K L

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] Rep.hV2
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]


/-- Exact original-object consumer of `originalIdeleClassInvariantNormQuotient_order_lower`. -/
theorem actual_original_norm_descent_originalIdeleClassInvariantNormQuotient_order_lower_source
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Finite (OriginalIdeleClassInvariantNormQuotient K L g) ∧
      Nat.card Gal(L/K) ≤ Nat.card (OriginalIdeleClassInvariantNormQuotient K L g) :=
  originalIdeleClassInvariantNormQuotient_order_lower K L g hg

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


/-- Exact original-object consumer of `originalIdeleClassInvariantNormQuotient_degree_nsmul_zero`. -/
theorem actual_original_norm_descent_originalIdeleClassInvariantNormQuotient_degree_nsmul_zero_source
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
    (x : OriginalIdeleClassInvariantNormQuotient K L g) :
    Module.finrank K L • x = 0 :=
  originalIdeleClassInvariantNormQuotient_degree_nsmul_zero K L g hg x

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalFullClassH0_surjective`. -/
theorem actual_original_norm_descent_originalFullClassH0_surjective_source [FiniteDimensional K L] :
    Function.Surjective ((groupCohomology.functor ℤ Gal(L/K) 0).map (originalFullClassRepHom K L)) :=
  originalFullClassH0_surjective K L

end

section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]



/-- Exact original-object consumer of `original_ideleClass_fixed_has_fixed_representative`. -/
theorem actual_original_norm_descent_original_ideleClass_fixed_has_fixed_representative_source
    (c : OriginalNumberFieldIdeleClassGroup L)
    (hc : ∀ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c = c) :
    ∃ a : (AdeleRing (𝓞 L) L)ˣ,
      QuotientGroup.mk' (numberFieldPrincipalIdele L).range a = c ∧
        ∀ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a = a :=
  original_ideleClass_fixed_has_fixed_representative K L c hc

end

section

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]



/-- Exact original-object consumer of `original_intValuation_algebraMap_pow`. -/
theorem actual_original_norm_descent_original_intValuation_algebraMap_pow_source
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (r : R) :
    w.intValuation (algebraMap R S r) =
      v.intValuation r ^ v.asIdeal.ramificationIdx w.asIdeal :=
  original_intValuation_algebraMap_pow v w r

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `original_adicFieldMap_uniformContinuous`. -/
theorem actual_original_norm_descent_original_adicFieldMap_uniformContinuous_source :
    UniformContinuous (WithVal.map (v.valuation K) (w.valuation L) (algebraMap K L)) :=
  original_adicFieldMap_uniformContinuous K L v w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `originalAdicBaseChangeMap_mem_integers`. -/
theorem actual_original_norm_descent_originalAdicBaseChangeMap_mem_integers_source (x : v.adicCompletion K) :
    originalAdicBaseChangeMap K L v w x ∈ w.adicCompletionIntegers L ↔
      x ∈ v.adicCompletionIntegers K :=
  originalAdicBaseChangeMap_mem_integers K L v w x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `originalAdicBaseChangeMap_fixed`. -/
theorem actual_original_norm_descent_originalAdicBaseChangeMap_fixed_source (σ : Gal(L/K))
    (hσ : numberFieldGaloisPlaceEquiv K L σ w = w) (x : v.adicCompletion K) :
    numberFieldGaloisLocalTransport K L σ w w hσ
      (originalAdicBaseChangeMap K L v w x) = originalAdicBaseChangeMap K L v w x :=
  originalAdicBaseChangeMap_fixed K L v w σ hσ x

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_adicAbv_not_isEquiv_of_ne`. -/
theorem actual_original_norm_descent_original_adicAbv_not_isEquiv_of_ne_source
    {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv K w) :=
  original_adicAbv_not_isEquiv_of_ne K hvw

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_finiteCompletions_dense`. -/
theorem actual_original_norm_descent_original_finiteCompletions_dense_source (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun v : S => algebraMap K (v.1.adicCompletion K) x) :=
  original_finiteCompletions_dense K S

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]



/-- Exact original-object consumer of `originalCompletionOrbitTrace_mem_base`. -/
theorem actual_original_norm_descent_originalCompletionOrbitTrace_mem_base_source [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (z : ∀ u : originalGaloisCompletionOrbit K L w, u.1.adicCompletion L) :
    originalCompletionOrbitTrace K L w z ∈ Set.range (originalAdicBaseChangeMap K L v w) :=
  originalCompletionOrbitTrace_mem_base K L v w z

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `originalAdicBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_norm_descent_originalAdicBaseChangeMap_range_iff_fixed_source (x : w.adicCompletion L) :
    x ∈ Set.range (originalAdicBaseChangeMap K L v w) ↔
      ∀ (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ w = w),
        numberFieldGaloisLocalTransport K L σ w w hσ x = x :=
  originalAdicBaseChangeMap_range_iff_fixed K L v w x

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Topology
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] Rep.hV2 AddCommGroup.toAddCommMonoid
attribute [local instance] IsCyclic.commGroup
section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalFinitePrimeBelow_preimage_finite`. -/
theorem actual_original_base_norm_originalFinitePrimeBelow_preimage_finite_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    {w : HeightOneSpectrum (𝓞 L) | originalFinitePrimeBelow K L w ∈ S}.Finite :=
  originalFinitePrimeBelow_preimage_finite K L S hS

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalAdicBaseChangeMap_transport`. -/
theorem actual_original_base_norm_originalAdicBaseChangeMap_transport_source
    (v : HeightOneSpectrum (𝓞 K)) (u w : HeightOneSpectrum (𝓞 L))
    [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
    (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)
    (x : v.adicCompletion K) :
    numberFieldGaloisLocalTransport K L σ u w hσ (originalAdicBaseChangeMap K L v u x) =
      originalAdicBaseChangeMap K L v w x :=
  originalAdicBaseChangeMap_transport K L v u w σ hσ x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalFiniteAdeleBaseChangeMap_fixed`. -/
theorem actual_original_base_norm_originalFiniteAdeleBaseChangeMap_fixed_source (σ : Gal(L/K)) (a : FiniteAdeleRing (𝓞 K) K) :
    numberFieldFiniteAdeleGaloisMap K L σ (originalFiniteAdeleBaseChangeMap K L a) =
      originalFiniteAdeleBaseChangeMap K L a :=
  originalFiniteAdeleBaseChangeMap_fixed K L σ a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalFiniteAdeleBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_base_norm_originalFiniteAdeleBaseChangeMap_range_iff_fixed_source (a : FiniteAdeleRing (𝓞 L) L) :
    a ∈ Set.range (originalFiniteAdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldFiniteAdeleGaloisMap K L σ a = a :=
  originalFiniteAdeleBaseChangeMap_range_iff_fixed K L a

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



variable [NumberField K] [NumberField L]



/-- Exact original-object consumer of `originalInfiniteAdeleBaseChangeMap_isClosedEmbedding`. -/
theorem actual_original_base_norm_originalInfiniteAdeleBaseChangeMap_isClosedEmbedding_source :
    IsClosedEmbedding (originalInfiniteAdeleBaseChangeMap K L) :=
  originalInfiniteAdeleBaseChangeMap_isClosedEmbedding K L

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]



variable [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalInfiniteAdeleBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_base_norm_originalInfiniteAdeleBaseChangeMap_range_iff_fixed_source (a : InfiniteAdeleRing L) :
    a ∈ Set.range (originalInfiniteAdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ a = a :=
  originalInfiniteAdeleBaseChangeMap_range_iff_fixed K L a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalAdeleBaseChangeMap_surjective_fixed`. -/
theorem actual_original_base_norm_originalAdeleBaseChangeMap_surjective_fixed_source [FiniteDimensional K L] [IsGalois K L]
    (a : AdeleRing (𝓞 L) L) (ha : ∀ σ : Gal(L/K), numberFieldAdeleGaloisMap K L σ a = a) :
    ∃ b : AdeleRing (𝓞 K) K, originalAdeleBaseChangeMap K L b = a :=
  originalAdeleBaseChangeMap_surjective_fixed K L a ha

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



/-- Exact original-object consumer of `originalIdeleBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_base_norm_originalIdeleBaseChangeMap_range_iff_fixed_source [FiniteDimensional K L] [IsGalois K L]
    (a : (AdeleRing (𝓞 L) L)ˣ) :
    a ∈ Set.range (originalIdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a = a :=
  originalIdeleBaseChangeMap_range_iff_fixed K L a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



variable [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassBaseChangeMap_range_iff_fixed`. -/
theorem actual_original_base_norm_originalIdeleClassBaseChangeMap_range_iff_fixed_source (c : OriginalNumberFieldIdeleClassGroup L) :
    c ∈ Set.range (originalIdeleClassBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c = c :=
  originalIdeleClassBaseChangeMap_range_iff_fixed K L c

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleNorm_principal`. -/
theorem actual_original_base_norm_originalIdeleNorm_principal_source (x : Lˣ) :
    originalIdeleNorm K L (numberFieldPrincipalIdele L x) =
      numberFieldPrincipalIdele K (Units.map (Algebra.norm K (S := L)) x) :=
  originalIdeleNorm_principal K L x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassBaseChangeMap_norm`. -/
theorem actual_original_base_norm_originalIdeleClassBaseChangeMap_norm_source (c : OriginalNumberFieldIdeleClassGroup L) :
    originalIdeleClassBaseChangeMap K L (originalIdeleClassNorm K L c) =
      ∏ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c :=
  originalIdeleClassBaseChangeMap_norm K L c

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


/-- Exact original-object consumer of `originalIdeleClassBaseInvariant_norm`. -/
theorem actual_original_base_norm_originalIdeleClassBaseInvariant_norm_source (g : Gal(L/K))
    (x : Additive (OriginalNumberFieldIdeleClassGroup L)) :
    (originalIdeleClassBaseInvariant K L g (originalIdeleClassNormLinear K L x)).val =
      (originalIdeleClassRep K L).norm.hom x :=
  originalIdeleClassBaseInvariant_norm K L g x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


/-- Exact original-object consumer of `originalIdeleClassNormQuotient_degree_nsmul_zero`. -/
theorem actual_original_base_norm_originalIdeleClassNormQuotient_degree_nsmul_zero_source (x : OriginalIdeleClassNormQuotient K L) :
    Module.finrank K L • x = 0 :=
  originalIdeleClassNormQuotient_degree_nsmul_zero K L x

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Topology
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] Rep.hV2
attribute [local instance] IsCyclic.commGroup
section

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]



variable [NumberField K] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicBaseFixedEquiv_val`. -/
theorem actual_original_local_norm_originalAdicBaseFixedEquiv_val_source (x : v.adicCompletion K) :
    (originalAdicBaseFixedEquiv K L v w x).val = originalAdicBaseChangeMap K L v w x :=
  originalAdicBaseFixedEquiv_val K L v w x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicNorm_galois_product`. -/
theorem actual_original_local_norm_originalAdicNorm_galois_product_source :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ x : w.adicCompletion L,
      originalAdicBaseChangeMap K L v w (Algebra.norm (v.adicCompletion K) x) =
        ∏ σ : OriginalFiniteDecompositionGroup K L w,
          numberFieldGaloisLocalTransport K L σ.val w w σ.property x :=
  originalAdicNorm_galois_product K L v w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



variable [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_finiteComponent_product`. -/
theorem actual_original_local_norm_originalIdeleNorm_finiteComponent_product_source (a : (AdeleRing (𝓞 L) L)ˣ) :
    Units.map (originalAdicBaseChangeMap K L v w).toMonoidHom
        (numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a)) =
      ∏ σ : Gal(L/K), Units.map
        (numberFieldGaloisLocalTransport K L σ ((numberFieldGaloisPlaceEquiv K L σ).symm w) w
          ((numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w)).toMonoidHom
        (numberFieldIdeleFiniteComponent L ((numberFieldGaloisPlaceEquiv K L σ).symm w) a) :=
  originalIdeleNorm_finiteComponent_product K L v w a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (w : HeightOneSpectrum (𝓞 L))



omit [NumberField K] [IsGalois K L] in
attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleFiniteOrbitNormPreimage_product`. -/
theorem actual_original_local_norm_originalIdeleFiniteOrbitNormPreimage_product_source (a : (AdeleRing (𝓞 L) L)ˣ) :
    (∏ σ : Gal(L/K), numberFieldIdeleFiniteComponent L w (numberFieldIdeleGaloisMap K L σ a)) =
      ∏ τ : OriginalFiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisLocalTransport K L τ.val w w τ.property).toMonoidHom
          (originalIdeleFiniteOrbitNormPreimage K L w a) :=
  originalIdeleFiniteOrbitNormPreimage_product K L w a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_finiteComponent_eq_localNorm`. -/
theorem actual_original_local_norm_originalIdeleNorm_finiteComponent_eq_localNorm_source :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ a : (AdeleRing (𝓞 L) L)ˣ,
      numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a) =
        Units.map (Algebra.norm (v.adicCompletion K) (S := w.adicCompletion L))
          (originalIdeleFiniteOrbitNormPreimage K L w a) :=
  originalIdeleNorm_finiteComponent_eq_localNorm K L v w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (w : InfinitePlace L)



variable [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfiniteCompletionBaseChange_range_iff_fixed`. -/
theorem actual_original_local_norm_originalInfiniteCompletionBaseChange_range_iff_fixed_source (x : w.Completion) :
    x ∈ Set.range (originalInfiniteCompletionBaseChange K L w) ↔
      ∀ (σ : Gal(L/K)) (hσ : σ • w = w), numberFieldGaloisArchimedeanTransport K L σ w w hσ x = x :=
  originalInfiniteCompletionBaseChange_range_iff_fixed K L w x

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]



variable [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
  (w : InfinitePlace L)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfiniteCompletionBaseFixedEquiv_val`. -/
theorem actual_original_local_norm_originalInfiniteCompletionBaseFixedEquiv_val_source (x : (w.comap (algebraMap K L)).Completion) :
    (originalInfiniteCompletionBaseFixedEquiv K L w x).val = originalInfiniteCompletionBaseChange K L w x :=
  originalInfiniteCompletionBaseFixedEquiv_val K L w x

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : InfinitePlace L)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfiniteNorm_galois_product`. -/
theorem actual_original_local_norm_originalInfiniteNorm_galois_product_source :
    letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
      (originalInfiniteCompletionBaseChange K L w).toAlgebra
    ∀ x : w.Completion,
      originalInfiniteCompletionBaseChange K L w (Algebra.norm ((w.comap (algebraMap K L)).Completion) x) =
        ∏ σ : OriginalInfiniteDecompositionGroup K L w,
          numberFieldGaloisArchimedeanTransport K L σ.val w w σ.property x :=
  originalInfiniteNorm_galois_product K L w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (w : InfinitePlace L)



omit [NumberField K] [IsGalois K L] in
attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleInfiniteOrbitNormPreimage_product`. -/
theorem actual_original_local_norm_originalIdeleInfiniteOrbitNormPreimage_product_source (a : (AdeleRing (𝓞 L) L)ˣ) :
    (∏ σ : Gal(L/K), numberFieldIdeleInfiniteComponent L w (numberFieldIdeleGaloisMap K L σ a)) =
      ∏ τ : OriginalInfiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom
          (originalIdeleInfiniteOrbitNormPreimage K L w a) :=
  originalIdeleInfiniteOrbitNormPreimage_product K L w a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (w : InfinitePlace L)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_infiniteComponent_eq_localNorm`. -/
theorem actual_original_local_norm_originalIdeleNorm_infiniteComponent_eq_localNorm_source :
    letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
      (originalInfiniteCompletionBaseChange K L w).toAlgebra
    ∀ a : (AdeleRing (𝓞 L) L)ˣ,
      numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a) =
        Units.map (Algebra.norm ((w.comap (algebraMap K L)).Completion) (S := w.Completion))
          (originalIdeleInfiniteOrbitNormPreimage K L w a) :=
  originalIdeleNorm_infiniteComponent_eq_localNorm K L w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalAdicNorm_preimage_integerUnit`. -/
theorem actual_original_local_norm_originalAdicNorm_preimage_integerUnit_source :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ u : (w.adicCompletion L)ˣ,
      Units.map (Algebra.norm (v.adicCompletion K) (S := w.adicCompletion L)) u ∈
        (v.adicCompletionIntegers K).units → u ∈ (w.adicCompletionIntegers L).units :=
  originalAdicNorm_preimage_integerUnit K L v w

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



variable [FiniteDimensional K L] [IsGalois K L]



variable [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_finiteLocal`. -/
theorem actual_original_local_norm_originalIdeleNorm_finiteLocal_source (w : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) (originalIdeleNorm K L a) =
      originalFiniteLocalNorm K L w (originalIdeleFiniteOrbitNormPreimage K L w a) :=
  originalIdeleNorm_finiteLocal K L w a

end

section

variable (K : Type) [Field K] [NumberField K]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdele_eq_of_components`. -/
theorem actual_original_local_norm_originalIdele_eq_of_components_source (a b : (AdeleRing (𝓞 K) K)ˣ)
    (hFin : ∀ v, numberFieldIdeleFiniteComponent K v a = numberFieldIdeleFiniteComponent K v b)
    (hInf : ∀ v, numberFieldIdeleInfiniteComponent K v a = numberFieldIdeleInfiniteComponent K v b) : a = b :=
  originalIdele_eq_of_components K a b hFin hInf

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfiniteLocalNorm_baseChange`. -/
theorem actual_original_local_norm_originalInfiniteLocalNorm_baseChange_source (w : InfinitePlace L) (u : w.Completionˣ) :
    Units.map (originalInfiniteCompletionBaseChange K L w).toMonoidHom
        (originalInfiniteLocalNorm K L w u) =
      ∏ τ : OriginalInfiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom u :=
  originalInfiniteLocalNorm_baseChange K L w u

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_finiteComponent_of_onePrime`. -/
theorem actual_original_local_norm_originalIdeleNorm_finiteComponent_of_onePrime_source (w : HeightOneSpectrum (𝓞 L))
    (a : (AdeleRing (𝓞 L) L)ˣ)
    (ha : ∀ u : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L u = originalFinitePrimeBelow K L w →
      u ≠ w → numberFieldIdeleFiniteComponent L u a = 1) :
    numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) (originalIdeleNorm K L a) =
      originalFiniteLocalNorm K L w (numberFieldIdeleFiniteComponent L w a) :=
  originalIdeleNorm_finiteComponent_of_onePrime K L w a ha

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_infiniteComponent_of_onePlace`. -/
theorem actual_original_local_norm_originalIdeleNorm_infiniteComponent_of_onePlace_source (w : InfinitePlace L)
    (a : (AdeleRing (𝓞 L) L)ˣ)
    (ha : ∀ u : InfinitePlace L, u.comap (algebraMap K L) = w.comap (algebraMap K L) →
      u ≠ w → numberFieldIdeleInfiniteComponent L u a = 1) :
    numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a) =
      originalInfiniteLocalNorm K L w (numberFieldIdeleInfiniteComponent L w a) :=
  originalIdeleNorm_infiniteComponent_of_onePlace K L w a ha

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



variable [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleNorm_range_iff_local`. -/
theorem actual_original_local_norm_originalIdeleNorm_range_iff_local_source (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ (originalIdeleNorm K L).range ↔
      (∀ w : HeightOneSpectrum (𝓞 L), numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) a ∈
        (originalFiniteLocalNorm K L w).range) ∧
      (∀ w : InfinitePlace L, numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) a ∈
        (originalInfiniteLocalNorm K L w).range) :=
  originalIdeleNorm_range_iff_local K L a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalFiniteLocalNorm_degreePower`. -/
theorem actual_original_local_norm_originalFiniteLocalNorm_degreePower_source (w : HeightOneSpectrum (𝓞 L))
    (u : ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ) :
    u ^ Module.finrank K L ∈ (originalFiniteLocalNorm K L w).range :=
  originalFiniteLocalNorm_degreePower K L w u

end

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `localIntegerUnit_norm_preimages_of_fixed_uniformizer`. -/
theorem actual_original_local_norm_localIntegerUnit_norm_preimages_of_fixed_uniformizer_source
    (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x :=
  localIntegerUnit_norm_preimages_of_fixed_uniformizer K L π hfixed hπ

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalFiniteLocalNorm_integerUnit_of_unramified`. -/
theorem actual_original_local_norm_originalFiniteLocalNorm_integerUnit_of_unramified_source
    (w : HeightOneSpectrum (𝓞 L)) (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (u : ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ)
    (hu : u ∈ ((originalFinitePrimeBelow K L w).adicCompletionIntegers K).units) :
    u ∈ (originalFiniteLocalNorm K L w).range :=
  originalFiniteLocalNorm_integerUnit_of_unramified K L w hw u hu

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalFiniteLocalNorm_surjective_of_split`. -/
theorem actual_original_local_norm_originalFiniteLocalNorm_surjective_of_split_source
    (w : HeightOneSpectrum (𝓞 L)) (hw : OriginalFiniteDecompositionGroup K L w = ⊥) :
    Function.Surjective (originalFiniteLocalNorm K L w) :=
  originalFiniteLocalNorm_surjective_of_split K L w hw

end

section

variable (K : Type) [Field K] [NumberField K]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdelePowerLocalUnitSubgroup_mem_iff`. -/
theorem actual_original_local_norm_originalIdelePowerLocalUnitSubgroup_mem_iff_source (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ originalIdelePowerLocalUnitSubgroup K n S T ↔
      (∀ w : InfinitePlace K, numberFieldIdeleInfiniteComponent K w a ∈ (powMonoidHom n).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S →
        numberFieldIdeleFiniteComponent K v a ∈ (powMonoidHom n).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T →
        numberFieldIdeleFiniteComponent K v a ∈ (v.adicCompletionIntegers K).units) :=
  originalIdelePowerLocalUnitSubgroup_mem_iff K n S T a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleClassPowerLocalUnitSubgroup_le_norm`. -/
theorem actual_original_local_norm_originalIdeleClassPowerLocalUnitSubgroup_le_norm_source
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hAway : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∪ T →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    originalIdeleClassPowerLocalUnitSubgroup K (Module.finrank K L) S T ≤ (originalIdeleClassNorm K L).range :=
  originalIdeleClassPowerLocalUnitSubgroup_le_norm K L S T hT hAway

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



variable [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleClassPowerLocalUnitSubgroup_le_norm_enlarged`. -/
theorem actual_original_local_norm_originalIdeleClassPowerLocalUnitSubgroup_le_norm_enlarged_source
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥) :
    originalIdeleClassPowerLocalUnitSubgroup K (Module.finrank K L)
      (S ∪ originalNormRamificationSupport K L) T ≤ (originalIdeleClassNorm K L).range :=
  originalIdeleClassPowerLocalUnitSubgroup_le_norm_enlarged K L S T hT

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Topology
open scoped NumberField ValuativeRel Classical WithZero
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [local instance] IsCyclic.commGroup
section

variable (K : Type) [Field K] [NumberField K]



variable (L : Type) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


variable (S T : Finset (HeightOneSpectrum (𝓞 K)))
  (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
    OriginalFiniteDecompositionGroup K L w = ⊥)



include hT in
attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient`. -/
theorem actual_original_power_quotient_originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_source
    [Finite (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
      (S ∪ originalNormRamificationSupport K L) T)] :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤
      Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
        (S ∪ originalNormRamificationSupport K L) T) :=
  originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient K L S T hT

end

section

variable (K : Type) [Field K] [NumberField K]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSupportedPowerClassMap_ker`. -/
theorem actual_original_power_quotient_originalSupportedPowerClassMap_ker_source (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (originalSupportedPowerClassMap K n S T).ker = originalSupportedPowerLocalUnitSubgroup K n S T :=
  originalSupportedPowerClassMap_ker K n S T

end

section

variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSupportedPowerLocalUnitQuotient_card`. -/
theorem actual_original_power_quotient_originalSupportedPowerLocalUnitQuotient_card_source :
    Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) =
      (∏ w : InfinitePlace K, Nat.card
        (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range)) *
      ∏ v : S, Nat.card ((v.val.adicCompletion K)ˣ ⧸
        (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range) :=
  originalSupportedPowerLocalUnitQuotient_card K n S T

end

section

variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSUnitPowerLocalQuotientMap_injective`. -/
theorem actual_original_power_quotient_originalSUnitPowerLocalQuotientMap_injective_source :
    Function.Injective (originalSUnitPowerLocalQuotientMap K n S T) :=
  originalSUnitPowerLocalQuotientMap_injective K n S T

end

section

variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSupportedClassPowerQuotientMap_surjective`. -/
theorem actual_original_power_quotient_originalSupportedClassPowerQuotientMap_surjective_source
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Function.Surjective (originalSupportedClassPowerQuotientMap K n S T) :=
  originalSupportedClassPowerQuotientMap_surjective K n S T hS

end

section

variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalSUnitPowerLocalQuotient_card_mul_class`. -/
theorem actual_original_power_quotient_originalSUnitPowerLocalQuotient_card_mul_class_source
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Nat.card (OriginalSUnitPowerLocalQuotient K n S T) *
        Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K n S T) =
      Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) :=
  originalSUnitPowerLocalQuotient_card_mul_class K n S T hS

end

section

variable (K : Type) [Field K] [NumberField K]



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalFinitePowerQuotient_finite`. -/
theorem actual_original_power_quotient_originalFinitePowerQuotient_finite_source (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    Finite ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) :=
  originalFinitePowerQuotient_finite K v n hn

end

section

variable (K : Type) [Field K] (w : InfinitePlace K)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalComplexCompletionUnit_power_surjective`. -/
theorem actual_original_power_quotient_originalComplexCompletionUnit_power_surjective_source (hw : w.IsComplex)
    (n : ℕ) (hn : 0 < n) : Function.Surjective (powMonoidHom n : w.Completionˣ →* w.Completionˣ) :=
  originalComplexCompletionUnit_power_surjective K w hw n hn

end

section

variable (K : Type) [Field K] (w : InfinitePlace K)



attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalInfinitePowerQuotient_card`. -/
theorem actual_original_power_quotient_originalInfinitePowerQuotient_card_source (n : ℕ) (hn : 0 < n) :
    Nat.card (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) =
      if w.IsReal ∧ Even n then 2 else 1 :=
  originalInfinitePowerQuotient_card K w n hn

end

section

variable (K : Type) [Field K] [NumberField K]



variable (L : Type) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]


attribute [-instance] UniformSpace.Completion.instSMul in
/-- Exact original-object consumer of `originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_of_support`. -/
theorem actual_original_power_quotient_originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_of_support_source
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑((S ∪ originalNormRamificationSupport K L) ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤
      Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
        (S ∪ originalNormRamificationSupport K L) T) :=
  originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_of_support K L S T hT hS

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Filter Topology Metric
open scoped NumberField ValuativeRel Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]





/-- Exact original-object consumer of `normedField_power_norm_sub_eventually`. -/
theorem actual_original_power_index_normedField_power_norm_sub_eventually_source (n : ℕ) (hn : (n : K) ≠ 0) :
    ∀ᶠ x : K in 𝓝 1, ‖x ^ n - 1‖ = ‖(n : K)‖ * ‖x - 1‖ :=
  normedField_power_norm_sub_eventually K n hn

end

section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]





/-- Exact original-object consumer of `normedField_power_small_closedBall`. -/
theorem actual_original_power_index_normedField_power_small_closedBall_source (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ s : ℝ, 0 < s → s ≤ r →
      Set.BijOn (fun x : K => x ^ n) (closedBall 1 s)
        (closedBall 1 (‖(n : K)‖ * s)) :=
  normedField_power_small_closedBall K n hn

end

section

variable {G : Type} [CommGroup G]





/-- Exact original-object consumer of `endomorphism_index_of_small_subgroup`. -/
theorem actual_original_power_index_endomorphism_index_of_small_subgroup_source (f : G →* G) (U : Subgroup G)
    [U.FiniteIndex] (hstable : U.map f ≤ U) (hker : U ⊓ f.ker = ⊥) :
    f.range.index = Nat.card f.ker * (U.map f).relIndex U :=
  endomorphism_index_of_small_subgroup f U hstable hker

end

section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]





/-- Exact original-object consumer of `normedFieldSmallUnitSubgroup_isOpen`. -/
theorem actual_original_power_index_normedFieldSmallUnitSubgroup_isOpen_source (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    IsOpen (normedFieldSmallUnitSubgroup K r hr0.le hr1 : Set Kˣ) :=
  normedFieldSmallUnitSubgroup_isOpen K r hr0 hr1

end

section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]





/-- Exact original-object consumer of `normedField_exists_small_unit_power_image`. -/
theorem actual_original_power_index_normedField_exists_small_unit_power_image_source (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ (r : ℝ) (_hr0 : 0 < r) (hr1 : r < 1), ∀ (s : ℝ) (hs0 : 0 < s) (hsr : s ≤ r),
      let hs1 : s < 1 := hsr.trans_lt hr1
      let ht1 : ‖(n : K)‖ * s < 1 :=
        (mul_le_of_le_one_left hs0.le (IsUltrametricDist.norm_natCast_le_one K n)).trans_lt hs1
      let U := normedFieldSmallUnitSubgroup K s hs0.le hs1
      let V := normedFieldSmallUnitSubgroup K (‖(n : K)‖ * s)
        (mul_nonneg (norm_nonneg _) hs0.le) ht1
      U.map (powMonoidHom n : Kˣ →* Kˣ) = V ∧
        U ⊓ (powMonoidHom n : Kˣ →* Kˣ).ker = ⊥ :=
  normedField_exists_small_unit_power_image K n hn

end

section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]



variable (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hs1 : s < 1)
  (hmul : s * s ≤ t)





include hmul in
/-- Exact original-object consumer of `normedFieldSmallUnit_relativeIndex`. -/
theorem actual_original_power_index_normedFieldSmallUnit_relativeIndex_source (ht1 : t < 1) :
    (normedFieldSmallUnitSubgroup K t ht.le ht1).relIndex
      (normedFieldSmallUnitSubgroup K s hs.le hs1) =
      Nat.card (normedFieldBallModule K s hs ⧸
        (normedFieldBallModule K t ht).comap (normedFieldBallModule K s hs).subtype) :=
  normedFieldSmallUnit_relativeIndex K s t hs ht hs1 hmul ht1

end

section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]



/-- Original local-field structure for this exact consumer. -/
local instance localFieldBallIntegerCoordinatesNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- Original local-field structure for this exact consumer. -/
local instance localFieldBallIntegerCoordinatesUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K

/-- Exact original-object consumer of `localFieldIntegerBallEquiv_apply`. -/
theorem actual_original_power_index_localFieldIntegerBallEquiv_apply_source (a : K) (ha : a ≠ 0) (x : 𝒪[K]) :
    (localFieldIntegerBallEquiv K a ha x : K) = a * (x : K) :=
  localFieldIntegerBallEquiv_apply K a ha x

end

section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]



/-- Original local-field structure for this exact consumer. -/
local instance localFieldBallScalarQuotientNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- Original local-field structure for this exact consumer. -/
local instance localFieldBallScalarQuotientUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K

/-- Exact original-object consumer of `localFieldBallScalarQuotient_card`. -/
theorem actual_original_power_index_localFieldBallScalarQuotient_card_source (a : K) (ha : a ≠ 0)
    (r : 𝒪[K]) (hr : r ≠ 0) :
    Nat.card (normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha) ⧸
      (normedFieldBallModule K ‖(r : K) * a‖
        (norm_pos_iff.mpr (mul_ne_zero (by exact_mod_cast hr) ha))).comap
          (normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha)).subtype) =
      Nat.card (𝒪[K] ⧸ (Ideal.span {r} : Ideal 𝒪[K])) :=
  localFieldBallScalarQuotient_card K a ha r hr

end

section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]



/-- Original local-field structure for this exact consumer. -/
local instance localFieldIntegerUnitPowerIndexNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- Original local-field structure for this exact consumer. -/
local instance localFieldIntegerUnitPowerIndexUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
/-- Original local-field structure for this exact consumer. -/
local instance localFieldIntegerUnitPowerIndexComplete : CompleteSpace K := localFieldOriginalNorm_complete K

/-- Exact original-object consumer of `localField_integerUnit_power_index`. -/
theorem actual_original_power_index_localField_integerUnit_power_index_source (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker *
        Nat.card (𝒪[K] ⧸ (Ideal.span {(n : 𝒪[K])} : Ideal 𝒪[K])) :=
  localField_integerUnit_power_index K n hn

end

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (q : 𝒪[K]) (hq : Irreducible q)





/-- Exact original-object consumer of `localField_unitPower_index_uniformizer_factor`. -/
theorem actual_original_power_index_localField_unitPower_index_uniformizer_factor_source (n : ℕ) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) :=
  localField_unitPower_index_uniformizer_factor K n

end

section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]





/-- Exact original-object consumer of `localField_unitPower_index_scalar_of_primitiveRoot`. -/
theorem actual_original_power_index_localField_unitPower_index_scalar_of_primitiveRoot_source
    (n : ℕ) (hn : (n : K) ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (n * Nat.card (𝒪[K] ⧸ (Ideal.span {(n : 𝒪[K])} : Ideal 𝒪[K]))) :=
  localField_unitPower_index_scalar_of_primitiveRoot K n hn ζ hζ

end

section

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))




/-- The actual ideal semiring, fixed for this exact consumer. -/
local instance originalScalarIdealSemiring : IdemCommSemiring (Ideal (v.adicCompletionIntegers K)) := Ideal.instIdemCommSemiring


/-- Exact original-object consumer of `originalAdic_natCast_span_eq_maximalIdeal_pow`. -/
theorem actual_original_power_index_originalAdic_natCast_span_eq_maximalIdeal_pow_source (n : ℕ) (hn : n ≠ 0) :
    (Ideal.span {(n : v.adicCompletionIntegers K)} : Ideal (v.adicCompletionIntegers K)) =
      @Monoid.npow (Ideal (v.adicCompletionIntegers K)) inferInstance
        (multiplicity v.asIdeal (Ideal.span {(n : 𝓞 K)}))
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
  originalAdic_natCast_span_eq_maximalIdeal_pow K v n hn

end

section

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))





/-- Exact original-object consumer of `originalAdic_natCast_quotient_card`. -/
theorem actual_original_power_index_originalAdic_natCast_quotient_card_source (n : ℕ) (hn : n ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      (Ideal.span {(n : v.adicCompletionIntegers K)} : Ideal (v.adicCompletionIntegers K))) =
      Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)})) :=
  originalAdic_natCast_quotient_card K v n hn

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalFinitePowerQuotient_card`. -/
theorem actual_original_power_index_originalFinitePowerQuotient_card_source (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) =
      n * (n * Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)}))) :=
  originalFinitePowerQuotient_card K v n hn ζ hζ

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalFinitePowerQuotient_product`. -/
theorem actual_original_power_index_originalFinitePowerQuotient_product_source (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v : S, Nat.card ((v.val.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range)) =
      n ^ (2 * S.card) * n ^ Module.finrank ℚ K :=
  originalFinitePowerQuotient_product K n hn ζ hζ S hS

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalInfinitePowerQuotient_product_mul_degree`. -/
theorem actual_original_power_index_originalInfinitePowerQuotient_product_mul_degree_source
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    (∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸
      (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range)) *
        n ^ Module.finrank ℚ K = n ^ (2 * Fintype.card (InfinitePlace K)) :=
  originalInfinitePowerQuotient_product_mul_degree K n hn ζ hζ

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalSupportedPowerLocalUnitQuotient_card_exact`. -/
theorem actual_original_power_index_originalSupportedPowerLocalUnitQuotient_card_exact_source
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) =
      n ^ (2 * (Fintype.card (InfinitePlace K) + S.card)) :=
  originalSupportedPowerLocalUnitQuotient_card_exact K n hn ζ hζ S T hS

end

section

variable (K : Type) [Field K] [NumberField K]





/-- Exact original-object consumer of `originalClassPowerQuotient_card_of_selected_kernel`. -/
theorem actual_original_power_index_originalClassPowerQuotient_card_of_selected_kernel_source
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hLarge : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))))
    (hDisjoint : Disjoint S T)
    (hCount : T.card + 1 = Fintype.card (InfinitePlace K) + S.card)
    (hKernel : originalSUnitPowerLocalSubgroup K n S T =
      (powMonoidHom n : ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
        ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K)).range) :
    Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K n S T) = n :=
  originalClassPowerQuotient_card_of_selected_kernel K n hn ζ hζ S T hS hLarge hDisjoint hCount hKernel

end


end
noncomputable section
open NumberField IsDedekindDomain CategoryTheory Filter Topology Metric
open scoped NumberField ValuativeRel Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
section

variable (K : Type) [Field K] {ι : Type} [Fintype ι]



/-- Exact original-object consumer of `finite_independent_absoluteValues_dense`. -/
theorem actual_original_prime_selection_finite_independent_absoluteValues_dense_source (abv : ι → AbsoluteValue K ℝ)
    (hNontrivial : ∀ i, (abv i).IsNontrivial)
    (hIndependent : Pairwise fun i j => ¬ (abv i).IsEquiv (abv j)) :
    DenseRange (algebraMap K (∀ i, WithAbs (abv i))) :=
  finite_independent_absoluteValues_dense K abv hNontrivial hIndependent

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_mixedCompletions_dense`. -/
theorem actual_original_prime_selection_original_mixedCompletions_dense_source (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun i : OriginalApproximationPlace K S =>
      algebraMap K (OriginalApproximationCompletion K S i) x) :=
  original_mixedCompletions_dense K S

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_principalUnit_open_approximation`. -/
theorem actual_original_prime_selection_original_principalUnit_open_approximation_source
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ i, (OriginalApproximationCompletion K S i)ˣ)
    (U : ∀ i, Subgroup (OriginalApproximationCompletion K S i)ˣ)
    (hU : ∀ i, IsOpen (U i : Set (OriginalApproximationCompletion K S i)ˣ)) :
    ∃ x : Kˣ, ∀ i,
      a i * (Units.map (algebraMap K (OriginalApproximationCompletion K S i)).toMonoidHom x)⁻¹ ∈ U i :=
  original_principalUnit_open_approximation K S a U hU

end

section

variable (K : Type) [Field K] [NumberField K]



/-- Exact original-object consumer of `original_principalUnit_power_approximation`. -/
theorem actual_original_prime_selection_original_principalUnit_power_approximation_source
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : 0 < n)
    (a : ∀ i, (OriginalApproximationCompletion K S i)ˣ) :
    ∃ x : Kˣ, ∀ i,
      a i * (Units.map (algebraMap K (OriginalApproximationCompletion K S i)).toMonoidHom x)⁻¹ ∈
        (powMonoidHom n : (OriginalApproximationCompletion K S i)ˣ →*
          (OriginalApproximationCompletion K S i)ˣ).range :=
  original_principalUnit_power_approximation K S n hn a

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalIdeleClassNorm_surjective_of_split_outside`. -/
theorem actual_original_prime_selection_originalIdeleClassNorm_surjective_of_split_outside_source
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSplit : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      OriginalFiniteDecompositionGroup K L w = ⊥) :
    Function.Surjective (originalIdeleClassNorm K L) :=
  originalIdeleClassNorm_surjective_of_split_outside K L S hSplit

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeDegree_fullDecomposition_infinite`. -/
theorem actual_original_prime_selection_original_primeDegree_fullDecomposition_infinite_source
    (hp : (Module.finrank K L).Prime) :
    Set.Infinite {v : HeightOneSpectrum (𝓞 K) | ∃ w : HeightOneSpectrum (𝓞 L),
      originalFinitePrimeBelow K L w = v ∧ OriginalFiniteDecompositionGroup K L w = ⊤} :=
  original_primeDegree_fullDecomposition_infinite K L hp

end

section

variable (G : Type) [CommGroup G] (p : ℕ) [Fact p.Prime]



/-- Exact original-object consumer of `primeExponent_exists_coordinates`. -/
theorem actual_original_prime_selection_primeExponent_exists_coordinates_source (r : ℕ)
    (hPower : ∀ g : G, g ^ p = 1) (hCard : Nat.card G = p ^ r) :
    Nonempty (G ≃* (Fin r → Multiplicative (ZMod p))) :=
  primeExponent_exists_coordinates G p r hPower hCard

end

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]



/-- Exact original-object consumer of `numberField_exists_prime_sUnit_kummer_coordinates`. -/
theorem actual_original_prime_selection_numberField_exists_prime_sUnit_kummer_coordinates_source
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K E = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (hE : E ≤ originalKummerRadicalField (Ω := Ω) p
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range)),
      S₀ ⊆ S ∧
      let N := originalKummerRadicalField (Ω := Ω) p
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range)
      letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
      letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
      let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
      Function.Surjective f ∧
        1 ≤ Fintype.card (NumberField.InfinitePlace K) + S.card ∧
        Nonempty (f.ker ≃* (Fin (Fintype.card (NumberField.InfinitePlace K) + S.card - 1) →
          Multiplicative (ZMod p))) :=
  numberField_exists_prime_sUnit_kummer_coordinates E p hDegree ζ hζ S₀

end

section

variable {G : Type} [Group G] {p r : ℕ}
  (e : G ≃* (Fin r → Multiplicative (ZMod p)))



/-- Exact original-object consumer of `primeCoordinateGenerator_iSup`. -/
theorem actual_original_prime_selection_primeCoordinateGenerator_iSup_source [NeZero p] :
    (⨆ i : Fin r, Subgroup.zpowers (primeCoordinateGenerator e i)) = ⊤ :=
  primeCoordinateGenerator_iSup e

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeOrder_fixedField_exists_fullDecomposition`. -/
theorem actual_original_prime_selection_original_primeOrder_fixedField_exists_fullDecomposition_source
    (p : ℕ) (hp : p.Prime) (g : Gal(L/K)) (hg : orderOf g = p)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∧
      OriginalFiniteDecompositionGroup (IntermediateField.fixedField (Subgroup.zpowers g)) L w = ⊤ :=
  original_primeOrder_fixedField_exists_fullDecomposition K L p hp g hg S

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeCoordinate_primes_distinct`. -/
theorem actual_original_prime_selection_original_primeCoordinate_primes_distinct_source
    (p : ℕ) (hp : p.Prime) (r : ℕ) (H : Subgroup Gal(L/K))
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : Fin r → HeightOneSpectrum (𝓞 L),
      Function.Injective (fun i => originalFinitePrimeBelow K L (w i)) ∧
      ∀ i, originalFinitePrimeBelow K L (w i) ∉ S ∧
        OriginalFiniteDecompositionGroup
          (IntermediateField.fixedField (Subgroup.zpowers (primeCoordinateGenerator e i).val)) L (w i) = ⊤ :=
  original_primeCoordinate_primes_distinct K L p hp r H e S

end


section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalFiniteDecomposition_isCyclic_of_unramified`. -/
theorem actual_original_prime_selection_originalFiniteDecomposition_isCyclic_of_unramified_source
    (w : HeightOneSpectrum (𝓞 L)) (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    IsCyclic (OriginalFiniteDecompositionGroup K L w) :=
  originalFiniteDecomposition_isCyclic_of_unramified K L w hw

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalFiniteDecomposition_eq_zpowers_of_relative_top`. -/
theorem actual_original_prime_selection_originalFiniteDecomposition_eq_zpowers_of_relative_top_source
    (p : ℕ) (hp : 0 < p) (hPower : ∀ σ : Gal(L/K), σ ^ p = 1)
    (g : Gal(L/K)) (hg : orderOf g = p) (w : HeightOneSpectrum (𝓞 L))
    (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (hFull : OriginalFiniteDecompositionGroup
      (IntermediateField.fixedField (Subgroup.zpowers g)) L w = ⊤) :
    OriginalFiniteDecompositionGroup K L w = Subgroup.zpowers g :=
  originalFiniteDecomposition_eq_zpowers_of_relative_top K L p hp hPower g hg w hw hFull

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]



omit [NumberField L] in
/-- Exact original-object consumer of `originalFiniteDecomposition_below_eq_bot_of_le_ker`. -/
theorem actual_original_prime_selection_originalFiniteDecomposition_below_eq_bot_of_le_ker_source
    (w : HeightOneSpectrum (𝓞 L))
    (hD : OriginalFiniteDecompositionGroup K L w ≤ (AlgEquiv.restrictNormalHom E).ker) :
    OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w) = ⊥ :=
  originalFiniteDecomposition_below_eq_bot_of_le_ker K L E w hD

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `original_primeCoordinate_split_primeSet`. -/
theorem actual_original_prime_selection_original_primeCoordinate_split_primeSet_source
    (E : IntermediateField K L) [IsGalois K E]
    (p : ℕ) (hp : p.Prime) (hPower : ∀ σ : Gal(L/K), σ ^ p = 1)
    (r : ℕ) (e : (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker ≃*
      (Fin r → Multiplicative (ZMod p)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (w : Fin r → HeightOneSpectrum (𝓞 L)),
      T = Finset.univ.image (fun i => originalFinitePrimeBelow K L (w i)) ∧
      T.card = r ∧ Disjoint S T ∧
      (∀ i, OriginalFiniteDecompositionGroup K L (w i) =
        Subgroup.zpowers (primeCoordinateGenerator e i).val) ∧
      ∀ v : HeightOneSpectrum (𝓞 E), originalFinitePrimeBelow K E v ∈ T →
        OriginalFiniteDecompositionGroup K E v = ⊥ :=
  original_primeCoordinate_split_primeSet K L E p hp hPower r e S

end


section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]



/-- Exact original-object consumer of `originalLocalKummer_power_iff_fixed`. -/
theorem actual_original_prime_selection_originalLocalKummer_power_iff_fixed_source
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (a : Kˣ) (β : Lˣ) (hβ : (β : L) ^ n = algebraMap K L (a : K)) :
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range ↔
    (β : L) ∈ IntermediateField.fixedField (OriginalFiniteDecompositionGroup K L w) :=
  originalLocalKummer_power_iff_fixed K L v w n hn ζ hζ a β hβ

end

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]



/-- Exact original-object consumer of `originalLocalKummer_coordinates_iff_mem_subextension`. -/
theorem actual_original_prime_selection_originalLocalKummer_coordinates_iff_mem_subextension_source
    (E : IntermediateField K L) [IsGalois K E]
    (p : ℕ) (hp : 0 < p) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (r : ℕ) (e : (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker ≃*
      (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 L))
    (hD : ∀ i, OriginalFiniteDecompositionGroup K L (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val)
    (a : Kˣ) (β : Lˣ) (hβ : (β : L) ^ p = algebraMap K L (a : K)) :
    (∀ i, Units.map (algebraMap K ((originalFinitePrimeBelow K L (w i)).adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom p : ((originalFinitePrimeBelow K L (w i)).adicCompletion K)ˣ →*
        ((originalFinitePrimeBelow K L (w i)).adicCompletion K)ˣ).range) ↔ (β : L) ∈ E :=
  originalLocalKummer_coordinates_iff_mem_subextension K L E p hp ζ hζ r e w hD a β hβ

end


end
end Dubon2026.SemanticRegression
