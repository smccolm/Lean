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

end Dubon2026.SemanticRegression
